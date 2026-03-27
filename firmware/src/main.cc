#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <bsp/board_api.h>
#include <tusb.h>

#ifdef ADC_ENABLED
#include <hardware/adc.h>
#endif
#include <hardware/flash.h>
#include <hardware/gpio.h>
#include <pico/bootrom.h>
#include <pico/mutex.h>
#include <pico/platform.h>
#include <pico/stdio.h>
#include <pico/unique_id.h>

#include "activity_led.h"
#include "config.h"
#include "crc.h"
#include "descriptor_parser.h"
#include "globals.h"
#include "i2c.h"
#include "mcp4651.h"
#include "our_descriptor.h"
#include "platform.h"
#include "remapper.h"
#include "tick.h"

// RP2350 UF2s wipe the last sector of flash every time
// because of RP2350-E10 errata mitigation. So we put
// the config one sector down.
#if PICO_RP2350
#define CONFIG_OFFSET_IN_FLASH (PICO_FLASH_SIZE_BYTES - PERSISTED_CONFIG_SIZE - 4096)
#else
#define CONFIG_OFFSET_IN_FLASH (PICO_FLASH_SIZE_BYTES - PERSISTED_CONFIG_SIZE)
#endif

#define FLASH_CONFIG_IN_MEMORY (((uint8_t*) XIP_BASE) + CONFIG_OFFSET_IN_FLASH)

#define ADC_USAGE_PAGE 0xFFF80000

uint64_t next_print = 0;

mutex_t mutexes[(uint8_t) MutexId::N];

uint32_t gpio_valid_pins_mask = 0;
uint32_t gpio_in_mask = 0;
uint32_t gpio_out_mask = 0;
uint32_t prev_gpio_state = 0;
uint64_t last_gpio_change[32] = { 0 };
bool set_gpio_dir_pending = false;

#ifdef ADC_ENABLED
uint16_t prev_adc_state[NADCS] = { 0 };
#endif

const uint32_t MOUSE_X_USAGE = 0x00010030;
const uint32_t MOUSE_Y_USAGE = 0x00010031;

extern tusb_desc_device_t desc_device;
extern char const* string_desc_arr[];

static char mirrored_product_name[32] = { 0 };

static bool find_relative_mouse_dev_addr(uint8_t* dev_addr_out) {
    bool found = false;

    my_mutex_enter(MutexId::THEIR_USAGES);
    for (auto const& [interface_id, report_map] : their_usages) {
        bool has_relative_x = false;
        bool has_relative_y = false;

        for (auto const& [report_id, usage_map] : report_map) {
            (void) report_id;

            auto x_it = usage_map.find(MOUSE_X_USAGE);
            if ((x_it != usage_map.end()) && x_it->second.is_relative) {
                has_relative_x = true;
            }

            auto y_it = usage_map.find(MOUSE_Y_USAGE);
            if ((y_it != usage_map.end()) && y_it->second.is_relative) {
                has_relative_y = true;
            }

            if (has_relative_x && has_relative_y) {
                *dev_addr_out = (uint8_t) (interface_id >> 8);
                found = true;
                break;
            }
        }

        if (found) {
            break;
        }
    }
    my_mutex_exit(MutexId::THEIR_USAGES);

    return found;
}
static bool mirror_mouse_identity(uint8_t dev_addr) {
    uint16_t vid = 0;
    uint16_t pid = 0;
    if (tuh_vid_pid_get(dev_addr, &vid, &pid)) {
        desc_device.idVendor = vid;
        desc_device.idProduct = pid;
    } else {
        return false;
    }

    // 先取设备支持的语言 ID，默认回退到 0x0409
    uint16_t lang_desc[16] = { 0 };
    uint16_t language_id = 0x0409;
    if (tuh_descriptor_get_string_sync(dev_addr, 0, 0, lang_desc, sizeof(lang_desc)) == XFER_RESULT_SUCCESS) {
        uint8_t lang_len = ((uint8_t*) lang_desc)[0];
        if (lang_len >= 4) {
            language_id = lang_desc[1];
        }
    }

    uint16_t product_desc_utf16[32] = { 0 };
    uint8_t res = tuh_descriptor_get_product_string_sync(dev_addr, language_id, product_desc_utf16, sizeof(product_desc_utf16));
    if ((res != XFER_RESULT_SUCCESS) && (language_id != 0x0409)) {
        res = tuh_descriptor_get_product_string_sync(dev_addr, 0x0409, product_desc_utf16, sizeof(product_desc_utf16));
    }
    if (res != XFER_RESULT_SUCCESS) {
        return false;
    }

    uint8_t total_len = ((uint8_t*) product_desc_utf16)[0];
    if (total_len < 4) {
        return false;
    }

    uint8_t chars = (uint8_t) ((total_len - 2) / 2);
    if (chars > 31) {
        chars = 31;
    }

    for (uint8_t i = 0; i < chars; i++) {
        uint16_t ch = product_desc_utf16[1 + i];
        mirrored_product_name[i] = (ch >= 0x20 && ch <= 0x7E) ? (char) ch : '_';
    }
    mirrored_product_name[chars] = 0;

    string_desc_arr[2] = mirrored_product_name;
    return true;
}
void print_stats_maybe() {
    uint64_t now = time_us_64();
    if (now > next_print) {
        print_stats();
        while (next_print < now) {
            next_print += 1000000;
        }
    }
}

void __no_inline_not_in_flash_func(sof_handler)(uint32_t frame_count) {
    sof_callback();
}

bool do_send_report(uint8_t interface, const uint8_t* report_with_id, uint8_t len) {
    if (tud_suspended() &&
        (our_descriptor->should_cause_wakeup != nullptr) &&
        our_descriptor->should_cause_wakeup(report_with_id[0], report_with_id + 1, len - 1)) {
        tud_remote_wakeup();
    } else {
        tud_hid_n_report(interface, report_with_id[0], report_with_id + 1, len - 1);
    }
    return true;  // XXX?
}

void gpio_pins_init() {
    gpio_valid_pins_mask = get_gpio_valid_pins_mask();
    gpio_init_mask(gpio_valid_pins_mask);
}

void set_gpio_inout_masks(uint32_t in_mask, uint32_t out_mask) {
    // if some pin appears as both input and output, input wins
    gpio_out_mask = (out_mask & ~in_mask) & gpio_valid_pins_mask;
    // we treat all pins except the output ones as input so that the monitor works
    gpio_in_mask = gpio_valid_pins_mask & ~gpio_out_mask;
    set_gpio_dir_pending = true;
}

void set_gpio_dir() {
    gpio_set_dir_masked(gpio_in_mask, 0);
    // output pin direction will be set in write_gpio()
    for (uint8_t i = 0; i <= 29; i++) {
        uint32_t bit = 1 << i;
        if (gpio_valid_pins_mask & bit) {
            gpio_set_pulls(i, gpio_in_mask & bit, false);
        }
    }
}

#ifdef ADC_ENABLED
void adc_pins_init() {
    adc_init();
    for (int n = 26; n < 26 + NADCS; n++) {
        adc_gpio_init(n);
    }

#ifdef PICO_SMPS_MODE_PIN
    // (This only does anything on a Pico, but won't hurt on custom board v8.)
    gpio_init(PICO_SMPS_MODE_PIN);
    gpio_set_dir(PICO_SMPS_MODE_PIN, GPIO_OUT);
    gpio_put(PICO_SMPS_MODE_PIN, true);
#endif
}
#endif

bool read_gpio(uint64_t now) {
    uint32_t gpio_state = gpio_get_all() & gpio_in_mask;
    uint32_t changed = prev_gpio_state ^ gpio_state;
    if (changed != 0) {
        for (uint8_t i = 0; i <= 29; i++) {
            uint32_t bit = 1 << i;
            if (changed & bit) {
                if (last_gpio_change[i] + gpio_debounce_time <= now) {
                    uint32_t usage = GPIO_USAGE_PAGE | i;
                    int32_t state = !(gpio_state & bit);  // active low
                    set_input_state(usage, state, state);
                    if (monitor_enabled) {
                        monitor_usage(usage, state, 0);
                    }
                    last_gpio_change[i] = now;
                } else {
                    // ignore this change
                    gpio_state ^= bit;
                    changed ^= bit;
                }
            }
        }
        prev_gpio_state = gpio_state;
    }
    return changed != 0;
}

void write_gpio() {
    if (suspended) {
        return;
    }

    uint32_t value = gpio_out_state[0] | (gpio_out_state[1] << 8) | (gpio_out_state[2] << 16) | (gpio_out_state[3] << 24);
    switch (gpio_output_mode) {
        case 0:
            gpio_put_masked(gpio_out_mask, value);
            gpio_set_dir_masked(gpio_out_mask, gpio_out_mask);
            break;
        case 1:
            gpio_put_masked(gpio_out_mask, 0);
            gpio_set_dir_masked(gpio_out_mask, value);
            break;
    }
    memset(gpio_out_state, 0, sizeof(gpio_out_state));
}

#ifdef ADC_ENABLED
bool read_adc() {
    bool changed = false;
    for (int i = 0; i < NADCS; i++) {
        adc_select_input(i);
        uint16_t state = adc_read();
        if (state != prev_adc_state[i]) {
            changed = true;
            prev_adc_state[i] = state;
        }
        uint32_t usage = ADC_USAGE_PAGE | i;
        set_input_state(usage, state, state >> 4);
        if (monitor_enabled) {
            monitor_usage(usage, state, 0);
        }
    }
    return changed;
}
#endif

void do_persist_config(uint8_t* buffer) {
#if !PICO_COPY_TO_RAM
    uint32_t ints = save_and_disable_interrupts();
#endif
    flash_range_erase(CONFIG_OFFSET_IN_FLASH, PERSISTED_CONFIG_SIZE);
    flash_range_program(CONFIG_OFFSET_IN_FLASH, buffer, PERSISTED_CONFIG_SIZE);
#if !PICO_COPY_TO_RAM
    restore_interrupts(ints);
#endif
}

void reset_to_bootloader() {
    reset_usb_boot(0, 0);
}

void pair_new_device() {
}

void clear_bonds() {
}

void my_mutexes_init() {
    for (int i = 0; i < (int8_t) MutexId::N; i++) {
        mutex_init(&mutexes[i]);
    }
}

void my_mutex_enter(MutexId id) {
    mutex_enter_blocking(&mutexes[(uint8_t) id]);
}

void my_mutex_exit(MutexId id) {
    mutex_exit(&mutexes[(uint8_t) id]);
}

uint64_t get_time() {
    return time_us_64();
}

uint64_t get_unique_id() {
    pico_unique_board_id_t unique_id;
    pico_get_unique_board_id(&unique_id);
    uint64_t ret = 0;
    for (int i = 0; i < 8; i++) {
        ret |= (uint64_t) unique_id.id[7 - i] << (8 * i);
    }
    return ret;
}

int main() {
    my_mutexes_init();
    gpio_pins_init();
#ifdef I2C_ENABLED
    our_i2c_init();
#endif
#ifdef ADC_ENABLED
    adc_pins_init();
#endif
    tick_init();
    bool device_side_connected = false;
    tud_disconnect();
    load_config(FLASH_CONFIG_IN_MEMORY);
    our_descriptor = &our_descriptors[our_descriptor_number];
    parse_our_descriptor();
    set_mapping_from_config();
    board_init();
    extra_init();
    tusb_init();
    stdio_init_all();

    tud_sof_isr_set(sof_handler);

    next_print = time_us_64() + 1000000;

    while (true) {
        bool tick;
        bool new_report;
        read_report(&new_report, &tick);
        if (new_report) {
            activity_led_on();
        }
        if (their_descriptor_updated) {
            update_their_descriptor_derivates();
            their_descriptor_updated = false;
        }
        if (tick) {
            bool gpio_state_changed = read_gpio(time_us_64());
            if (gpio_state_changed) {
                activity_led_on();
            }
#ifdef ADC_ENABLED
            read_adc();
#endif
            process_mapping(true);
            write_gpio();
#ifdef MCP4651_ENABLED
            mcp4651_write();
#endif
        }
        tud_task();
        if (!device_side_connected) {
            uint8_t mouse_dev_addr = 0;
            if (find_relative_mouse_dev_addr(&mouse_dev_addr)) {
                if (mirror_mouse_identity(mouse_dev_addr)) {
                    tud_connect();
                    device_side_connected = true;
                }
            }
        }
        if (boot_protocol_updated) {
            parse_our_descriptor();
            boot_protocol_updated = false;
            config_updated = true;
        }
        if (resume_pending) {
            resume_pending = false;
            suspended = false;
        }
        if (config_updated) {
            set_mapping_from_config();
            config_updated = false;
        }
        if (set_gpio_dir_pending && !suspended) {
            set_gpio_dir();
            set_gpio_dir_pending = false;
        }
        if (tud_hid_n_ready(0) || tud_suspended()) {
            send_report(do_send_report);
        }
        if (monitor_enabled && tud_hid_n_ready(1)) {
            send_monitor_report(do_send_report);
        }
        if (our_descriptor->main_loop_task != nullptr) {
            our_descriptor->main_loop_task();
        }
        send_out_report();
        if (need_to_persist_config) {
            persist_config_return_code = persist_config();
            need_to_persist_config = false;
        }

        print_stats_maybe();

        activity_led_off_maybe();
    }

    return 0;
}
