// Simple GPIO pin driver with typestate pattern
// Demonstrates runtime state detection when taking over hardware

use std::{
    mem::replace,
    sync::atomic::{AtomicBool, Ordering},
};

use flux_rs::{
    alias, bitvec::BV32, constant, defs, invariant, opaque, refined_by, reflect, spec, specs,
    trusted,
};

// Unsafe HW Stuff / Singleton ------------------------------------------------------
struct Peripherals {
    gpio_a: Gpio,
    gpio_b: Gpio,
    gpio_c: Gpio,
}

// Real hardware example addresses (STM32-like):
// GPIOA: 0x4800_0000
// GPIOB: 0x4800_0400
// GPIOC: 0x4800_0800
// Each GPIO port has the same register layout but different base address

// Safe singleton access to peripherals
#[trusted]
fn take_peripherals() -> Option<Peripherals> {
    static TAKEN: AtomicBool = AtomicBool::new(false);
    if TAKEN
        .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
        .is_ok()
    {
        Some(Peripherals {
            gpio_a: Gpio(0x4800_0000 as *mut GpioRegisters),
            gpio_b: Gpio(0x4800_0400 as *mut GpioRegisters),
            gpio_c: Gpio(0x4800_0800 as *mut GpioRegisters),
        })
    } else {
        None
    }
}

#[trusted]
impl Gpio {
    #[spec(fn(&Gpio[@modes]) -> &GpioRegisters[modes])]
    pub fn get_registers(&self) -> &GpioRegisters {
        unsafe { &*self.0 }
    }

    // sets the modes bitvec
    #[spec(fn(self: &mut Gpio, modes: BV32) ensures self: Gpio[modes])]
    pub fn set_modes(&mut self, modes: BV32) {
        unsafe {
            let regs = &mut *self.0;
            regs.modes = modes;
        }
    }

    // does not change modes
    #[spec(fn(self: &mut Gpio[@modes], output: u32) ensures self: Gpio[modes])]
    pub fn set_output(&mut self, output: u32) {
        unsafe {
            let regs = &mut *self.0;
            regs.output = output;
        }
    }
}

// Gpio API --------------------------------------------------------------------------
// Hardware register interface (simplified)
// In real hardware (e.g., STM32), these registers control multiple pins at once
// Each bit in the register corresponds to one pin
// Example: GPIOA controls pins PA0-PA15
#[refined_by(modes: bitvec<32>)]
#[repr(C)]
struct GpioRegisters {
    #[field(BV32[modes])]
    modes: BV32, // Bit 0 = pin 0 mode, bit 1 = pin 1 mode, etc.
    output: u32, // Bit 0 = pin 0 output, bit 1 = pin 1 output, etc.
    input: u32,  // Bit 0 = pin 0 input, bit 1 = pin 1 input, etc.
}

#[reflect]
enum Mode {
    Input,
    Output,
}

#[opaque]
#[refined_by(modes: bitvec<32>)]
struct Gpio(*mut GpioRegisters);

#[alias(type Pin[n: int] = {u8[n] | 0 <= n && n < 32})]
type Pin = u8;

defs! {
    fn get_mode(bv: bitvec<32>, index: int) -> Mode {
        let val = (bv >> bv_int_to_bv32(index)) & 1;
        if val == 0 {
            Mode::Input
        } else {
            Mode::Output
        }
    }

    fn set_mode(bv: bitvec<32>, index: int, mode: Mode) -> bitvec<32> {
        let index_bits = bv_int_to_bv32(index);
        if mode == Mode::Input {
            bv & bv_not(1 << index_bits)
        } else { // Mode::Output
            bv | (1 << index_bits)
        }
    }
}

#[constant(bv_int_to_bv32(0))]
const ZERO: BV32 = BV32::new(0);

#[constant(bv_int_to_bv32(1))]
const ONE: BV32 = BV32::new(1);

impl Gpio {
    #[spec(fn(&Gpio[@modes], pin: Pin) -> Mode[get_mode(modes, pin)])]
    fn get_mode(&self, pin: Pin) -> Mode {
        let regs = self.get_registers();
        let b0 = 0;
        if ((regs.modes >> pin) & 1) == b0 {
            Mode::Input
        } else {
            Mode::Output
        }
    }

    #[spec(fn(self: &mut Gpio[@modes], pin: Pin, mode: Mode)
           ensures self: Gpio[set_mode(modes, pin, mode)])]
    fn set_mode(&mut self, pin: Pin, mode: Mode) {
        let regs = self.get_registers();
        match mode {
            Mode::Input => {
                self.set_modes(regs.modes & !(ONE << pin));
            }
            Mode::Output => {
                self.set_modes(regs.modes | (ONE << pin));
            }
        }
    }

    // requires pin in Input mode
    #[spec(fn(&Gpio[@modes], pin: Pin) -> bool
           requires get_mode(modes, pin) == Mode::Input)]
    fn read(&self, pin: Pin) -> bool {
        let regs = self.get_registers();
        ((regs.input >> pin) & 1) == 1
    }

    // requires pin in Output mode
    #[spec(fn(self: &mut Gpio[@modes], pin: Pin, value: bool)
           requires get_mode(modes, pin) == Mode::Output)]
    fn write(&mut self, pin: Pin, value: bool) {
        let regs = self.get_registers();
        if value {
            self.set_output(regs.output | (1 << pin));
        } else {
            self.set_output(regs.output & !(1 << pin));
        }
    }
}

// CLIENT CODE EXAMPLES --------------------------------------------------

// Example showing multiple pins from the same port in DIFFERENT states
pub fn example_same_port() {
    // Get mutable access to GPIOA
    let mut peripherals = take_peripherals().expect("Peripherals already taken");
    let gpio_a = &mut peripherals.gpio_a;

    // Multiple pins share the same registers (same port) but can be in different states!
    // Configure the pins as input or output
    gpio_a.set_mode(0, Mode::Output); // PA0 = Output
    gpio_a.set_mode(1, Mode::Output); // PA1 = Output
    gpio_a.set_mode(5, Mode::Input); // PA5 = Input

    // Each pin's state is tracked by the type system through refinements
    // The hardware mode register might look like: 0b00...00100011
    // Bit 0 = 1 (output), Bit 1 = 1 (output), Bit 5 = 0 (input)

    // They all manipulate the same hardware registers using different bit positions
    gpio_a.write(0, true); // Sets bit 0 in GPIOA output register (high)
    gpio_a.write(1, true); // Sets bit 1 in GPIOA output register (high)
    let button_state = gpio_a.read(5); // Reads bit 5 from GPIOA input register

    // Type system prevents mistakes through refinements:
    // gpio_a.write(5, true);  // ERROR! Can't write to a pin in Input mode
    // gpio_a.read(0);         // ERROR! Can't read from a pin in Output mode

    // After the above code, the GPIOA registers would look like:
    // mode register:   0b00...00100011 (bit 5=0 input, bits 0,1=1 output)
    // output register: 0b00...00000011 (bits 0,1 high, bit 5 not used)
}

// Example showing pins from different ports
pub fn example_different_ports() {
    // Get mutable references to different GPIO ports
    let mut peripherals = take_peripherals().expect("Peripherals already taken");
    let gpio_a = &mut peripherals.gpio_a;
    let gpio_b = &mut peripherals.gpio_b;
    let mut gpio_c = &mut peripherals.gpio_c;

    // Same pin number, different ports = different physical pins
    // Configure pins as outputs
    gpio_a.set_mode(5, Mode::Output); // PA5
    gpio_b.set_mode(5, Mode::Output); // PB5 (completely different pin!)
    gpio_c.set_mode(13, Mode::Output); // PC13 (often the onboard LED)

    // Control the pins from different ports
    gpio_a.write(5, true); // PA5 set high
    gpio_b.write(5, false); // PB5 set low
    gpio_c.write(13, true); // PC13 set high
}

// Example 1: Taking over hardware in unknown state
#[spec(fn(gpio: &mut Gpio) ensures gpio: Gpio)] // boo strong reference!
fn example_with_runtime_detection(gpio: &mut Gpio) {
    // Get pin number we want to check
    let pin: Pin = 5;

    // Runtime check to see what the hardware is actually configured as
    let current_mode = gpio.get_mode(pin);

    match current_mode {
        Mode::Input => {
            // Hardware was in input mode
            let value = gpio.read(pin);
            println!("Pin was input, read: {}", value);

            // Can convert to output if needed
            gpio.set_mode(pin, Mode::Output);
            gpio.write(pin, true); // Set high
        }
        Mode::Output => {
            // Hardware was in output mode
            println!("Pin was output, setting high");
            gpio.write(pin, true); // Set high
        }
    }
}

// Example 2: Configuring from scratch (don't care about current state)

#[spec(fn(gpio: &mut Gpio) ensures gpio: Gpio)] // boo strong reference!
fn example_forced_configuration(gpio: &mut Gpio) {
    // Take pin in unknown state and force it to output
    let led_pin: Pin = 3;
    gpio.set_mode(led_pin, Mode::Output);

    // Now we can safely use it as output
    gpio.write(led_pin, true); // Set high
    gpio.write(led_pin, false); // Set low

    // This won't compile - can't read from an output pin:
    // let value = gpio.read(led_pin); // ERROR! Prevented by refinement types
}

// Example 3: Safe state transitions
#[spec(fn(gpio: &mut Gpio) ensures gpio: Gpio)] // boo strong reference!
fn example_state_transition(gpio: &mut Gpio) {
    // Define pin number
    let pin: Pin = 7;

    // Start as input
    gpio.set_mode(pin, Mode::Input);
    let button_pressed = gpio.read(pin);

    // Convert to output
    gpio.set_mode(pin, Mode::Output);

    // Can't read anymore - this won't compile:
    // let value = gpio.read(pin); // ERROR! Prevented by refinement types

    // But we can write
    gpio.write(pin, true); // Set high

    // Convert back to input
    gpio.set_mode(pin, Mode::Input);
    let new_value = gpio.read(pin);
}

// Example 4: Real-world bootloader scenario
#[spec(fn(gpio: &mut Gpio) ensures gpio: Gpio)] // boo strong reference!
fn bootloader_handoff(gpio: &mut Gpio) {
    // Define the status LED pin
    let status_led: Pin = 13;

    // Check what bootloader left it as
    let current_mode = gpio.get_mode(status_led);

    match current_mode {
        Mode::Output => {
            // Already output, good to go
            println!("Status LED was already configured as output");
        }
        Mode::Input => {
            // Was input, need to reconfigure
            println!("Status LED was configured as input, changing to output");
            gpio.set_mode(status_led, Mode::Output);
        }
    }

    // Now guaranteed to be output (either it was already, or we just set it)
    gpio.write(status_led, true); // Set high
}
