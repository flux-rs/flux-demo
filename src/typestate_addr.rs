// Simple GPIO pin driver with typestate pattern
// Demonstrates runtime state detection when taking over hardware

use std::{
    mem::replace,
    sync::atomic::{AtomicBool, Ordering}, vec,
};

use flux_rs::{
    alias, bitvec::BV32, constant, defs, detached_spec, extern_spec, invariant, opaque, refined_by, reflect, spec, specs, trusted
};


fn test_shl_or() {
    let b1 = BV32::new(1);  // 0b0001
    let b5 = BV32::new(5);  // 0b0101
    let res = b5 << b1;     // 0b1010
    let res = res | b1;     // 0b1011
    flux_rs::assert(res == BV32::new(11));
}

#[spec(fn () -> u32[11])]
fn test_shl_orr() -> u32 {
  let b1 = BV32::new(1);  // 0b0001
  let b5 = BV32::new(5);  // 0b0101
  let res = b5 << b1;     // 0b1010
  let res = res | b1;     // 0b1011
  res.into() // assert(res == BV32::new(11));
}

// --------------------------------------------------------------------------------

#[alias(type Pin = u8{n: 0 <= n && n < 32})]
type Pin = u8;

defs! {
    fn get_pin(bv: bitvec<32>, pin: int) -> bool{
        let val = (bv >> bv_int_to_bv32(pin)) & 1;
        val == 1
    }

    fn set_pin(bv: bitvec<32>, pin: int, val: bool) -> bitvec<32> {
        let index_bits = bv_int_to_bv32(pin);
        if val {
            bv | (1 << index_bits)
        } else {
            bv & bv_not(1 << index_bits)
        }
    }
}

#[spec(fn(gpio: &mut Gpio[@modes]) ensures gpio: Gpio[modes])]
fn test_get_set_typ(gpio: &mut Gpio) {
    let orig = gpio.get_mode(3);            // save original mode
    gpio.set_mode(3, Mode::Output);         // set to output
    flux_rs::assert(gpio.get_mode(3) == Mode::Output);
    gpio.set_mode(3, orig);           // restore original mode
}

// returns `1`` if the bit at `index` is set, else `0`
fn get_pin(bv: BV32, pin: Pin) -> bool {
    ((bv >> pin) & 1) == 1
}

// sets the bit at `index` to `1` if `val` is `true` and to `0` otherwise
// #[spec(fn (bv: BV32, pin: Pin, val: bool) -> BV32[set_pin(bv, pin, val)])]
fn set_pin(bv: BV32, pin: Pin, val: bool) -> BV32 {
    if val {
        bv | (BV32::new(1) << pin)
    } else {
        bv & !(BV32::new(1) << pin)
    }
}

detached_spec! {
  fn get_pin(bv: BV32, pin: Pin) -> bool[get_pin(bv, pin)];
  fn set_pin(bv: BV32, pin: Pin, val: bool) -> BV32[set_pin(bv, pin, val)];
}


fn test_get_set_pin() {
  let b5 = BV32::new(5);                      // 0b0101
  flux_rs::assert(get_pin(b5, 2));    // bit 2 is set
  let b5 = set_pin(b5, 2, false);  // 0b0000
  flux_rs::assert(!get_pin(b5, 2));     // bit 2 is cleared
}

/*

== 1. Bitvectors (see flux tests!)
   fn set(bv32, i:u8, b:bool) -> bv
   fn get(bv32, i:u8) -> bool
   fn mask(bv32, hi, lo) -> bv
   fn test_mask(bv) -> { mask(bv, 3, 0) < 16 }

== 2. Registers & Gpio & Peripherals
   Plain rust

== 3. Tracking `modes`
    - index
    - track in private methods to access gpio-registers

== 4. Using `modes`
    - get_mode
    - set_mode
    - read_pin
    - write_pin
    in public methods to read/write gpio-registers)

== 5. Clients

== 6. Summary

*/

// === GPIO Device

// #[opaque]
// #[refined_by(modes: bitvec<32>)]
struct Gpio(*mut Registers);


// === Hardware register interface --------------------------------------------------

// Each GPIO port has multiple registers controlling pin modes, input, and output
// In real hardware (e.g., STM32), these registers control multiple pins at once
// Each bit in the register corresponds to one pin
// Example: GPIOA controls pins PA0-PA15
// #[refined_by(modes: bitvec<32>)]
#[repr(C)]
struct Registers {
    // #[field(BV32[modes])]
    modes: BV32, // Bit 0 = pin 0 mode, bit 1 = pin 1 mode, etc.
    output: u32, // Bit 0 = pin 0 output, bit 1 = pin 1 output, etc.
    input: u32,  // Bit 0 = pin 0 input, bit 1 = pin 1 input, etc.
}

// Refined Gpio ----------------------------------------------------------------
detached_spec! {
    #[opaque]
    #[refined_by(modes: bitvec<32>)]
    struct Gpio;
}

// Refined Registers -----------------------------------------------------------
detached_spec! {
    #[refined_by(modes: bitvec<32>)]
    struct Registers {
        modes: BV32[modes],
        output: u32,
        input: u32,
    }
}

// Private internal/unsafe pointer methods methods ------------------------------
#[trusted]
impl Gpio {
    #[spec(fn(&Gpio[@modes]) -> &Registers[modes])]
    fn get_registers(&self) -> &Registers {
        unsafe { &*self.0 }
    }

    // UPDATES the `modes`
    #[spec(fn(self: &mut Gpio, modes: BV32) ensures self: Gpio[modes])]
    fn set_modes(&mut self, modes: BV32) {
        unsafe { (&mut *self.0).modes = modes }
    }

    // PRESERVES the `modes`
    #[spec(fn(self: &mut Gpio[@modes], output: u32) ensures self: Gpio[modes])]
    fn set_output(&mut self, output: u32) {
        unsafe {
            let regs = &mut *self.0;
            regs.output = output;
        }
    }
}

// ----------------------------------------------------------------------------------
// MODES
// ----------------------------------------------------------------------------------

#[reflect]
#[derive(PartialEq, Eq)]
enum Mode {
    Input,
    Output
}
flux_core::eq!(Mode);

defs! {
  fn bool_to_mode(b:bool) -> Mode {
    if b { Mode::Output } else { Mode::Input }
  }
  fn mode_to_bool(mode: Mode) -> bool {
    mode == Mode::Output
  }
}


impl From<bool> for Mode {
  #[spec(fn (b: bool) -> Mode[bool_to_mode(b)])]
  fn from(b: bool) -> Self {
    if b { Mode::Output } else { Mode::Input }
  }
}

impl Into<bool> for Mode {
    #[spec(fn (mode: Mode) -> bool[mode_to_bool(mode)])]
    fn into(self) -> bool {
        match self {
            Mode::Input => false,
            Mode::Output => true,
        }
    }
}

// ------------------------------------------------------------------------------------------
// PUBLIC `Gpio` access methods and API -----------------------------------------------------
// ------------------------------------------------------------------------------------------


defs! {
  fn get_mode(bv: bitvec<32>, index: int) -> Mode {
    bool_to_mode(get_pin(bv, index))
  }

  fn set_mode(bv: bitvec<32>, index: int, mode: Mode) -> bitvec<32> {
    set_pin(bv, index, mode_to_bool(mode))
  }
}


// Public API implementation that uses the internal methods
impl Gpio {
    #[spec(fn(&Gpio[@modes], pin: Pin) -> Mode[get_mode(modes, pin)])]
    pub fn get_mode(&self, pin: Pin) -> Mode {
        let regs = self.get_registers();
        Mode::from(get_pin(regs.modes, pin))
    }

    #[spec(fn(self: &mut Gpio[@modes], pin: Pin, mode: Mode)
           ensures self: Gpio[set_mode(modes, pin, mode)])]
    pub fn set_mode(&mut self, pin: Pin, mode: Mode) {
        let one = BV32::new(1);
        let regs = self.get_registers();
        self.set_modes(set_pin(regs.modes, pin, mode.into()))
    }
}

#[alias(type Pin(modes: bitvec<32>) = Pin{n: get_mode(modes, n) == Mode::Input})]
type InPin = Pin;

#[alias(type Pin(modes: bitvec<32>) = Pin{n: get_mode(modes, n) == Mode::Output})]
type OutPin = Pin;


impl Gpio {
    // requires pin in Input mode
    #[spec(fn(&Gpio[@modes], pin: InPin(modes)) -> bool)]
    pub fn read(&self, pin: InPin) -> bool {
        let regs = self.get_registers();
        get_pin(regs.input.into(), pin)
    }

    // requires pin in Output mode
    #[spec(fn(self: &mut Gpio[@modes], pin: OutPin(modes), value: bool))]
    pub fn write(&mut self, pin: OutPin, value: bool) {
        let output = self.get_registers().output.into();
        let new_output = set_pin(output, pin, value).into();;
        self.set_output(new_output);
    }
}

// Peripherals ----------------------------------------------------------------------
// Unsafe HW Stuff / Singleton ------------------------------------------------------
// ----------------------------------------------------------------------------------
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
            gpio_a: Gpio(0x4800_0000 as *mut Registers),
            gpio_b: Gpio(0x4800_0400 as *mut Registers),
            gpio_c: Gpio(0x4800_0800 as *mut Registers),
        })
    } else {
        None
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



#[spec(fn(gpio: &mut Gpio[@modes]) ensures gpio: Gpio[set_mode(modes, 8, Mode::Output)])]
fn ex_pin_write(gpio: &mut Gpio) {
    gpio.set_mode(8, Mode::Output);
    gpio.write(8, true);
    gpio.write(8, false);
}


#[spec(fn(gpio: &mut Gpio[@modes], pin:Pin) -> Option<bool>
       ensures gpio: Gpio[set_mode(modes, pin, Mode::Output)] )]
fn detect_and_set(gpio: &mut Gpio, pin: Pin) -> Option<bool> {
    // gpio.read(pin); // ERROR can't read, don't know state!
    if let Mode::Input = gpio.get_mode(pin) {
        let val = gpio.read(pin);
        gpio.set_mode(pin, Mode::Output);
        return Some(val);
    }
    None
}

// Example 1: Taking over hardware in unknown state
#[spec(fn(gpio: &mut Gpio) ensures gpio: Gpio)] // boo strong reference!
fn example_with_runtime_detection(gpio: &mut Gpio) {
    // Get pin number we want to check
    let pin: Pin = 5;

    // gpio.write(pin, true); // ERROR can't write, don't know state!

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


// Example 2: Safe state transitions (SKIP)
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




// Example 3: Configuring from scratch (don't care about current state)
// EXERCISE 0 remove the set_mode call inside, ask to fix code.
#[spec(fn(gpio: &mut Gpio) ensures gpio: Gpio)] // boo strong reference!
fn example_forced_configuration(gpio: &mut Gpio) {
    // Take pin in unknown state and force it to output
    let led_pin: Pin = 13;
    // EXERCISE: remove the set_mode below.
    gpio.set_mode(led_pin, Mode::Output);

    // Now we can safely use it as output
    gpio.write(led_pin, true); // Set high
    gpio.write(led_pin, false); // Set low

    // This won't compile - can't read from an output pin:
    // let value = gpio.read(led_pin); // ERROR! Prevented by refinement types
}



// EXERCISE 1
#[spec(fn(gpio: &mut Gpio[@modes]) requires get_mode(modes, 13) == Mode::Output)]
fn blink_status_led(gpio: &mut Gpio) {
    // Toggle PC13 (which bootloader_handoff guaranteed is in Output mode)
    static mut LED_STATE: bool = true;
    let value = unsafe {
        LED_STATE = !LED_STATE;
        LED_STATE
    };
    gpio.write(13, value);  // We can safely write because bootloader_handoff ensured it's an output
}

// EXERCISE 2
#[spec(fn(gpio: &Gpio[@modes], pins: &[InPin(modes)]) -> Vec<bool>)]
fn ex_read_pins_range(gpio: &Gpio, pins: &[InPin]) -> Vec<bool> {
    let mut res = vec![];
    for i in 0..pins.len() {
        res.push(gpio.read(pins[i]));
    }
    res
}

#[spec(fn(gpio: &Gpio[@modes], pins: &[InPin(modes)]) -> Vec<bool>)]
fn ex_read_pins_for(gpio: &Gpio, pins: &[InPin]) -> Vec<bool> {
    let mut res = vec![];
    for pin in pins {
        res.push(gpio.read(*pin));
    }
    res
}

// EXERCISE 3
#[spec(fn(gpio: &mut Gpio[@modes], pins: &[OutPin(modes)][@n]))]
fn ex_reset_pins(gpio: &mut Gpio, pins: &[OutPin]) {
    for pin in pins {
        gpio.write(*pin, false);
    }
}

#[spec(fn(gpio: &mut Gpio[@modes], pins: &[OutPin(modes)][@n], vals: &[bool][n]))]
fn ex_write_pins(gpio: &mut Gpio, pins: &[OutPin], vals: &[bool]) {
    for i in 0..pins.len() {
        gpio.write(pins[i], vals[i]);
    }
}


// EXERCISE 4: fix spec for setup_status_led
fn app() {
    // Get mutable access to GPIOA
    let mut peripherals = take_peripherals().expect("Peripherals already taken");
    let gpio_c = &mut peripherals.gpio_c;

    // Setup the status LED safely
    setup_status_led(gpio_c);

    loop {
        // Main application loop
        // Read sensors
        // let sensor_data = read_sensors();
        // Process data
        // let result = process_data(sensor_data);
        // Update outputs
        // update_outputs(result);

        // Blink status LED to indicate system is alive
        blink_status_led(gpio_c);
    }
}

// EXERCISE 4
#[spec(fn(gpio: &mut Gpio[@modes]) ensures gpio: Gpio[set_mode(modes, 13, Mode::Output)])] // boo strong reference!
fn setup_status_led(gpio: &mut Gpio) {
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