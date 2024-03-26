use std::ops::{Index, IndexMut};
use std::convert::From;

#[derive(Debug)]
pub struct BusReadError;

#[derive(Debug)]
pub struct BusWriteError;

pub trait Bus {
    fn read(&self, addr: u16) -> Result<u8, BusReadError>;
    fn write(&mut self, addr: u16, data: u8) -> Result<(), BusWriteError>;
}

#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Flags([bool; 7]);

pub struct Cpu<T: Bus> {
    pub pc: u16,
    pub a: u8,
    pub x: u8,
    pub y: u8,
    pub s: u8,
    pub p: Flags,
    pub stack: [u8; 256],
    bus: T,
}

enum Op {
    ADC(u8),
    AND(u8),
    ASL(u16),
    BCC(u16),
    BCS(u16),
    BEQ(u16),
    BIT(u16),
    BMI(u16),
    BNE(u16),
    BPL(u16),
    BRK,
    BVC(u16),
    BVS(u16),
    CLC,
    CLD,
    CLI,
    CLV,
    CMP(u8),
    CPX(u8),
    CPY(u8),
    DEC(u16),
}

enum Flag {
    Negative,
    Overflow,
    Break,
    Decimal,
    InterruptDisable,
    Zero,
    Carry,
}

impl<T: Bus> Cpu<T> {
    pub fn new(bus: T) -> Self {
        Self {
            pc: 0,
            a: 0,
            x: 0,
            y: 0,
            s: 0xff,
            p: Flags([false; 7]), // N,V,B,D,I,Z,C
            stack: [0; 256],
            bus,
        }
    }

    pub fn reset(&mut self) {
        self.pc = 0;
        self.a = 0;
        self.x = 0;
        self.y = 0;
        self.s = 0xff;
        self.p = Flags([false; 7]);
    }

    fn stack_push(&mut self, byte: u8) {
        self.stack[self.s as usize] = byte;
        self.s = self.s.wrapping_sub(1);
    }

    fn stack_pop(&mut self) -> u8 {
        self.s = self.s.wrapping_add(1);
        self.stack[self.s as usize]
    }

    fn execute(&mut self, op: Op) {
        match op {
            Op::ADC(x) => {
                let carry = self.p[Flag::Carry] as u8;
                let (unsigned_result, has_carried) = self.a.overflowing_add(x + carry);
                let (signed_result, has_overflowed) = (self.a as i8).overflowing_add_unsigned(x + carry);
                self.a = unsigned_result;
                self.p[Flag::Negative] = signed_result < 0;
                self.p[Flag::Overflow] = has_overflowed;
                self.p[Flag::Zero] = unsigned_result == 0;
                self.p[Flag::Carry] = has_carried;

            },
            Op::AND(x) => {
                let unsigned_result = self.a & x;
                let signed_result = unsigned_result as i8;
                self.a = unsigned_result;
                self.p[Flag::Zero] = unsigned_result == 0;
                self.p[Flag::Negative] = signed_result < 0;
            },
            Op::ASL(addr) => {
                let byte = self.bus.read(addr).unwrap();
                let bit_seven = (byte & 0b10000000) >> 7;
                let unsigned_result = byte << 1;
                let signed_result = unsigned_result as i8;
                self.bus.write(addr, unsigned_result).unwrap();
                self.p[Flag::Carry] = bit_seven != 0;
                self.p[Flag::Zero] = unsigned_result == 0;
                self.p[Flag::Negative] = signed_result < 0;
            },
            Op::BCC(x) => {
                if !self.p[Flag::Carry] {
                    self.pc = self.pc.wrapping_add(x);
                }
            },
            Op::BCS(x) => {
                if self.p[Flag::Carry] {
                    self.pc = self.pc.wrapping_add(x);
                }
            },
            Op::BEQ(x) => {
                if self.p[Flag::Zero] {
                    self.pc = self.pc.wrapping_add(x);
                }
            },
            Op::BIT(addr) => {
                let byte = self.bus.read(addr).unwrap();
                let bit_seven = (byte & 0b10000000) >> 7;
                let bit_six = (byte & 0b01000000) >> 6;
                self.p[Flag::Zero] = (self.a & byte) == 0;
                self.p[Flag::Negative] = bit_seven != 0;
                self.p[Flag::Overflow] = bit_six != 0;
            },
            Op::BMI(x) => {
                if self.p[Flag::Negative] {
                    self.pc = self.pc.wrapping_add(x);
                }
            },
            Op::BNE(x) => {
                if !self.p[Flag::Zero] {
                    self.pc = self.pc.wrapping_add(x);
                }
            },
            Op::BPL(x) => {
                if !self.p[Flag::Negative] {
                    self.pc = self.pc.wrapping_add(x);
                }
            },
            Op::BRK => {
                let pc = self.pc.to_le_bytes();
                self.stack_push(pc[0]);
                self.stack_push(pc[1]);
                self.stack_push(u8::from(self.p));
            },
            Op::BVC(x) => {
                if !self.p[Flag::Overflow] {
                    self.pc += x;
                }
            },
            Op::BVS(x) => {
                if self.p[Flag::Overflow] {
                    self.pc += x;
                }
            },
            Op::CLC => {
                self.p[Flag::Carry] = false;
            },
            Op::CLD => {
                self.p[Flag::Decimal] = false;
            },
            Op::CLI => {
                self.p[Flag::InterruptDisable] = false;
            },
            Op::CLV => {
                self.p[Flag::Overflow] = false;
            },
            Op::CMP(x) => {
                let (result, _) = self.a.overflowing_sub(x);
                self.p[Flag::Carry] = self.a >= x;
                self.p[Flag::Zero] = self.a == x;
                self.p[Flag::Negative] = (result as i8) < 0;
            },
            Op::CPX(x) => {
                let (result, _) = self.x.overflowing_sub(x);
                self.p[Flag::Carry] = self.x >= x;
                self.p[Flag::Zero] = self.x == x;
                self.p[Flag::Negative] = (result as i8) < 0;
            },
            Op::CPY(x) => {
                let (result, _) = self.y.overflowing_sub(x);
                self.p[Flag::Carry] = self.y >= x;
                self.p[Flag::Zero] = self.y == x;
                self.p[Flag::Negative] = (result as i8) < 0;
            },
            Op::DEC(addr) => {
                let byte = self.bus.read(addr).unwrap();
                let result = byte.wrapping_sub(1);
                self.bus.write(addr, result).unwrap();
                self.p[Flag::Zero] = result == 0;
                self.p[Flag::Negative] = (result as i8) < 0;
            },
        }
    }
}

impl Index<Flag> for Flags {
    type Output = bool;

    fn index(&self, flag: Flag) -> &Self::Output {
        &self.0[flag as usize]
    }
}

impl IndexMut<Flag> for Flags {
    fn index_mut(&mut self, flag: Flag) -> &mut Self::Output {
        &mut self.0[flag as usize]
    }
}

impl From<Flags> for u8 {
    fn from(value: Flags) -> u8 {
        value.0.iter().enumerate().fold(0, |acc, (i, val)| {
            if i == 1 {
                2 * (acc * 2 + (*val as u8)) + 1
            } else {
                acc * 2 + (*val as u8)
            }
        })
    }
}

impl From<u8> for Flags {
    fn from(mut value: u8) -> Flags {
        let mut res = [false; 7];
        for (i, val) in res.iter_mut().rev().enumerate() {
            if i == 5 {
                value >>= 1;
            }
            *val = (value % 2) != 0;
            value >>= 1;
        }
        Flags(res)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestBus {
        pub ram: [u8; 5]
    }

    impl TestBus {
        fn new() -> Self {
            Self {
                ram: [0; 5],
            }
        }
    }

    impl Bus for TestBus {
        fn read(&self, addr: u16) -> Result<u8, BusReadError> {
            if (addr as usize) < self.ram.len() {
                return Ok(self.ram[addr as usize]);
            }
            Err(BusReadError{})
        }

        fn write(&mut self, addr: u16, data: u8) -> Result<(), BusWriteError> {
            if (addr as usize) < self.ram.len() {
                self.ram[addr as usize] = data;
                return Ok(())
            }
            Err(BusWriteError{})
        }
    }

    #[test]
    fn flags_to_u8() {
        let (mut result, mut expected);
        expected = 0b00100000;
        result = u8::from(Flags([false; 7]));
        assert!(
            result == expected,
            "Result {:b}, Expected {:b}",
            result,
            expected
        );
        expected = 0b11111111;
        result = u8::from(Flags([true; 7]));
        assert!(
            result == expected,
            "Result {:b}, Expected {:b}",
            result,
            expected
        );
        expected = 0b10111001;
        result = u8::from(Flags([true, false, true, true, false, false, true]));
        assert!(
            result == expected,
            "Result {:b}, Expected {:b}",
            result,
            expected
        );
    }

    #[test]
    fn u8_to_flags() {
        let (mut result, mut expected);
        expected = Flags([false; 7]);
        result = Flags::from(0b00100000);
        assert!(
            result == expected,
            "Result {:?}, Expected {:?}",
            result,
            expected
        );
        expected = Flags([true; 7]);
        result = Flags::from(0b11111111);
        assert!(
            result == expected,
            "Result {:?}, Expected {:?}",
            result,
            expected
        );
        expected = Flags([false, true, true, true, false, true, false]);
        result = Flags::from(0b01111010);
        assert!(
            result == expected,
            "Result {:?}, Expected {:?}",
            result,
            expected
        );
    }

    #[test]
    fn stack_push() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // correctly adjusts stack pointer
        cpu.reset();
        expected = 0xfe;
        x = 0x23;
        cpu.stack_push(x);
        result = cpu.s;
        assert!(
            result == expected,
            "S not adjusted correctly. Result {}, Expected {}",
            result,
            expected
        );

        // stack values pushed correctly 
        cpu.reset();
        x = 0x23;
        expected = x;
        cpu.stack_push(x);
        result = cpu.stack[0xff];
        assert!(
            result == expected,
            "First byte of stack is wrong. Result {}, Expected {}",
            result,
            expected
        );

        // stack pointer overflows as expected
        cpu.reset();
        expected = 0;
        cpu.stack_pop();
        result = cpu.s;
        assert!(
            result == expected,
            "S does not overflow as expected. Result {}, Expected {}",
            result,
            expected
        );

        // stack pointer underflows as expected
        cpu.reset();
        cpu.s = 0;
        x = 0x23;
        cpu.stack_push(x);
        expected = 0xff;
        result = cpu.s;
        assert!(
            result == expected,
            "S does not underflow as expected. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_adc() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // no carry bit
        cpu.reset();
        x = 0x8;
        cpu.a = 0x23;
        expected = x + cpu.a;
        cpu.execute(Op::ADC(x));
        result = cpu.a;
        assert!(
            result == expected,
            "Incorrect value in A register. Result: {}, Expected: {}",
            result,
            expected
        );

        // with carry bit
        cpu.reset();
        cpu.p[Flag::Carry] = true;
        x = 0x12;
        cpu.a = 0x15;
        expected = x + cpu.a + 1;
        cpu.execute(Op::ADC(x));
        result = cpu.a;
        assert!(
            result == expected,
            "Incorrect value in A register when carry bit set. Result: {}, Expected: {}",
            result,
            expected
        );

        // does not set carry flag on non overflowing op
        cpu.reset();
        x = 0x10;
        cpu.a = 0x0f;
        expected = 0;
        cpu.execute(Op::ADC(x));
        result = cpu.p[Flag::Carry] as u8;
        assert!(
            result == expected,
            "Carry flag not set correctly on non overflowing op. Result {}, Expected {}",
            result,
            expected
        );

        // sets carry flag on unsigned overflow
        cpu.reset();
        x = 0x5;
        cpu.a = 0xff;
        expected = 1;
        cpu.execute(Op::ADC(x));
        result = cpu.p[Flag::Carry] as u8;
        assert!(
            result == expected,
            "Carry flag not set correctly on unsigned overflow. Result {}, Expected {}",
            result,
            expected
        );

        // clears carry flag on non overflowing op
        cpu.reset();
        x = 0x5;
        cpu.a = 0x54;
        expected = 0;
        cpu.p[Flag::Carry] = true;
        cpu.execute(Op::ADC(x));
        result = cpu.p[Flag::Carry] as u8;
        assert!(
            result == expected,
            "Carry flag not cleared correctly on non overflowing op. Result {}, Expected {}",
            result,
            expected
        );

        // sets overflow flag on signed overflow
        cpu.reset();
        x = 1;
        cpu.a = 127;
        expected = 1;
        cpu.execute(Op::ADC(x));
        result = cpu.p[Flag::Overflow] as u8;
        assert!(
            result == expected,
            "Overflow flag is not set correctly on signed overflow. Result {}, Expected {}",
            result,
            expected
        );

        // does not set overflow flag on signed nonoverflowing op
        cpu.reset();
        x = 1;
        cpu.a = 126;
        expected = 0;
        cpu.execute(Op::ADC(x));
        result = cpu.p[Flag::Overflow] as u8;
        assert!(
            result == expected,
            "Overflow not set correctly on signed non overflowing op. Result {}, Expected {}",
            result,
            expected
        );

        // clears overflow flag on signed non overflowing op
        cpu.reset();
        x = 1;
        cpu.a = 10;
        expected = 0;
        cpu.p[Flag::Overflow] = true;
        cpu.execute(Op::ADC(x));
        result = cpu.p[Flag::Overflow] as u8;
        assert!(
            result == expected,
            "Overflow flag not cleared correctly on signed non overflowing op. Result {}, Expected {}", 
            result, 
            expected
        );

        // sets negative flag correctly
        cpu.reset();
        x = 5;
        cpu.a = 10u8.wrapping_neg(); 
        expected = 1;
        cpu.execute(Op::ADC(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not set correctly on negative sum. Result {}, Expected {}",
            result,
            expected
        );

        // clears negative flag correctly
        cpu.reset();
        x = 12;
        cpu.a = 10u8.wrapping_neg();
        expected = 0;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::ADC(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not cleared correctly on non-negative sum. Result {}, Expected {}",
            result,
            expected
        );

        // sets zero flag correctly
        cpu.reset();
        x = 10;
        cpu.a = 10u8.wrapping_neg(); 
        expected = 1;
        cpu.execute(Op::ADC(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not set correctly on zero sum. Result {}, Expected {}",
            result,
            expected
        );

        // clears zero flag correctly
        cpu.reset();
        x = 12;
        cpu.a = 6;
        expected = 0;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::ADC(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not cleared correctly on non-zero sum. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_and() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // correct answer
        cpu.reset();
        x = 0b00110101;
        cpu.a = 0b11010011;
        expected = 0b00010001;
        cpu.execute(Op::AND(x));
        result = cpu.a;
        assert!(
            result == expected,
            "A register contains incorrect result. Expected {}, Result {}",
            result,
            expected
        );

        // sets zero flag correctly
        cpu.reset();
        x = 0b01010101;
        cpu.a = 0b10101010;
        expected = 1;
        cpu.execute(Op::AND(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not set correctly. Expected {}, Result {}",
            result,
            expected
        );

        // clears zero flag correctly 
        cpu.reset();
        x = 0b01010101;
        cpu.a = 0b10111010;
        expected = 0;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::AND(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not cleared correctly. Expected {}, Result {}",
            result,
            expected
        );

        // sets negative flag correctly
        cpu.reset();
        x = 0b11010101;
        cpu.a = 0b10101010;
        expected = 1;
        cpu.execute(Op::AND(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not set correctly. Expected {}, Result {}",
            result,
            expected
        );

        // clears negative flag correctly 
        cpu.reset();
        x = 0b01010101;
        cpu.a = 0b10111010;
        expected = 0;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::AND(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not cleared correctly. Expected {}, Result {}",
            result,
            expected
        );
    }

    #[test]
    fn op_asl() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut addr, mut result, mut expected);

        // shifts correctly
        cpu.reset();
        addr = 2u16;
        cpu.bus.ram[addr as usize] = 2;
        expected = 0b00000100;
        cpu.execute(Op::ASL(addr));
        result = cpu.bus.read(addr).unwrap();
        assert!(
            result == expected,
            "Incorrect value in memory. Expected {}, Result {}",
            result,
            expected
        );

        // sets carry correctly
        cpu.reset();
        addr = 3u16;
        cpu.bus.ram[addr as usize] = 0b10001000;
        expected = 1;
        cpu.execute(Op::ASL(addr));
        result = cpu.p[Flag::Carry] as u8;
        assert!(
            result == expected,
            "Carry flag set incorrectly. Expected {}, Result {}",
            result,
            expected
        );

        // clears carry correctly
        cpu.reset();
        addr = 1u16;
        cpu.bus.ram[addr as usize] = 0b01001111;
        expected = 0;
        cpu.p[Flag::Carry] = true;
        cpu.execute(Op::ASL(addr));
        result = cpu.p[Flag::Carry] as u8;
        assert!(
            result == expected,
            "Carry flag cleared incorrectly. Expected {}, Result {}",
            result,
            expected
        );

        // sets zero flag correctly
        cpu.reset();
        addr = 4u16;
        cpu.bus.ram[addr as usize] = 0b10000000;
        expected = 1;
        cpu.execute(Op::ASL(addr));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag set incorrectly. Expected {}, Result {}",
            result,
            expected
        );

        // clears zero flag correctly
        cpu.reset();
        addr = 4u16;
        cpu.bus.ram[addr as usize] = 0b01001111;
        expected = 0;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::ASL(addr));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Expected {}, Result {}",
            result,
            expected
        );

        // sets negative flag correctly
        cpu.reset();
        addr = 4u16;
        cpu.bus.ram[addr as usize] = 0b01000001;
        expected = 1;
        cpu.execute(Op::ASL(addr));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag set incorrectly. Expected {}, Result {}",
            result,
            expected
        );

        // clears negative flag correctly
        cpu.reset();
        addr = 4u16;
        cpu.bus.ram[addr as usize] = 0b00001111;
        expected = 0;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::ASL(addr));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Expected {}, Result {}",
            result,
            expected
        );
    }

    #[test]
    fn op_bcc() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // branches when carry cleared
        cpu.reset();
        x = 0x1123;
        expected = cpu.pc + x;
        cpu.p[Flag::Carry] = false;
        cpu.execute(Op::BCC(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on branching. Expected {}, Result {}",
            result,
            expected
        );

        // does not branch when carry set
        cpu.reset();
        x = 0x2232;
        expected = cpu.pc;
        cpu.p[Flag::Carry] = true;
        cpu.execute(Op::BCC(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on non-branching. Expected {}, Result {}",
            result,
            expected
        );
    }
    #[test]
    fn op_bcs() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // branches when carry set
        cpu.reset();
        x = 0x1189;
        expected = cpu.pc + x;
        cpu.p[Flag::Carry] = true;
        cpu.execute(Op::BCS(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on branching. Expected {}, Result {}",
            result,
            expected
        );

        // does not branch when carry cleared
        cpu.reset();
        x = 0x2211;
        expected = cpu.pc;
        cpu.p[Flag::Carry] = false;
        cpu.execute(Op::BCS(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on non-branching. Expected {}, Result {}",
            result,
            expected
        );
    }
    #[test]
    fn op_beq() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // branches when zero flag set
        cpu.reset();
        x = 0x3102;
        expected = cpu.pc + x;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::BEQ(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on branching. Expected {}, Result {}",
            result,
            expected
        );

        // does not branch when zero flag cleared
        cpu.reset();
        x = 0x1111;
        expected = cpu.pc;
        cpu.p[Flag::Zero] = false;
        cpu.execute(Op::BEQ(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on non-branching. Expected {}, Result {}",
            result,
            expected
        );
    }

    #[test]
    fn op_bit() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut addr, mut result, mut expected);

        // sets zero flag correctly
        cpu.reset();
        addr = 2u16;
        cpu.a = 0b11001100;
        cpu.bus.ram[addr as usize] = 0b00110011;
        cpu.p[Flag::Zero] = false;
        expected = true;
        cpu.execute(Op::BIT(addr));
        result = cpu.p[Flag::Zero];
        assert!(
            result == expected,
            "Incorrect setting of zero flag. Expected {}, Result {}",
            result,
            expected
        );

        // clears zero flag correctly
        cpu.reset();
        addr = 3u16;
        cpu.a = 0b11011100;
        cpu.bus.ram[addr as usize] = 0b00111111;
        cpu.p[Flag::Zero] = true;
        expected = false;
        cpu.execute(Op::BIT(addr));
        result = cpu.p[Flag::Zero];
        assert!(
            result == expected,
            "Incorrect clearing of zero flag. Expected {}, Result {}",
            result,
            expected
        );

        // sets negative flag correctly
        cpu.reset();
        addr = 1u16;
        cpu.a = 0b01010000;
        cpu.bus.ram[addr as usize] = 0b10110011;
        cpu.p[Flag::Negative] = false;
        expected = true;
        cpu.execute(Op::BIT(addr));
        result = cpu.p[Flag::Negative];
        assert!(
            result == expected,
            "Incorrect setting of negative flag. Expected {}, Result {}",
            result,
            expected
        );

        // clears negative flag correctly
        cpu.reset();
        addr = 3u16;
        cpu.a = 0b11011100;
        cpu.bus.ram[addr as usize] = 0b01111111;
        cpu.p[Flag::Negative] = true;
        expected = false;
        cpu.execute(Op::BIT(addr));
        result = cpu.p[Flag::Negative];
        assert!(
            result == expected,
            "Incorrect clearing of negative flag. Expected {}, Result {}",
            result,
            expected
        );

        // sets overflow flag correctly
        cpu.reset();
        addr = 0u16;
        cpu.a = 0b01010000;
        cpu.bus.ram[addr as usize] = 0b01010011;
        cpu.p[Flag::Overflow] = false;
        expected = true;
        cpu.execute(Op::BIT(addr));
        result = cpu.p[Flag::Overflow];
        assert!(
            result == expected,
            "Incorrect setting of overflow flag. Expected {}, Result {}",
            result,
            expected
        );

        // clears overflow flag correctly
        cpu.reset();
        addr = 3u16;
        cpu.a = 0b11011100;
        cpu.bus.ram[addr as usize] = 0b10111111;
        cpu.p[Flag::Overflow] = true;
        expected = false;
        cpu.execute(Op::BIT(addr));
        result = cpu.p[Flag::Overflow];
        assert!(
            result == expected,
            "Incorrect clearing of overflow flag. Expected {}, Result {}",
            result,
            expected
        );
    }

    #[test]
    fn op_bmi() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // branches when negative flag set
        cpu.reset();
        x = 0x3456;
        expected = cpu.pc + x;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::BMI(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on branching. Expected {}, Result {}",
            result,
            expected
        );

        // does not branch when negative flag clear
        cpu.reset();
        x = 0x2238;
        expected = cpu.pc;
        cpu.p[Flag::Negative] = false;
        cpu.execute(Op::BMI(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on non-branching. Expected {}, Result {}",
            result,
            expected
        );
    }

    #[test]
    fn op_bne() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // branches when zero flag clear
        cpu.reset();
        x = 0x1234;
        expected = cpu.pc + x;
        cpu.p[Flag::Zero] = false;
        cpu.execute(Op::BNE(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on branching. Expected {}, Result {}",
            result,
            expected
        );

        // does not branch when zero flag set
        cpu.reset();
        x = 0x1111;
        expected = cpu.pc;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::BNE(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on non-branching. Expected {}, Result {}",
            result,
            expected
        );
    }

    #[test]
    fn op_bpl() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // branches when negative flag clear
        cpu.reset();
        x = 0x0532;
        expected = cpu.pc + x;
        cpu.p[Flag::Negative] = false;
        cpu.execute(Op::BPL(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on branching. Expected {}, Result {}",
            result,
            expected
        );

        // does not branch when negative flag set
        cpu.reset();
        x = 0x2222;
        expected = cpu.pc;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::BPL(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on non-branching. Expected {}, Result {}",
            result,
            expected
        );
    }

    #[test]
    fn op_brk() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut result, mut expected);
        
        // stack contains correct values
        cpu.reset();
        cpu.pc = 0x2345;
        cpu.p = Flags([false, false, true, true, false, true, false]);
        cpu.execute(Op::BRK);
        expected = 0x45;
        result = cpu.stack[0xff];
        assert!(
            result == expected,
            "First byte incorrect. Result {}, Expected {}",
            result, 
            expected
        );
        expected = 0x23;
        result = cpu.stack[0xfe];
        assert!(
            result == expected,
            "Second byte incorrect. Result {}, Expected {}",
            result,
            expected
        );
        expected = 0b00111010;
        result = cpu.stack[0xfd];
        assert!(
            result == expected,
            "Third byte incorrect. Result {}, Expected {}",
            result,
            expected
        );
    }
    #[test]
    fn op_bvc() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // branches when overflow cleared
        cpu.reset();
        x = 0x5555;
        expected = cpu.pc + x;
        cpu.p[Flag::Overflow] = false;
        cpu.execute(Op::BVC(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on branching. Expected {}, Result {}",
            result,
            expected
        );

        // does not branch when overflow set
        cpu.reset();
        x = 0x1234;
        expected = cpu.pc;
        cpu.p[Flag::Overflow] = true;
        cpu.execute(Op::BVC(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on non-branching. Expected {}, Result {}",
            result,
            expected
        );
    }
    #[test]
    fn op_bvs() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // branches when overflow set
        cpu.reset();
        x = 0x1155;
        expected = cpu.pc + x;
        cpu.p[Flag::Overflow] = true;
        cpu.execute(Op::BVS(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on branching. Expected {}, Result {}",
            result,
            expected
        );

        // does not branch when overflow cleared
        cpu.reset();
        x = 0x1122;
        expected = cpu.pc;
        cpu.p[Flag::Overflow] = false;
        cpu.execute(Op::BVS(x));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value on non-branching. Expected {}, Result {}",
            result,
            expected
        );
    }

    #[test]
    fn op_clc() {
        let mut cpu = Cpu::new(TestBus::new());

        let expected = false;
        cpu.p[Flag::Carry] = true;
        cpu.execute(Op::CLC);
        let result = cpu.p[Flag::Carry];
        assert!(
            result == expected,
            "Carry not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }
    #[test]
    fn op_cld() {
        let mut cpu = Cpu::new(TestBus::new());

        let expected = false;
        cpu.p[Flag::Decimal] = true;
        cpu.execute(Op::CLD);
        let result = cpu.p[Flag::Decimal];
        assert!(
            result == expected,
            "Decimal flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }
    #[test]
    fn op_cli() {
        let mut cpu = Cpu::new(TestBus::new());

        let expected = false;
        cpu.p[Flag::InterruptDisable] = true;
        cpu.execute(Op::CLI);
        let result = cpu.p[Flag::InterruptDisable];
        assert!(
            result == expected,
            "Interrupt disable flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }
    #[test]
    fn op_clv() {
        let mut cpu = Cpu::new(TestBus::new());

        let expected = false;
        cpu.p[Flag::Overflow] = true;
        cpu.execute(Op::CLV);
        let result = cpu.p[Flag::Overflow];
        assert!(
            result == expected,
            "Overflow flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }
    #[test]
    fn op_cmp() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // sets carry flag correctly
        cpu.reset();
        cpu.a = 0x8a;
        x = 0x21;
        expected = true;
        cpu.execute(Op::CMP(x));
        result = cpu.p[Flag::Carry];
        assert!(
            result == expected,
            "Carry flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears carry flag correctly
        cpu.reset();
        cpu.a = 0x21;
        x = 0x8a;
        cpu.p[Flag::Carry] = true;
        expected = false;
        cpu.execute(Op::CMP(x));
        result = cpu.p[Flag::Carry];
        assert!(
            result == expected,
            "Carry flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // sets zero flag correctly
        cpu.reset();
        cpu.a = 0x57;
        x = 0x57;
        cpu.p[Flag::Zero] = false;
        expected = true;
        cpu.execute(Op::CMP(x));
        result = cpu.p[Flag::Carry];
        assert!(
            result == expected,
            "Zero flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears zero flag correctly
        cpu.reset();
        cpu.a = 0x82;
        x = 0x59;
        cpu.p[Flag::Zero] = true;
        expected = false;
        cpu.execute(Op::CMP(x));
        result = cpu.p[Flag::Zero];
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );
        
        // sets negative flag correctly
        cpu.reset();
        cpu.a = 0x32;
        x = 0x42;
        cpu.p[Flag::Negative] = false;
        expected = true;
        cpu.execute(Op::CMP(x));
        result = cpu.p[Flag::Negative];
        assert!(
            result == expected,
            "Negative flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears negative flag correctly
        cpu.reset();
        cpu.a = 0x82;
        x = 0x51;
        cpu.p[Flag::Negative] = true;
        expected = false;
        cpu.execute(Op::CMP(x));
        result = cpu.p[Flag::Negative];
        assert!(
            result == expected,
            "Negative flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );
    }
    #[test]
    fn op_cpx() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // sets carry flag correctly
        cpu.reset();
        cpu.x = 0xaa;
        x = 0x92;
        expected = true;
        cpu.execute(Op::CPX(x));
        result = cpu.p[Flag::Carry];
        assert!(
            result == expected,
            "Carry flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears carry flag correctly
        cpu.reset();
        cpu.x = 0x41;
        x = 0x7a;
        cpu.p[Flag::Carry] = true;
        expected = false;
        cpu.execute(Op::CPX(x));
        result = cpu.p[Flag::Carry];
        assert!(
            result == expected,
            "Carry flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // sets zero flag correctly
        cpu.reset();
        cpu.x = 0x99;
        x = 0x99;
        cpu.p[Flag::Zero] = false;
        expected = true;
        cpu.execute(Op::CPX(x));
        result = cpu.p[Flag::Carry];
        assert!(
            result == expected,
            "Zero flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears zero flag correctly
        cpu.reset();
        cpu.x = 0x12;
        x = 0x59;
        cpu.p[Flag::Zero] = true;
        expected = false;
        cpu.execute(Op::CPX(x));
        result = cpu.p[Flag::Zero];
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );
        
        // sets negative flag correctly
        cpu.reset();
        cpu.x = 0x12;
        x = 0x2a;
        cpu.p[Flag::Negative] = false;
        expected = true;
        cpu.execute(Op::CPX(x));
        result = cpu.p[Flag::Negative];
        assert!(
            result == expected,
            "Negative flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears negative flag correctly
        cpu.reset();
        cpu.x = 0x7f;
        x = 0x01;
        cpu.p[Flag::Negative] = true;
        expected = false;
        cpu.execute(Op::CPX(x));
        result = cpu.p[Flag::Negative];
        assert!(
            result == expected,
            "Negative flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );
    }
    #[test]
    fn op_cpy() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // sets carry flag correctly
        cpu.reset();
        cpu.y = 0xff;
        x = 0x23;
        expected = true;
        cpu.execute(Op::CPY(x));
        result = cpu.p[Flag::Carry];
        assert!(
            result == expected,
            "Carry flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears carry flag correctly
        cpu.reset();
        cpu.y = 0x21;
        x = 0xff;
        cpu.p[Flag::Carry] = true;
        expected = false;
        cpu.execute(Op::CPY(x));
        result = cpu.p[Flag::Carry];
        assert!(
            result == expected,
            "Carry flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // sets zero flag correctly
        cpu.reset();
        cpu.y = 0xa2;
        x = 0xa2;
        cpu.p[Flag::Zero] = false;
        expected = true;
        cpu.execute(Op::CPY(x));
        result = cpu.p[Flag::Carry];
        assert!(
            result == expected,
            "Zero flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears zero flag correctly
        cpu.reset();
        cpu.y = 0x02;
        x = 0x59;
        cpu.p[Flag::Zero] = true;
        expected = false;
        cpu.execute(Op::CPY(x));
        result = cpu.p[Flag::Zero];
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );
        
        // sets negative flag correctly
        cpu.reset();
        cpu.y = 0xf2;
        x = 0x1a;
        cpu.p[Flag::Negative] = false;
        expected = true;
        cpu.execute(Op::CPY(x));
        result = cpu.p[Flag::Negative];
        assert!(
            result == expected,
            "Negative flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears negative flag correctly
        cpu.reset();
        cpu.y = 0x4f;
        x = 0x05;
        cpu.p[Flag::Negative] = true;
        expected = false;
        cpu.execute(Op::CPY(x));
        result = cpu.p[Flag::Negative];
        assert!(
            result == expected,
            "Negative flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_dec() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut addr, mut result, mut expected);

        // value correct
        cpu.reset();
        addr = 2;
        x = 0x43;
        cpu.bus.ram[addr as usize] = x;
        expected = x - 1;
        cpu.execute(Op::DEC(addr));
        result = cpu.bus.ram[addr as usize];
        assert!(
            result == expected,
            "Value incorrect. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag set correctly
        cpu.reset();
        addr = 3;
        x = 0x1;
        cpu.bus.ram[addr as usize] = x;
        expected = true as u8;
        cpu.execute(Op::DEC(addr));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag cleared correctly
        cpu.reset();
        addr = 3;
        x = 0x5;
        cpu.bus.ram[addr as usize] = x;
        expected = false as u8;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::DEC(addr));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag set correctly
        cpu.reset();
        addr = 1;
        x = 0;
        cpu.bus.ram[addr as usize] = x;
        expected = true as u8;
        cpu.execute(Op::DEC(addr));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag cleared correctly
        cpu.reset();
        addr = 3;
        x = 0x32;
        cpu.bus.ram[addr as usize] = x;
        expected = false as u8;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::DEC(addr));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }
}
