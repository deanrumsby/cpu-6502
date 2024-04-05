#![feature(bigint_helper_methods)]

use std::convert::From;
use std::fmt;
use std::ops::{Index, IndexMut};

#[derive(Copy, Clone, PartialEq)]
pub struct Flags([bool; 7]);

pub struct Cpu<T: Bus> {
    pub pc: u16,
    pub a: u8,
    pub x: u8,
    pub y: u8,
    pub s: u8,
    pub p: Flags,
    pub bus: T,
}

impl<T: Bus> PartialEq for Cpu<T> {
    fn eq(&self, other: &Self) -> bool {
        self.pc == other.pc
            && self.a == other.a
            && self.x == other.x
            && self.y == other.y
            && self.s == other.s
            && self.p == other.p
    }
}

impl<T: Bus> fmt::Debug for Cpu<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Cpu")
            .field("pc", &format_args!("{:x}", &self.pc))
            .field("a", &format_args!("{:x}", &self.a))
            .field("x", &format_args!("{:x}", &self.x))
            .field("y", &format_args!("{:x}", &self.y))
            .field("s", &format_args!("{:x}", &self.s))
            .field("p", &self.p)
            .finish()
    }
}

impl fmt::Debug for Flags {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Flags")
            .field("negative", &self[Flag::Negative])
            .field("overlow", &self[Flag::Overflow])
            .field("break", &self[Flag::Break])
            .field("decimal", &self[Flag::Decimal])
            .field("interrupt disable", &self[Flag::InterruptDisable])
            .field("zero", &self[Flag::Zero])
            .field("carry", &self[Flag::Carry])
            .finish()
    }
}

pub trait Bus {
    fn read(&self, addr: u16) -> u8;
    fn write(&mut self, addr: u16, byte: u8);
}

enum Address {
    Accumulator,
    Memory(u16),
}

enum Op {
    ADC(u8),
    AND(u8),
    ASL(Address),
    BCC(u16),
    BCS(u16),
    BEQ(u16),
    BIT(u8),
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
    DEC(Address),
    DEX,
    DEY,
    EOR(u8),
    INC(Address),
    INX,
    INY,
    JMP(u16),
    JSR(u16),
    LDA(u8),
    LDX(u8),
    LDY(u8),
    LSR(Address),
    NOP,
    ORA(u8),
    PHA,
    PHP,
    PLA,
    PLP,
    ROL(Address),
    ROR(Address),
    RTI,
    RTS,
    SBC(u8),
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
        let addr = 0x0100u16 + (self.s as u16);
        self.bus.write(addr, byte);
        self.s = self.s.wrapping_sub(1);
    }

    fn stack_pop(&mut self) -> u8 {
        self.s = self.s.wrapping_add(1);
        let addr = 0x0100u16 + (self.s as u16);
        self.bus.read(addr)
    }

    fn execute(&mut self, op: Op) {
        match op {
            Op::ADC(x) => {
                let carry = self.p[Flag::Carry];
                let (unsigned_result, has_carried) = self.a.carrying_add(x, carry);
                let (signed_result, has_overflowed) = (self.a as i8).carrying_add(x as i8, carry);
                self.a = unsigned_result;
                self.p[Flag::Negative] = signed_result < 0;
                self.p[Flag::Overflow] = has_overflowed;
                self.p[Flag::Zero] = unsigned_result == 0;
                self.p[Flag::Carry] = has_carried;
            }
            Op::AND(x) => {
                let unsigned_result = self.a & x;
                let signed_result = unsigned_result as i8;
                self.a = unsigned_result;
                self.p[Flag::Zero] = unsigned_result == 0;
                self.p[Flag::Negative] = signed_result < 0;
            }
            Op::ASL(addr) => {
                let byte = match addr {
                    Address::Accumulator => self.a,
                    Address::Memory(a) => self.bus.read(a),
                };
                let bit_seven = (byte & 0b10000000) >> 7;
                let unsigned_result = byte << 1;
                let signed_result = unsigned_result as i8;
                match addr {
                    Address::Accumulator => self.a = unsigned_result,
                    Address::Memory(a) => self.bus.write(a, unsigned_result),
                };
                self.p[Flag::Carry] = bit_seven != 0;
                self.p[Flag::Zero] = unsigned_result == 0;
                self.p[Flag::Negative] = signed_result < 0;
            }
            Op::BCC(x) => {
                if !self.p[Flag::Carry] {
                    self.pc = self.pc.wrapping_add(x);
                }
            }
            Op::BCS(x) => {
                if self.p[Flag::Carry] {
                    self.pc = self.pc.wrapping_add(x);
                }
            }
            Op::BEQ(x) => {
                if self.p[Flag::Zero] {
                    self.pc = self.pc.wrapping_add(x);
                }
            }
            Op::BIT(x) => {
                let bit_seven = (x & 0b10000000) >> 7;
                let bit_six = (x & 0b01000000) >> 6;
                self.p[Flag::Zero] = (self.a & x) == 0;
                self.p[Flag::Negative] = bit_seven != 0;
                self.p[Flag::Overflow] = bit_six != 0;
            }
            Op::BMI(x) => {
                if self.p[Flag::Negative] {
                    self.pc = self.pc.wrapping_add(x);
                }
            }
            Op::BNE(x) => {
                if !self.p[Flag::Zero] {
                    self.pc = self.pc.wrapping_add(x);
                }
            }
            Op::BPL(x) => {
                if !self.p[Flag::Negative] {
                    self.pc = self.pc.wrapping_add(x);
                }
            }
            Op::BRK => {
                let pc = self.pc.to_le_bytes();
                self.stack_push(pc[0]);
                self.stack_push(pc[1]);
                self.stack_push(u8::from(self.p));
                self.pc = 0xfffe;
                self.p[Flag::Break] = true;
            }
            Op::BVC(x) => {
                if !self.p[Flag::Overflow] {
                    self.pc += x;
                }
            }
            Op::BVS(x) => {
                if self.p[Flag::Overflow] {
                    self.pc += x;
                }
            }
            Op::CLC => {
                self.p[Flag::Carry] = false;
            }
            Op::CLD => {
                self.p[Flag::Decimal] = false;
            }
            Op::CLI => {
                self.p[Flag::InterruptDisable] = false;
            }
            Op::CLV => {
                self.p[Flag::Overflow] = false;
            }
            Op::CMP(x) => {
                let (result, _) = self.a.overflowing_sub(x);
                self.p[Flag::Carry] = self.a >= x;
                self.p[Flag::Zero] = self.a == x;
                self.p[Flag::Negative] = (result as i8) < 0;
            }
            Op::CPX(x) => {
                let (result, _) = self.x.overflowing_sub(x);
                self.p[Flag::Carry] = self.x >= x;
                self.p[Flag::Zero] = self.x == x;
                self.p[Flag::Negative] = (result as i8) < 0;
            }
            Op::CPY(x) => {
                let (result, _) = self.y.overflowing_sub(x);
                self.p[Flag::Carry] = self.y >= x;
                self.p[Flag::Zero] = self.y == x;
                self.p[Flag::Negative] = (result as i8) < 0;
            }
            Op::DEC(addr) => {
                let addr = match addr {
                    Address::Memory(a) => a,
                    _ => panic!("invalid address"),
                };
                let result = self.bus.read(addr).wrapping_sub(1);
                self.bus.write(addr, result);
                self.p[Flag::Zero] = result == 0;
                self.p[Flag::Negative] = (result as i8) < 0;
            }
            Op::DEX => {
                self.x = self.x.wrapping_sub(1);
                self.p[Flag::Zero] = self.x == 0;
                self.p[Flag::Negative] = (self.x as i8) < 0;
            }
            Op::DEY => {
                self.y = self.y.wrapping_sub(1);
                self.p[Flag::Zero] = self.y == 0;
                self.p[Flag::Negative] = (self.y as i8) < 0;
            }
            Op::EOR(x) => {
                self.a ^= x;
                self.p[Flag::Zero] = self.a == 0;
                self.p[Flag::Negative] = (self.a as i8) < 0;
            }
            Op::INC(addr) => {
                let addr = match addr {
                    Address::Memory(a) => a,
                    _ => panic!("invalid address"),
                };
                let result = self.bus.read(addr).wrapping_add(1);
                self.bus.write(addr, result);
                self.p[Flag::Zero] = result == 0;
                self.p[Flag::Negative] = (result as i8) < 0;
            }
            Op::INX => {
                self.x = self.x.wrapping_add(1);
                self.p[Flag::Zero] = self.x == 0;
                self.p[Flag::Negative] = (self.x as i8) < 0;
            }
            Op::INY => {
                self.y = self.y.wrapping_add(1);
                self.p[Flag::Zero] = self.y == 0;
                self.p[Flag::Negative] = (self.y as i8) < 0;
            }
            Op::JMP(addr) => {
                self.pc = addr;
            }
            Op::JSR(addr) => {
                let pc = self.pc.to_le_bytes();
                self.stack_push(pc[0]);
                self.stack_push(pc[1]);
                self.pc = addr;
            }
            Op::LDA(x) => {
                self.a = x;
                self.p[Flag::Zero] = x == 0;
                self.p[Flag::Negative] = (x as i8) < 0;
            }
            Op::LDX(x) => {
                self.x = x;
                self.p[Flag::Zero] = x == 0;
                self.p[Flag::Negative] = (x as i8) < 0;
            }
            Op::LDY(x) => {
                self.y = x;
                self.p[Flag::Zero] = x == 0;
                self.p[Flag::Negative] = (x as i8) < 0;
            }
            Op::LSR(addr) => {
                let byte = match addr {
                    Address::Accumulator => self.a,
                    Address::Memory(a) => self.bus.read(a),
                };
                let bit_zero = byte & 0b00000001;
                let result = byte >> 1;
                match addr {
                    Address::Accumulator => self.a = result,
                    Address::Memory(a) => self.bus.write(a, result),
                }
                self.p[Flag::Carry] = bit_zero != 0;
                self.p[Flag::Zero] = result == 0;
                self.p[Flag::Negative] = false;
            }
            Op::NOP => {}
            Op::ORA(x) => {
                self.a |= x;
                self.p[Flag::Zero] = self.a == 0;
                self.p[Flag::Negative] = (self.a as i8) < 0;
            }
            Op::PHA => {
                self.stack_push(self.a);
            }
            Op::PHP => {
                self.stack_push(u8::from(self.p));
            }
            Op::PLA => {
                self.a = self.stack_pop();
                self.p[Flag::Zero] = self.a == 0;
                self.p[Flag::Negative] = (self.a as i8) < 0;
            }
            Op::PLP => {
                self.p = Flags::from(self.stack_pop());
            }
            Op::ROL(addr) => {
                let byte = match addr {
                    Address::Accumulator => self.a,
                    Address::Memory(a) => self.bus.read(a),
                };
                let bit_seven = 0b10000000 & byte;
                let bit_zero = self.p[Flag::Carry] as u8;
                let result = (byte << 1) + bit_zero;
                match addr {
                    Address::Accumulator => self.a = result,
                    Address::Memory(a) => self.bus.write(a, result),
                };
                self.p[Flag::Carry] = bit_seven != 0;
                self.p[Flag::Zero] = result == 0;
                self.p[Flag::Negative] = (result as i8) < 0;
            }
            Op::ROR(addr) => {
                let byte = match addr {
                    Address::Accumulator => self.a,
                    Address::Memory(a) => self.bus.read(a),
                };
                let bit_zero = 0b00000001 & byte;
                let bit_seven = self.p[Flag::Carry] as u8;
                let result = (byte >> 1) + bit_seven * 128;
                match addr {
                    Address::Accumulator => self.a = result,
                    Address::Memory(a) => self.bus.write(a, result),
                };
                self.p[Flag::Carry] = bit_zero != 0;
                self.p[Flag::Zero] = result == 0;
                self.p[Flag::Negative] = (result as i8) < 0;
            }
            Op::RTI => {
                self.p = Flags::from(self.stack_pop());
                self.pc = u16::from_be_bytes([self.stack_pop(), self.stack_pop()]);
            }
            Op::RTS => {
                self.pc = u16::from_be_bytes([self.stack_pop(), self.stack_pop()]);
            }
            Op::SBC(x) => {
                let borrow = !self.p[Flag::Carry];
                let (unsigned_result, has_borrowed) = self.a.borrowing_sub(x, borrow);
                let (signed_result, has_underflowed) =
                    (self.a as i8).borrowing_sub(x as i8, borrow);
                self.a = unsigned_result;
                self.p[Flag::Negative] = signed_result < 0;
                self.p[Flag::Overflow] = has_underflowed;
                self.p[Flag::Zero] = unsigned_result == 0;
                self.p[Flag::Carry] = !has_borrowed;
            }
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
    use pretty_assertions::assert_eq;

    #[derive(Debug, PartialEq)]
    struct TestBus {
        memory: [u8; 4],
    }

    impl TestBus {
        pub fn new() -> Self {
            Self { memory: [0; 4] }
        }
    }

    impl Bus for TestBus {
        fn read(&self, addr: u16) -> u8 {
            self.memory[(addr as usize) % self.memory.len()]
        }

        fn write(&mut self, addr: u16, byte: u8) {
            self.memory[(addr as usize) % self.memory.len()] = byte;
        }
    }

    #[test]
    fn flags_to_u8() {
        let (mut result, mut expected);

        expected = 0b00100000;
        result = u8::from(Flags([false; 7]));
        assert_eq!(
            result, expected,
            "Result {:b}, Expected {:b}",
            result, expected
        );

        expected = 0b11111111;
        result = u8::from(Flags([true; 7]));
        assert_eq!(
            result, expected,
            "Result {:b}, Expected {:b}",
            result, expected
        );

        expected = 0b10111001;
        result = u8::from(Flags([true, false, true, true, false, false, true]));
        assert_eq!(
            result, expected,
            "Result {:b}, Expected {:b}",
            result, expected
        );
    }

    #[test]
    fn u8_to_flags() {
        let (mut result, mut expected);

        expected = Flags([false; 7]);
        result = Flags::from(0b00100000);
        assert_eq!(result, expected);

        expected = Flags([true; 7]);
        result = Flags::from(0b11111111);
        assert_eq!(result, expected);

        expected = Flags([false, true, true, true, false, true, false]);
        result = Flags::from(0b01111010);
        assert_eq!(result, expected);
    }

    #[test]
    fn stack_push() {
        // typical case
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let (x0, x1) = (0x55, 0xf2);
        cpu.stack_push(x0);
        cpu.stack_push(x1);
        expected.s = 0xfd;
        expected.bus.memory = [0, 0, x1, x0];
        assert_eq!(cpu, expected, "typical case");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "typical case - memory");

        // stack pointer overflow
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.stack_pop();
        expected.s = 0;
        assert_eq!(cpu, expected);

        // stack pointer underflow
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        let x = 0x23;
        cpu.s = 0;
        cpu.stack_push(x);
        expected.s = 0xff;
        expected.bus.memory = [x, 0, 0, 0];
        assert_eq!(cpu, expected);
        assert_eq!(cpu.bus.memory, expected.bus.memory);
    }

    #[test]
    fn op_adc() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // no carry bit
        x = 0x8;
        cpu.a = 0x23;
        expected.a = x + cpu.a;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "no carry bit");

        // with carry bit
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.p[Flag::Carry] = true;
        x = 0x12;
        cpu.a = 0x15;
        expected.a = x + cpu.a + 1;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "with carry bit");

        // unsigned overflow
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0x5;
        cpu.a = 0xff;
        expected.a = x.wrapping_add(cpu.a);
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "unsigned overflow");

        // non overflowing with carry set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0x5;
        cpu.a = 0x54;
        expected.a = x + cpu.a + 1;
        cpu.p[Flag::Carry] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "non overflowing with carry set");

        // signed overflow
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 1;
        cpu.a = 127;
        expected.a = x + cpu.a;
        expected.p[Flag::Overflow] = true;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "signed overflow");

        // signed non overflow with overflow set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 1;
        cpu.a = 126;
        expected.a = x + cpu.a;
        cpu.p[Flag::Overflow] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "signed non overflow with overflow set");

        // negative result
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 5;
        cpu.a = 10u8.wrapping_neg();
        expected.a = x + cpu.a;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "negative result");

        // positive result with negative flag set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 12;
        cpu.a = 10u8.wrapping_neg();
        expected.a = x.wrapping_add(cpu.a);
        expected.p[Flag::Carry] = true;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "positive result with negative flag set");

        // zero result
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 10;
        cpu.a = 10u8.wrapping_neg();
        expected.a = x.wrapping_add(cpu.a);
        expected.p[Flag::Zero] = true;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "zero result");

        // non zero result with zero flag set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 12;
        cpu.a = 6;
        expected.a = x + cpu.a;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "non zero result with zero flag set");
    }

    #[test]
    fn op_and() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // typical
        x = 0b00110101;
        cpu.a = 0b11010011;
        expected.a = 0b00010001;
        cpu.execute(Op::AND(x));
        assert_eq!(cpu, expected, "typical");

        // zero result
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0b01010101;
        cpu.a = 0b10101010;
        expected.a = 0;
        expected.p[Flag::Zero] = true;
        cpu.execute(Op::AND(x));
        assert_eq!(cpu, expected, "zero result");

        // non zero result with zero flag set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0b01010101;
        cpu.a = 0b10111010;
        cpu.p[Flag::Zero] = true;
        expected.a = 0b00010000;
        expected.p[Flag::Zero] = false;
        cpu.execute(Op::AND(x));
        assert_eq!(cpu, expected, "non zero result with zero flag set");

        // negative result
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0b11010101;
        cpu.a = 0b10101010;
        expected.a = 0b10000000;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::AND(x));
        assert_eq!(cpu, expected, "negative result");

        // non negative result with negative flag set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0b01010101;
        cpu.a = 0b10111010;
        cpu.p[Flag::Negative] = true;
        expected.a = 0b00010000;
        expected.p[Flag::Negative] = false;
        cpu.execute(Op::AND(x));
        assert_eq!(cpu, expected, "non negative result with negative flag set");
    }

    #[test]
    fn op_asl() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());

        // typical
        cpu.a = 0b00000010;
        expected.a = 0b00000100;
        cpu.execute(Op::ASL(Address::Accumulator));
        assert_eq!(cpu, expected, "typical");

        // bit seven set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b10001000;
        expected.a = 0b00010000;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::ASL(Address::Accumulator));
        assert_eq!(cpu, expected, "bit seven set");

        // bit seven clear with carry flag set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b00001111;
        cpu.p[Flag::Carry] = true;
        expected.a = 0b00011110;
        expected.p[Flag::Carry] = false;
        cpu.execute(Op::ASL(Address::Accumulator));
        assert_eq!(cpu, expected, "bit seven clear with carry flag set");

        // zero result
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0;
        expected.a = 0;
        expected.p[Flag::Zero] = true;
        cpu.execute(Op::ASL(Address::Accumulator));
        assert_eq!(cpu, expected, "zero result");

        // non zero result with zero flag set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b00001111;
        cpu.p[Flag::Zero] = true;
        expected.a = 0b00011110;
        expected.p[Flag::Zero] = false;
        cpu.execute(Op::ASL(Address::Accumulator));
        assert_eq!(cpu, expected, "non zero result with zero flag set");

        // negative result
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b01000001;
        expected.a = 0b10000010;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::ASL(Address::Accumulator));
        assert_eq!(cpu, expected, "negative result");

        // non negative result with negative flag set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b00001111;
        cpu.p[Flag::Negative] = true;
        expected.a = 0b00011110;
        expected.p[Flag::Negative] = false;
        cpu.execute(Op::ASL(Address::Accumulator));
        assert_eq!(cpu, expected, "non negative result with negative flag set");
    }

    #[test]
    fn op_bcc() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // carry cleared
        x = 0x1123;
        cpu.p[Flag::Carry] = false;
        expected.pc = cpu.pc + x;
        cpu.execute(Op::BCC(x));
        assert_eq!(cpu, expected, "carry cleared");

        // carry set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0x2232;
        cpu.p[Flag::Carry] = true;
        expected.pc = cpu.pc;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::BCC(x));
        assert_eq!(cpu, expected, "carry set");
    }

    #[test]
    fn op_bcs() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // carry set
        x = 0x1189;
        expected.pc = cpu.pc + x;
        cpu.p[Flag::Carry] = true;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::BCS(x));
        assert_eq!(cpu, expected, "carry set");

        // carry cleared
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0x2211;
        expected.pc = cpu.pc;
        cpu.p[Flag::Carry] = false;
        expected.p[Flag::Carry] = false;
        cpu.execute(Op::BCS(x));
        assert_eq!(cpu, expected, "carry cleared");
    }

    #[test]
    fn op_beq() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // zero flag set
        x = 0x3102;
        expected.pc = cpu.pc + x;
        cpu.p[Flag::Zero] = true;
        expected.p[Flag::Zero] = true;
        cpu.execute(Op::BEQ(x));
        assert_eq!(cpu, expected, "zero flag set");

        // zero flag cleared
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0x1111;
        expected.pc = cpu.pc;
        cpu.p[Flag::Zero] = false;
        cpu.execute(Op::BEQ(x));
        assert_eq!(cpu, expected, "zero flag cleared");
    }

    #[test]
    fn op_bit() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // zero result
        cpu.a = 0b11001100;
        x = 0b00110011;
        expected.a = cpu.a;
        expected.p[Flag::Zero] = true;
        cpu.execute(Op::BIT(x));
        assert_eq!(cpu, expected, "zero result");

        // non-zero result
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b11011100;
        x = 0b00111111;
        expected.a = cpu.a;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::BIT(x));
        assert_eq!(cpu, expected, "non-zero result");

        // bit seven set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b01010000;
        x = 0b10110011;
        cpu.p[Flag::Negative] = false;
        expected.a = cpu.a;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::BIT(x));
        assert_eq!(cpu, expected, "bit seven set");

        // bit seven clear
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b11011100;
        x = 0b00111111;
        cpu.p[Flag::Negative] = true;
        expected.a = cpu.a;
        cpu.execute(Op::BIT(x));
        assert_eq!(cpu, expected, "bit seven clear");

        // bit six set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b01010000;
        x = 0b01010011;
        cpu.p[Flag::Overflow] = false;
        expected.a = cpu.a;
        expected.p[Flag::Overflow] = true;
        cpu.execute(Op::BIT(x));
        assert_eq!(cpu, expected, "bit six set");

        // bit six clear
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b11011100;
        x = 0b00111111;
        cpu.p[Flag::Overflow] = true;
        expected.a = cpu.a;
        cpu.execute(Op::BIT(x));
        assert_eq!(cpu, expected, "bit six clear");
    }

    #[test]
    fn op_bmi() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // negative flag set
        x = 0x3456;
        expected.pc = cpu.pc + x;
        expected.p[Flag::Negative] = true;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::BMI(x));
        assert_eq!(cpu, expected, "negative flag set");

        // negative flag clear
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0x2238;
        expected.pc = cpu.pc;
        cpu.p[Flag::Negative] = false;
        cpu.execute(Op::BMI(x));
        assert_eq!(cpu, expected, "negative flag clear");
    }

    #[test]
    fn op_bne() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // zero flag clear
        x = 0x1234;
        expected.pc = cpu.pc + x;
        cpu.p[Flag::Zero] = false;
        cpu.execute(Op::BNE(x));
        assert_eq!(cpu, expected, "zero flag clear");

        // zero flag set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0x1111;
        expected.pc = cpu.pc;
        cpu.p[Flag::Zero] = true;
        expected.p[Flag::Zero] = true;
        cpu.execute(Op::BNE(x));
        assert_eq!(cpu, expected, "zero flag set");
    }

    #[test]
    fn op_bpl() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // negative flag clear
        x = 0x0532;
        expected.pc = cpu.pc + x;
        cpu.p[Flag::Negative] = false;
        cpu.execute(Op::BPL(x));
        assert_eq!(cpu, expected, "negative flag clear");

        // negative flag set
        cpu.reset();
        x = 0x2222;
        expected.pc = cpu.pc;
        cpu.p[Flag::Negative] = true;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::BPL(x));
        assert_eq!(cpu, expected, "negative flag set");
    }

    #[test]
    fn op_brk() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());

        cpu.pc = 0x2345;
        cpu.p = Flags([false, false, true, true, false, true, false]);
        cpu.execute(Op::BRK);
        expected.pc = 0xfffe;
        expected.p = cpu.p;
        expected.p[Flag::Break] = true;
        expected.s = 0xfc;
        expected.bus.memory = [0, 0b00111010, 0x23, 0x45];
        assert_eq!(cpu, expected, "state");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory");
    }

    #[test]
    fn op_bvc() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // overflow clear
        x = 0x5555;
        expected.pc = cpu.pc + x;
        cpu.p[Flag::Overflow] = false;
        cpu.execute(Op::BVC(x));
        assert_eq!(cpu, expected, "overflow clear");

        // overflow set
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0x1234;
        expected.pc = cpu.pc;
        cpu.p[Flag::Overflow] = true;
        expected.p[Flag::Overflow] = true;
        cpu.execute(Op::BVC(x));
        assert_eq!(cpu, expected, "overflow set");
    }

    #[test]
    fn op_bvs() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // overflow set
        x = 0x1155;
        expected.pc = cpu.pc + x;
        cpu.p[Flag::Overflow] = true;
        expected.p[Flag::Overflow] = true;
        cpu.execute(Op::BVS(x));
        assert_eq!(cpu, expected, "overflow set");

        // overflow clear
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        x = 0x1122;
        expected.pc = cpu.pc;
        cpu.p[Flag::Overflow] = false;
        cpu.execute(Op::BVS(x));
        assert_eq!(cpu, expected, "overflow clear");
    }

    #[test]
    fn op_clc() {
        let mut cpu = Cpu::new(TestBus::new());
        let expected = Cpu::new(TestBus::new());

        cpu.p[Flag::Carry] = true;
        cpu.execute(Op::CLC);
        assert_eq!(cpu, expected, "state");
    }

    #[test]
    fn op_cld() {
        let mut cpu = Cpu::new(TestBus::new());
        let expected = Cpu::new(TestBus::new());

        cpu.p[Flag::Decimal] = true;
        cpu.execute(Op::CLD);
        assert_eq!(cpu, expected, "state");
    }

    #[test]
    fn op_cli() {
        let mut cpu = Cpu::new(TestBus::new());
        let expected = Cpu::new(TestBus::new());

        cpu.p[Flag::InterruptDisable] = true;
        cpu.execute(Op::CLI);
        assert_eq!(cpu, expected, "state");
    }

    #[test]
    fn op_clv() {
        let mut cpu = Cpu::new(TestBus::new());
        let expected = Cpu::new(TestBus::new());

        cpu.p[Flag::Overflow] = true;
        cpu.execute(Op::CLV);
        assert_eq!(cpu, expected, "state");
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

    // #[test]
    // fn op_dec() {
    //     let mut cpu = Cpu::new(TestBus::new());
    //     let (mut x, mut result, mut expected);
    //
    //     // value correct
    //     cpu.reset();
    //     x = 0x43;
    //     expected = x - 1;
    //     cpu.execute(Op::DEC(&mut x));
    //     result = x;
    //     assert!(
    //         result == expected,
    //         "Value incorrect. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // zero flag set correctly
    //     cpu.reset();
    //     x = 0x1;
    //     expected = true as u8;
    //     cpu.execute(Op::DEC(&mut x));
    //     result = cpu.p[Flag::Zero] as u8;
    //     assert!(
    //         result == expected,
    //         "Zero flag not set correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // zero flag cleared correctly
    //     cpu.reset();
    //     x = 0x5;
    //     expected = false as u8;
    //     cpu.p[Flag::Zero] = true;
    //     cpu.execute(Op::DEC(&mut x));
    //     result = cpu.p[Flag::Zero] as u8;
    //     assert!(
    //         result == expected,
    //         "Zero flag not cleared correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // negative flag set correctly
    //     cpu.reset();
    //     x = 0;
    //     expected = true as u8;
    //     cpu.execute(Op::DEC(&mut x));
    //     result = cpu.p[Flag::Negative] as u8;
    //     assert!(
    //         result == expected,
    //         "Negative flag not set correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // negative flag cleared correctly
    //     cpu.reset();
    //     x = 0x32;
    //     expected = false as u8;
    //     cpu.p[Flag::Negative] = true;
    //     cpu.execute(Op::DEC(&mut x));
    //     result = cpu.p[Flag::Negative] as u8;
    //     assert!(
    //         result == expected,
    //         "Negative flag not cleared correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    // }

    #[test]
    fn op_dex() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut result, mut expected);

        // value correct
        cpu.reset();
        cpu.x = 0x23;
        expected = cpu.x - 1;
        cpu.execute(Op::DEX);
        result = cpu.x;
        assert!(
            result == expected,
            "Value incorrect. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag set correctly
        cpu.reset();
        cpu.x = 1;
        expected = true as u8;
        cpu.execute(Op::DEX);
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag cleared correctly
        cpu.reset();
        cpu.x = 0x12;
        expected = false as u8;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::DEX);
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag set correctly
        cpu.reset();
        expected = true as u8;
        cpu.x = 0;
        cpu.execute(Op::DEX);
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag cleared correctly
        cpu.reset();
        cpu.x = 0x52;
        expected = false as u8;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::DEX);
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_dey() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut result, mut expected);

        // value correct
        cpu.reset();
        cpu.y = 0x23;
        expected = cpu.y - 1;
        cpu.execute(Op::DEY);
        result = cpu.y;
        assert!(
            result == expected,
            "Value incorrect. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag set correctly
        cpu.reset();
        cpu.y = 1;
        expected = true as u8;
        cpu.execute(Op::DEY);
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag cleared correctly
        cpu.reset();
        cpu.y = 0x12;
        expected = false as u8;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::DEY);
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag set correctly
        cpu.reset();
        expected = true as u8;
        cpu.y = 0;
        cpu.execute(Op::DEY);
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag cleared correctly
        cpu.reset();
        cpu.y = 0x52;
        expected = false as u8;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::DEY);
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_eor() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // correct value
        cpu.reset();
        x = 0b11011010;
        cpu.a = 0b01011101;
        expected = 0b10000111;
        cpu.execute(Op::EOR(x));
        result = cpu.a;
        assert!(
            result == expected,
            "Incorrect value in A. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag set correctly
        cpu.reset();
        x = 0b10101010;
        cpu.a = 0b10101010;
        expected = true as u8;
        cpu.p[Flag::Zero] = false;
        cpu.execute(Op::EOR(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag cleared correctly
        cpu.reset();
        x = 0b10101010;
        cpu.a = 0b11111111;
        expected = false as u8;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::EOR(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag set correctly
        cpu.reset();
        x = 0b10101010;
        cpu.a = 0b00101010;
        expected = true as u8;
        cpu.p[Flag::Negative] = false;
        cpu.execute(Op::EOR(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag cleared correctly
        cpu.reset();
        x = 0b10101010;
        cpu.a = 0b11111111;
        expected = false as u8;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::EOR(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );
    }

    // #[test]
    // fn op_inc() {
    //     let mut cpu = Cpu::new(TestBus::new());
    //     let (mut x, mut result, mut expected);
    //
    //     // value correct
    //     cpu.reset();
    //     x = 0x43;
    //     expected = x + 1;
    //     cpu.execute(Op::INC(&mut x));
    //     result = x;
    //     assert!(
    //         result == expected,
    //         "Value incorrect. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // zero flag set correctly
    //     cpu.reset();
    //     x = 0xff;
    //     expected = true as u8;
    //     cpu.execute(Op::INC(&mut x));
    //     result = cpu.p[Flag::Zero] as u8;
    //     assert!(
    //         result == expected,
    //         "Zero flag not set correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // zero flag cleared correctly
    //     cpu.reset();
    //     x = 0x5;
    //     expected = false as u8;
    //     cpu.p[Flag::Zero] = true;
    //     cpu.execute(Op::INC(&mut x));
    //     result = cpu.p[Flag::Zero] as u8;
    //     assert!(
    //         result == expected,
    //         "Zero flag not cleared correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // negative flag set correctly
    //     cpu.reset();
    //     x = 0xfa;
    //     expected = true as u8;
    //     cpu.execute(Op::INC(&mut x));
    //     result = cpu.p[Flag::Negative] as u8;
    //     assert!(
    //         result == expected,
    //         "Negative flag not set correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // negative flag cleared correctly
    //     cpu.reset();
    //     x = 0x32;
    //     expected = false as u8;
    //     cpu.p[Flag::Negative] = true;
    //     cpu.execute(Op::INC(&mut x));
    //     result = cpu.p[Flag::Negative] as u8;
    //     assert!(
    //         result == expected,
    //         "Negative flag not cleared correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    // }

    #[test]
    fn op_inx() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut result, mut expected);

        // value correct
        cpu.reset();
        cpu.x = 0x23;
        expected = cpu.x + 1;
        cpu.execute(Op::INX);
        result = cpu.x;
        assert!(
            result == expected,
            "Value incorrect. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag set correctly
        cpu.reset();
        cpu.x = 0xff;
        expected = true as u8;
        cpu.execute(Op::INX);
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag cleared correctly
        cpu.reset();
        cpu.x = 0x12;
        expected = false as u8;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::INX);
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag set correctly
        cpu.reset();
        expected = true as u8;
        cpu.x = 0xa2;
        cpu.execute(Op::INX);
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag cleared correctly
        cpu.reset();
        cpu.x = 0x52;
        expected = false as u8;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::INX);
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_iny() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut result, mut expected);

        // value correct
        cpu.reset();
        cpu.y = 0x23;
        expected = cpu.y + 1;
        cpu.execute(Op::INY);
        result = cpu.y;
        assert!(
            result == expected,
            "Value incorrect. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag set correctly
        cpu.reset();
        cpu.y = 0xff;
        expected = true as u8;
        cpu.execute(Op::INY);
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag cleared correctly
        cpu.reset();
        cpu.y = 0x12;
        expected = false as u8;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::INY);
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag set correctly
        cpu.reset();
        expected = true as u8;
        cpu.y = 0xf1;
        cpu.execute(Op::INY);
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag cleared correctly
        cpu.reset();
        cpu.y = 0x52;
        expected = false as u8;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::INY);
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_jmp() {
        let mut cpu = Cpu::new(TestBus::new());
        let (addr, result, expected);

        // correct value
        cpu.reset();
        addr = 0x3245;
        cpu.pc = 0x1234;
        expected = addr;
        cpu.execute(Op::JMP(addr));
        result = cpu.pc;
        assert!(
            result == expected,
            "Incorrect PC value. Result {}, Expected {}",
            result,
            expected
        );
    }

    // #[test]
    // fn op_jsr() {
    //     let mut cpu = Cpu::new(TestBus::new());
    //     let (mut addr, mut result, mut expected);
    //
    //     // stack contains correct values
    //     cpu.reset();
    //     addr = 0xa2a1;
    //     cpu.pc = 0x526a;
    //     cpu.execute(Op::JSR(addr));
    //     expected = 0x6a;
    //     result = cpu.stack[0xff];
    //     assert!(
    //         result == expected,
    //         "First byte incorrect. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //     expected = 0x52;
    //     result = cpu.stack[0xfe];
    //     assert!(
    //         result == expected,
    //         "Second byte incorrect. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // pc value changed correctly
    //     cpu.reset();
    //     cpu.pc = 0x1234;
    //     addr = 0x5278;
    //     let expected = addr;
    //     cpu.execute(Op::JSR(addr));
    //     let result = cpu.pc;
    //     assert!(
    //         result == expected,
    //         "PC value incorrect. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    // }

    #[test]
    fn op_lda() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // loads correctly
        cpu.reset();
        cpu.a = 0x52;
        x = 0x11;
        expected = x;
        cpu.execute(Op::LDA(x));
        result = cpu.a;
        assert!(
            result == expected,
            "Incorrect value in A. Result {}, Expected {}",
            result,
            expected
        );

        // sets zero flag correctly
        cpu.reset();
        x = 0;
        cpu.p[Flag::Zero] = false;
        expected = true as u8;
        cpu.execute(Op::LDA(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears zero flag correctly
        cpu.reset();
        x = 5;
        cpu.p[Flag::Zero] = true;
        expected = false as u8;
        cpu.execute(Op::LDA(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // sets negative flag correctly
        cpu.reset();
        x = 0xff;
        cpu.p[Flag::Negative] = false;
        expected = true as u8;
        cpu.execute(Op::LDA(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears negative flag correctly
        cpu.reset();
        x = 5;
        cpu.p[Flag::Negative] = true;
        expected = false as u8;
        cpu.execute(Op::LDA(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_ldx() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // loads correctly
        cpu.reset();
        cpu.x = 0xde;
        x = 0x01;
        expected = x;
        cpu.execute(Op::LDX(x));
        result = cpu.x;
        assert!(
            result == expected,
            "Incorrect value in X. Result {}, Expected {}",
            result,
            expected
        );

        // sets zero flag correctly
        cpu.reset();
        x = 0;
        cpu.p[Flag::Zero] = false;
        expected = true as u8;
        cpu.execute(Op::LDX(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears zero flag correctly
        cpu.reset();
        x = 11;
        cpu.p[Flag::Zero] = true;
        expected = false as u8;
        cpu.execute(Op::LDX(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // sets negative flag correctly
        cpu.reset();
        x = 0xf1;
        cpu.p[Flag::Negative] = false;
        expected = true as u8;
        cpu.execute(Op::LDX(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears negative flag correctly
        cpu.reset();
        x = 55;
        cpu.p[Flag::Negative] = true;
        expected = false as u8;
        cpu.execute(Op::LDX(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_ldy() {
        let mut cpu = Cpu::new(TestBus::new());
        let (mut x, mut result, mut expected);

        // loads correctly
        cpu.reset();
        cpu.y = 0x2e;
        x = 0x08;
        expected = x;
        cpu.execute(Op::LDY(x));
        result = cpu.y;
        assert!(
            result == expected,
            "Incorrect value in Y. Result {}, Expected {}",
            result,
            expected
        );

        // sets zero flag correctly
        cpu.reset();
        x = 0;
        cpu.p[Flag::Zero] = false;
        expected = true as u8;
        cpu.execute(Op::LDY(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag set incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears zero flag correctly
        cpu.reset();
        x = 32;
        cpu.p[Flag::Zero] = true;
        expected = false as u8;
        cpu.execute(Op::LDY(x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // sets negative flag correctly
        cpu.reset();
        x = 0xe2;
        cpu.p[Flag::Negative] = false;
        expected = true as u8;
        cpu.execute(Op::LDY(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );

        // clears negative flag correctly
        cpu.reset();
        x = 89;
        cpu.p[Flag::Negative] = true;
        expected = false as u8;
        cpu.execute(Op::LDY(x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Zero flag cleared incorrectly. Result {}, Expected {}",
            result,
            expected
        );
    }

    // #[test]
    // fn op_lsr() {
    //     let mut cpu = Cpu::new(TestBus::new());
    //     let (mut x, mut result, mut expected);
    //
    //     // correct value
    //     cpu.reset();
    //     x = 0b10101010;
    //     expected = 0b01010101;
    //     cpu.execute(Op::LSR(&mut x));
    //     result = x;
    //     assert!(
    //         result == expected,
    //         "Incorrect value from bitshifting. Result {:b}, Expected {:b}",
    //         result,
    //         expected
    //     );
    //
    //     // sets carry flag
    //     cpu.reset();
    //     x = 0b00000001;
    //     expected = true as u8;
    //     cpu.execute(Op::LSR(&mut x));
    //     result = cpu.p[Flag::Carry] as u8;
    //     assert!(
    //         result == expected,
    //         "Carry not set correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // clears carry flag
    //     cpu.reset();
    //     x = 0b00110010;
    //     expected = false as u8;
    //     cpu.p[Flag::Carry] = true;
    //     cpu.execute(Op::LSR(&mut x));
    //     result = cpu.p[Flag::Carry] as u8;
    //     assert!(
    //         result == expected,
    //         "Carry not cleared correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // sets zero flag
    //     cpu.reset();
    //     x = 0b00000001;
    //     expected = true as u8;
    //     cpu.execute(Op::LSR(&mut x));
    //     result = cpu.p[Flag::Zero] as u8;
    //     assert!(
    //         result == expected,
    //         "Zero flag not set correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // clears zero flag
    //     cpu.reset();
    //     x = 0b10111010;
    //     expected = false as u8;
    //     cpu.p[Flag::Zero] = true;
    //     cpu.execute(Op::LSR(&mut x));
    //     result = cpu.p[Flag::Zero] as u8;
    //     assert!(
    //         result == expected,
    //         "Zero flag not cleared correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    //
    //     // clears negative flag
    //     cpu.reset();
    //     x = 0b10111110;
    //     expected = false as u8;
    //     cpu.p[Flag::Negative] = true;
    //     cpu.execute(Op::LSR(&mut x));
    //     result = cpu.p[Flag::Negative] as u8;
    //     assert!(
    //         result == expected,
    //         "Negative flag not cleared correctly. Result {}, Expected {}",
    //         result,
    //         expected
    //     );
    // }

    #[test]
    fn op_nop() {
        let mut cpu = Cpu::new(TestBus::new());
        let expected = Cpu::new(TestBus::new());
        cpu.execute(Op::NOP);
        assert_eq!(cpu, expected, "state");
    }

    #[test]
    fn op_ora() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // typical
        cpu.a = 0b00110111;
        x = 0b01000100;
        expected.a = 0b01110111;
        cpu.execute(Op::ORA(x));
        assert_eq!(cpu, expected, "typical");

        // negative
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b10101010;
        x = 0b10101010;
        expected.a = 0b10101010;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::ORA(x));
        assert_eq!(cpu, expected, "negative");

        // zero
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0;
        x = 0;
        expected.a = 0;
        expected.p[Flag::Zero] = true;
        cpu.execute(Op::ORA(x));
        assert_eq!(cpu, expected, "zero");
    }

    #[test]
    fn op_pha() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());

        cpu.a = 0xae;
        cpu.execute(Op::PHA);
        cpu.a = 0x23;
        cpu.execute(Op::PHA);
        expected.a = cpu.a;
        expected.s = 0xfd;
        expected.bus.memory = [0, 0, 0x23, 0xae];
        assert_eq!(cpu, expected, "state");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory");
    }

    #[test]
    fn op_php() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());

        cpu.p = Flags([false, true, true, true, false, true, true]);
        cpu.execute(Op::PHP);
        cpu.p = Flags([false, false, false, false, true, false, true]);
        cpu.execute(Op::PHP);
        cpu.p = Flags([false, true, false, false, true, false, true]);
        cpu.execute(Op::PHP);
        expected.p = cpu.p;
        expected.s = 0xfc;
        expected.bus.memory = [0, 0b01100101, 0b00100101, 0b01111011];
        assert_eq!(cpu, expected, "state");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory");
    }

    #[test]
    fn op_pla() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());

        cpu.s = 0xfc;
        cpu.bus.memory = [0, 0, 0x3a, 0xab];
        cpu.execute(Op::PLA);
        expected.s = 0xfd;
        expected.a = 0;
        expected.p[Flag::Zero] = true;
        expected.bus.memory = [0, 0, 0x3a, 0xab];
        assert_eq!(cpu, expected, "state 0");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory 0");
        cpu.execute(Op::PLA);
        expected.s = 0xfe;
        expected.a = 0x3a;
        expected.p[Flag::Zero] = false;
        expected.bus.memory = [0, 0, 0x3a, 0xab];
        assert_eq!(cpu, expected, "state 1");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory 1");
        cpu.execute(Op::PLA);
        expected.s = 0xff;
        expected.a = 0xab;
        expected.p[Flag::Negative] = true;
        expected.bus.memory = [0, 0, 0x3a, 0xab];
        assert_eq!(cpu, expected, "state 2");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory 2");
    }

    #[test]
    fn op_plp() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());

        cpu.s = 0xfd;
        cpu.bus.memory = [0, 0, 0b11100000, 0b01101100];
        cpu.execute(Op::PLP);
        expected.s = 0xfe;
        expected.p = Flags([true, true, false, false, false, false, false]);
        assert_eq!(cpu, expected, "state 0");
        cpu.execute(Op::PLP);
        expected.s = 0xff;
        expected.p = Flags([false, true, false, true, true, false, false]);
        assert_eq!(cpu, expected, "state 1");
    }

    #[test]
    fn op_rol() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());

        cpu.bus.memory[1] = 0b11101110;
        expected.bus.memory[1] = 0b11011100;
        expected.p[Flag::Carry] = true;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::ROL(Address::Memory(1)));
        assert_eq!(cpu, expected, "state 0");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory 0");

        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.p[Flag::Carry] = true;
        cpu.bus.memory[2] = 0b00011000;
        expected.bus.memory[2] = 0b00110001;
        cpu.execute(Op::ROL(Address::Memory(2)));
        assert_eq!(cpu, expected, "state 1");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory 1");

        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b10000000;
        expected.a = 0;
        expected.p[Flag::Zero] = true;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::ROL(Address::Accumulator));
        assert_eq!(cpu, expected, "state 2");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory 2");
    }

    #[test]
    fn op_ror() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());

        cpu.bus.memory[1] = 0b11101110;
        expected.bus.memory[1] = 0b01110111;
        cpu.execute(Op::ROR(Address::Memory(1)));
        assert_eq!(cpu, expected, "state 0");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory 0");

        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.p[Flag::Carry] = true;
        cpu.bus.memory[2] = 0b00011000;
        expected.bus.memory[2] = 0b10001100;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::ROR(Address::Memory(2)));
        assert_eq!(cpu, expected, "state 1");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory 1");

        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0b00000001;
        expected.a = 0;
        expected.p[Flag::Zero] = true;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::ROR(Address::Accumulator));
        assert_eq!(cpu, expected, "state 2");
        assert_eq!(cpu.bus.memory, expected.bus.memory, "memory 2");
    }

    #[test]
    fn op_rti() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());

        cpu.s = 0xfc;
        cpu.bus.memory = [0, 0b01101100, 0x32, 0x1f];
        cpu.execute(Op::RTI);
        expected.pc = 0x321f;
        expected.p = Flags([false, true, false, true, true, false, false]);
        assert_eq!(cpu, expected, "state");
    }

    #[test]
    fn op_rts() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());

        cpu.s = 0xfd;
        cpu.bus.memory = [0, 0, 0x12, 0x34];
        cpu.execute(Op::RTS);
        expected.pc = 0x1234;
        assert_eq!(cpu, expected, "state");
    }

    #[test]
    fn op_sbc() {
        let mut cpu = Cpu::new(TestBus::new());
        let mut expected = Cpu::new(TestBus::new());
        let mut x;

        // no carry bit
        x = 0x8;
        cpu.a = 0x23;
        expected.a = cpu.a - x - 1;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::SBC(x));
        assert_eq!(cpu, expected, "no carry bit");

        // with carry bit
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.p[Flag::Carry] = true;
        cpu.a = 0x15;
        x = 0x12;
        expected.a = cpu.a - x;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::SBC(x));
        assert_eq!(cpu, expected, "with carry bit");

        // unsigned underflow
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 0x5;
        x = 0xfe;
        expected.a = cpu.a.wrapping_sub(x + 1);
        cpu.execute(Op::SBC(x));
        assert_eq!(cpu, expected, "unsigned underflow");

        // signed underflow
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.p[Flag::Carry] = true;
        cpu.a = 127;
        x = 0xff;
        expected.a = cpu.a.wrapping_sub(x);
        expected.p[Flag::Overflow] = true;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::SBC(x));
        assert_eq!(cpu, expected, "signed underflow");

        // negative result
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 10u8.wrapping_neg();
        cpu.p[Flag::Carry] = true;
        x = 5;
        expected.a = cpu.a - x;
        expected.p[Flag::Negative] = true;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::SBC(x));
        assert_eq!(cpu, expected, "negative result");

        // zero result
        cpu = Cpu::new(TestBus::new());
        expected = Cpu::new(TestBus::new());
        cpu.a = 10;
        cpu.p[Flag::Carry] = true;
        x = 10;
        expected.a = 0;
        expected.p[Flag::Zero] = true;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::SBC(x));
        assert_eq!(cpu, expected, "zero result");
    }
}
