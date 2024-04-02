use std::ops::{Index, IndexMut};
use std::convert::From;

#[derive(Copy, Clone, PartialEq, Debug)]
pub struct Flags([bool; 7]);

pub struct Cpu {
    pub pc: u16,
    pub a: u8,
    pub x: u8,
    pub y: u8,
    pub s: u8,
    pub p: Flags,
    pub stack: [u8; 256],
}

enum Op<'a> {
    ADC(u8),
    AND(u8),
    ASL(&'a mut u8),
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
    DEC(&'a mut u8),
    DEX,
    DEY,
    EOR(u8),
    INC(&'a mut u8),
    INX,
    INY,
    JMP(u16),
    JSR(u16),
    LDA(u8),
    LDX(u8),
    LDY(u8),
    LSR(&'a mut u8),
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

impl Cpu {
    pub fn new() -> Self {
        Self {
            pc: 0,
            a: 0,
            x: 0,
            y: 0,
            s: 0xff,
            p: Flags([false; 7]), // N,V,B,D,I,Z,C
            stack: [0; 256],
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
                let byte = *addr;
                let bit_seven = (byte & 0b10000000) >> 7;
                let unsigned_result = byte << 1;
                let signed_result = unsigned_result as i8;
                *addr = unsigned_result;
                self.p[Flag::Carry] = bit_seven != 0;
                self.p[Flag::Zero] = unsigned_result == 0;
                self.p[Flag::Negative] = signed_result < 0;
            },
            Op::BCC(x) => {
                if !self.p[Flag::Carry] {
                    self.pc = self.pc.wrapping_add(x); }
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
            Op::BIT(x) => {
                let bit_seven = (x & 0b10000000) >> 7;
                let bit_six = (x & 0b01000000) >> 6;
                self.p[Flag::Zero] = (self.a & x) == 0;
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
                let result = (*addr).wrapping_sub(1);
                *addr = result;
                self.p[Flag::Zero] = result == 0;
                self.p[Flag::Negative] = (result as i8) < 0;
            },
            Op::DEX => {
                self.x = self.x.wrapping_sub(1);
                self.p[Flag::Zero] = self.x == 0;
                self.p[Flag::Negative] = (self.x as i8) < 0;
            },
            Op::DEY => {
                self.y = self.y.wrapping_sub(1);
                self.p[Flag::Zero] = self.y == 0;
                self.p[Flag::Negative] = (self.y as i8) < 0;
            },
            Op::EOR(x) => {
                self.a ^= x;
                self.p[Flag::Zero] = self.a == 0;
                self.p[Flag::Negative] = (self.a as i8) < 0;
            },
            Op::INC(addr) => {
                let result = (*addr).wrapping_add(1);
                *addr = result;
                self.p[Flag::Zero] = result == 0;
                self.p[Flag::Negative] = (result as i8) < 0;
            },
            Op::INX => {
                self.x = self.x.wrapping_add(1);
                self.p[Flag::Zero] = self.x == 0;
                self.p[Flag::Negative] = (self.x as i8) < 0;
            },
            Op::INY => {
                self.y = self.y.wrapping_add(1);
                self.p[Flag::Zero] = self.y == 0;
                self.p[Flag::Negative] = (self.y as i8) < 0;
            },
            Op::JMP(addr) => {
                self.pc = addr;
            },
            Op::JSR(addr) => {
                let pc = self.pc.to_le_bytes();
                self.stack_push(pc[0]);
                self.stack_push(pc[1]);
                self.pc = addr;
            },
            Op::LDA(x) => {
                self.a = x;
                self.p[Flag::Zero] = x == 0;
                self.p[Flag::Negative] = (x as i8) < 0;
            },
            Op::LDX(x) => {
                self.x = x;
                self.p[Flag::Zero] = x == 0;
                self.p[Flag::Negative] = (x as i8) < 0;
            },
            Op::LDY(x) => {
                self.y = x;
                self.p[Flag::Zero] = x == 0;
                self.p[Flag::Negative] = (x as i8) < 0;
            },
            Op::LSR(addr) => {
                let byte = *addr;
                let bit_zero = byte & 0b00000001;
                let result = byte >> 1;
                *addr = result;
                self.p[Flag::Carry] = bit_zero != 0;
                self.p[Flag::Zero] = result == 0;
                self.p[Flag::Negative] = false;
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
    use pretty_assertions::assert_eq;

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
        let mut cpu = Cpu::new();
        let mut expected = Cpu::new();
        let (x0, x1) = (0x55, 0xf2);
        cpu.stack_push(x0);
        cpu.stack_push(x1);
        expected.s = 0xfd;
        expected.stack[0xff] = x0;
        expected.stack[0xfe] = x1;
        assert_eq!(cpu, expected);

        // stack pointer overflow
        cpu = Cpu::new();
        expected = Cpu::new();
        cpu.stack_pop();
        expected.s = 0;
        assert_eq!(cpu, expected);

        // stack pointer underflow
        cpu = Cpu::new();
        expected = Cpu::new();
        let x = 0x23;
        cpu.s = 0;
        cpu.stack_push(x);
        expected.s = 0xff;
        expected.stack[0] = x;
        assert_eq!(cpu, expected);
    }

    #[test]
    fn op_adc() {
        let mut cpu = Cpu::new();
        let mut expected = Cpu::new();
        let mut x;

        // no carry bit
        x = 0x8;
        cpu.a = 0x23;
        expected.a = x + cpu.a;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "no carry bit");

        // with carry bit
        cpu = Cpu::new();
        expected = Cpu::new();
        cpu.p[Flag::Carry] = true;
        x = 0x12;
        cpu.a = 0x15;
        expected.a = x + cpu.a + 1;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "with carry bit");

        // unsigned overflow
        cpu = Cpu::new();
        expected = Cpu::new();
        x = 0x5;
        cpu.a = 0xff;
        expected.a = x.wrapping_add(cpu.a);
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "unsigned overflow");

        // non overflowing with carry set
        cpu = Cpu::new();
        expected = Cpu::new();
        x = 0x5;
        cpu.a = 0x54;
        expected.a = x + cpu.a + 1;
        cpu.p[Flag::Carry] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "non overflowing with carry set");

        // signed overflow
        cpu = Cpu::new();
        expected = Cpu::new();
        x = 1;
        cpu.a = 127;
        expected.a = x + cpu.a;
        expected.p[Flag::Overflow] = true;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "signed overflow");

        // signed non overflow with overflow set
        cpu = Cpu::new();
        expected = Cpu::new();
        x = 1;
        cpu.a = 126;
        expected.a = x + cpu.a;
        cpu.p[Flag::Overflow] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "signed non overflow with overflow set");

        // negative result
        cpu = Cpu::new();
        expected = Cpu::new();
        x = 5;
        cpu.a = 10u8.wrapping_neg();
        expected.a = x + cpu.a;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "negative result");

        // positive result with negative flag set
        cpu = Cpu::new();
        expected = Cpu::new();
        x = 12;
        cpu.a = 10u8.wrapping_neg();
        expected.a = x.wrapping_add(cpu.a);
        expected.p[Flag::Carry] = true;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "positive result with negative flag set");

        // zero result
        cpu = Cpu::new();
        expected = Cpu::new();
        x = 10;
        cpu.a = 10u8.wrapping_neg();
        expected.a = x.wrapping_add(cpu.a);
        expected.p[Flag::Zero] = true;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "zero result");

        // non zero result with zero flag set
        cpu = Cpu::new();
        expected = Cpu::new();
        x = 12;
        cpu.a = 6;
        expected.a = x + cpu.a;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::ADC(x));
        assert_eq!(cpu, expected, "non zero result with zero flag set");
    }

    #[test]
    fn op_and() {
        let mut cpu = Cpu::new();
        let mut expected = Cpu::new();
        let mut x;

        // typical
        x = 0b00110101;
        cpu.a = 0b11010011;
        expected.a = 0b00010001;
        cpu.execute(Op::AND(x));
        assert_eq!(cpu, expected, "typical");

        // zero result
        cpu = Cpu::new();
        expected = Cpu::new();
        x = 0b01010101;
        cpu.a = 0b10101010;
        expected.a = 0;
        expected.p[Flag::Zero] = true;
        cpu.execute(Op::AND(x));
        assert_eq!(cpu, expected, "zero result");

        // non zero result with zero flag set
        cpu = Cpu::new();
        expected = Cpu::new();
        x = 0b01010101;
        cpu.a = 0b10111010;
        cpu.p[Flag::Zero] = true;
        expected.a = 0b00010000;
        expected.p[Flag::Zero] = false;
        cpu.execute(Op::AND(x));
        assert_eq!(cpu, expected, "non zero result with zero flag set");

        // negative result
        cpu = Cpu::new();
        expected = Cpu::new();
        x = 0b11010101;
        cpu.a = 0b10101010;
        expected.a = 0b10000000;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::AND(x));
        assert_eq!(cpu, expected, "negative result");

        // non negative result with negative flag set
        cpu = Cpu::new();
        expected = Cpu::new();
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
        let mut cpu = Cpu::new();
        let mut expected = Cpu::new();

        // typical
        cpu.a = 0b00000010;
        expected.a = 0b00000100;
        cpu.execute(Op::ASL(&mut cpu.a));
        assert_eq!(cpu, expected, "typical");

        // bit seven set
        cpu = Cpu::new();
        expected = Cpu::new();
        cpu.a = 0b10001000;
        expected.a = 0b00010000;
        expected.p[Flag::Carry] = true;
        cpu.execute(Op::ASL(&mut cpu.a));
        assert_eq!(cpu, expected, "bit seven set");

        // bit seven clear with carry flag set
        cpu = Cpu::new();
        expected = Cpu::new();
        cpu.a = 0b00001111;
        cpu.p[Flag::Carry] = true;
        expected.a = 0b00011110;
        expected.p[Flag::Carry] = false;
        cpu.execute(Op::ASL(&mut cpu.a));
        assert_eq!(cpu, expected, "bit seven clear with carry flag set");

        // zero result
        cpu = Cpu::new();
        expected = Cpu::new();
        cpu.a = 0;
        expected.a = 0;
        expected.p[Flag::Carry] = true;
        expected.p[Flag::Zero] = true;
        cpu.execute(Op::ASL(&mut cpu.a));
        assert_eq!(cpu, expected, "zero result");

        // non zero result with zero flag set
        cpu = Cpu::new();
        expected = Cpu::new();
        cpu.a = 0b00001111;
        cpu.p[Flag::Zero] = true;
        expected.a = 0b00011110;
        expected.p[Flag::Zero] = false;
        cpu.execute(Op::ASL(&mut cpu.a));
        assert_eq!(cpu, expected, "non zero result with zero flag set");

        // negative result
        cpu = Cpu::new();
        expected = Cpu::new();
        cpu.a = 0b01000001;
        expected.a = 0b10000010;
        expected.p[Flag::Negative] = true;
        cpu.execute(Op::ASL(&mut cpu.a));
        assert_eq!(cpu, expected, "negative result");

        // non negative result with negative flag set
        cpu = Cpu::new();
        expected = Cpu::new();
        cpu.a = 0b00001111;
        cpu.p[Flag::Negative] = true;
        expected.a = 0b00011110;
        expected.p[Flag::Negative] = false;
        cpu.execute(Op::ASL(&mut cpu.a));
        assert_eq!(cpu, expected, "non negative result with negative flag set");
    }

    #[test]
    fn op_bcc() {
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
        let (mut x, mut result, mut expected);

        // sets zero flag correctly
        cpu.reset();
        cpu.a = 0b11001100;
        x = 0b00110011;
        cpu.p[Flag::Zero] = false;
        expected = true;
        cpu.execute(Op::BIT(x));
        result = cpu.p[Flag::Zero];
        assert!(
            result == expected,
            "Incorrect setting of zero flag. Expected {}, Result {}",
            result,
            expected
        );

        // clears zero flag correctly
        cpu.reset();
        cpu.a = 0b11011100;
        x = 0b00111111;
        cpu.p[Flag::Zero] = true;
        expected = false;
        cpu.execute(Op::BIT(x));
        result = cpu.p[Flag::Zero];
        assert!(
            result == expected,
            "Incorrect clearing of zero flag. Expected {}, Result {}",
            result,
            expected
        );

        // sets negative flag correctly
        cpu.reset();
        cpu.a = 0b01010000;
        x = 0b10110011;
        cpu.p[Flag::Negative] = false;
        expected = true;
        cpu.execute(Op::BIT(x));
        result = cpu.p[Flag::Negative];
        assert!(
            result == expected,
            "Incorrect setting of negative flag. Expected {}, Result {}",
            result,
            expected
        );

        // clears negative flag correctly
        cpu.reset();
        cpu.a = 0b11011100;
        x = 0b01111111;
        cpu.p[Flag::Negative] = true;
        expected = false;
        cpu.execute(Op::BIT(x));
        result = cpu.p[Flag::Negative];
        assert!(
            result == expected,
            "Incorrect clearing of negative flag. Expected {}, Result {}",
            result,
            expected
        );

        // sets overflow flag correctly
        cpu.reset();
        cpu.a = 0b01010000;
        x = 0b01010011;
        cpu.p[Flag::Overflow] = false;
        expected = true;
        cpu.execute(Op::BIT(x));
        result = cpu.p[Flag::Overflow];
        assert!(
            result == expected,
            "Incorrect setting of overflow flag. Expected {}, Result {}",
            result,
            expected
        );

        // clears overflow flag correctly
        cpu.reset();
        cpu.a = 0b11011100;
        x = 0b10111111;
        cpu.p[Flag::Overflow] = true;
        expected = false;
        cpu.execute(Op::BIT(x));
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();

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
        let mut cpu = Cpu::new();

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
        let mut cpu = Cpu::new();

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
        let mut cpu = Cpu::new();

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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
        let (mut x, mut result, mut expected);

        // value correct
        cpu.reset();
        x = 0x43;
        expected = x - 1;
        cpu.execute(Op::DEC(&mut x));
        result = x;
        assert!(
            result == expected,
            "Value incorrect. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag set correctly
        cpu.reset();
        x = 0x1;
        expected = true as u8;
        cpu.execute(Op::DEC(&mut x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag cleared correctly
        cpu.reset();
        x = 0x5;
        expected = false as u8;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::DEC(&mut x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag set correctly
        cpu.reset();
        x = 0;
        expected = true as u8;
        cpu.execute(Op::DEC(&mut x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag cleared correctly
        cpu.reset();
        x = 0x32;
        expected = false as u8;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::DEC(&mut x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_dex() {
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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

    #[test]
    fn op_inc() {
        let mut cpu = Cpu::new();
        let (mut x, mut result, mut expected);

        // value correct
        cpu.reset();
        x = 0x43;
        expected = x + 1;
        cpu.execute(Op::INC(&mut x));
        result = x;
        assert!(
            result == expected,
            "Value incorrect. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag set correctly
        cpu.reset();
        x = 0xff;
        expected = true as u8;
        cpu.execute(Op::INC(&mut x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // zero flag cleared correctly
        cpu.reset();
        x = 0x5;
        expected = false as u8;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::INC(&mut x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag set correctly
        cpu.reset();
        x = 0xfa;
        expected = true as u8;
        cpu.execute(Op::INC(&mut x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // negative flag cleared correctly
        cpu.reset();
        x = 0x32;
        expected = false as u8;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::INC(&mut x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_inx() {
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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

    #[test]
    fn op_jsr() {
        let mut cpu = Cpu::new();
        let (mut addr, mut result, mut expected);

        // stack contains correct values
        cpu.reset();
        addr = 0xa2a1;
        cpu.pc = 0x526a;
        cpu.execute(Op::JSR(addr));
        expected = 0x6a;
        result = cpu.stack[0xff];
        assert!(
            result == expected,
            "First byte incorrect. Result {}, Expected {}",
            result,
            expected
        );
        expected = 0x52;
        result = cpu.stack[0xfe];
        assert!(
            result == expected,
            "Second byte incorrect. Result {}, Expected {}",
            result,
            expected
        );

        // pc value changed correctly
        cpu.reset();
        cpu.pc = 0x1234;
        addr = 0x5278;
        let expected = addr;
        cpu.execute(Op::JSR(addr));
        let result = cpu.pc;
        assert!(
            result == expected,
            "PC value incorrect. Result {}, Expected {}",
            result,
            expected
        );
    }

    #[test]
    fn op_lda() {
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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
        let mut cpu = Cpu::new();
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

    #[test]
    fn op_lsr() {
        let mut cpu = Cpu::new();
        let (mut x, mut result, mut expected);

        // correct value
        cpu.reset();
        x = 0b10101010;
        expected = 0b01010101;
        cpu.execute(Op::LSR(&mut x));
        result = x;
        assert!(
            result == expected,
            "Incorrect value from bitshifting. Result {:b}, Expected {:b}",
            result,
            expected
        );

        // sets carry flag
        cpu.reset();
        x = 0b00000001;
        expected = true as u8;
        cpu.execute(Op::LSR(&mut x));
        result = cpu.p[Flag::Carry] as u8;
        assert!(
            result == expected,
            "Carry not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // clears carry flag
        cpu.reset();
        x = 0b00110010;
        expected = false as u8;
        cpu.p[Flag::Carry] = true;
        cpu.execute(Op::LSR(&mut x));
        result = cpu.p[Flag::Carry] as u8;
        assert!(
            result == expected,
            "Carry not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );

        // sets zero flag
        cpu.reset();
        x = 0b00000001;
        expected = true as u8;
        cpu.execute(Op::LSR(&mut x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not set correctly. Result {}, Expected {}",
            result,
            expected
        );

        // clears zero flag
        cpu.reset();
        x = 0b10111010;
        expected = false as u8;
        cpu.p[Flag::Zero] = true;
        cpu.execute(Op::LSR(&mut x));
        result = cpu.p[Flag::Zero] as u8;
        assert!(
            result == expected,
            "Zero flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );

        // clears negative flag
        cpu.reset();
        x = 0b10111110;
        expected = false as u8;
        cpu.p[Flag::Negative] = true;
        cpu.execute(Op::LSR(&mut x));
        result = cpu.p[Flag::Negative] as u8;
        assert!(
            result == expected,
            "Negative flag not cleared correctly. Result {}, Expected {}",
            result,
            expected
        );
    }
}
