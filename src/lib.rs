use std::ops::{Index, IndexMut};

pub struct Bus {}

pub struct Cpu {
    pub pc: u16,
    pub a: u8,
    pub x: u8,
    pub y: u8,
    pub s: u8,
    pub p: [bool; 7],
}

enum Op {
    ADC(u8),
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
            s: 0,
            p: [false; 7], // N,V,B,D,I,Z,C
        }
    }

    pub fn reset(&mut self) {
        self.pc = 0;
        self.a = 0;
        self.x = 0;
        self.y = 0;
        self.s = 0;
        self.p = [false; 7];
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

            }
        }
    }
}

impl Index<Flag> for [bool; 7] {
    type Output = bool;

    fn index(&self, flag: Flag) -> &Self::Output {
        &self[flag as usize]
    }
}

impl IndexMut<Flag> for [bool; 7] {
    fn index_mut(&mut self, flag: Flag) -> &mut Self::Output {
        &mut self[flag as usize]
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn op_adc() {
        let mut cpu = Cpu::new();
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
}
