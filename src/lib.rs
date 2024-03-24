use std::ops::{Index, IndexMut};

#[derive(Debug)]
pub struct BusReadError;

#[derive(Debug)]
pub struct BusWriteError;

pub trait Bus {
    fn read(&self, addr: u16) -> Result<u8, BusReadError>;
    fn write(&mut self, addr: u16, data: u8) -> Result<(), BusWriteError>;
}

pub struct Cpu<T: Bus> {
    pub pc: u16,
    pub a: u8,
    pub x: u8,
    pub y: u8,
    pub s: u8,
    pub p: [bool; 7],
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
            s: 0,
            p: [false; 7], // N,V,B,D,I,Z,C
            bus,
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
                    self.pc += x;
                }
            },
            Op::BCS(x) => {
                if self.p[Flag::Carry] {
                    self.pc += x;
                }
            },
            Op::BEQ(x) => {
                if self.p[Flag::Zero] {
                    self.pc += x;
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
                    self.pc += x;
                }
            },
            Op::BNE(x) => {
                if !self.p[Flag::Zero] {
                    self.pc += x;
                }
            },
            Op::BPL(x) => {
                if !self.p[Flag::Negative] {
                    self.pc += x;
                }
            },
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
}
