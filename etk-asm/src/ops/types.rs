use super::imm::{Imm, Immediate};

use std::fmt::Debug;

pub trait ImmediateTypes: Debug + Clone + Eq + PartialEq {
    // TODO: Technically `Self` doesn't need to implement anything, but it makes
    //       derive(...) work on `Op`.

    type P1: Immediate<1>;
    type P2: Immediate<2>;
    type P3: Immediate<3>;
    type P4: Immediate<4>;
    type P5: Immediate<5>;
    type P6: Immediate<6>;
    type P7: Immediate<7>;
    type P8: Immediate<8>;
    type P9: Immediate<9>;
    type P10: Immediate<10>;
    type P11: Immediate<11>;
    type P12: Immediate<12>;
    type P13: Immediate<13>;
    type P14: Immediate<14>;
    type P15: Immediate<15>;
    type P16: Immediate<16>;
    type P17: Immediate<17>;
    type P18: Immediate<18>;
    type P19: Immediate<19>;
    type P20: Immediate<20>;
    type P21: Immediate<21>;
    type P22: Immediate<22>;
    type P23: Immediate<23>;
    type P24: Immediate<24>;
    type P25: Immediate<25>;
    type P26: Immediate<26>;
    type P27: Immediate<27>;
    type P28: Immediate<28>;
    type P29: Immediate<29>;
    type P30: Immediate<30>;
    type P31: Immediate<31>;
    type P32: Immediate<32>;
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Concrete {}

impl ImmediateTypes for Concrete {
    type P1 = [u8; 1];
    type P2 = [u8; 2];
    type P3 = [u8; 3];
    type P4 = [u8; 4];
    type P5 = [u8; 5];
    type P6 = [u8; 6];
    type P7 = [u8; 7];
    type P8 = [u8; 8];
    type P9 = [u8; 9];
    type P10 = [u8; 10];
    type P11 = [u8; 11];
    type P12 = [u8; 12];
    type P13 = [u8; 13];
    type P14 = [u8; 14];
    type P15 = [u8; 15];
    type P16 = [u8; 16];
    type P17 = [u8; 17];
    type P18 = [u8; 18];
    type P19 = [u8; 19];
    type P20 = [u8; 20];
    type P21 = [u8; 21];
    type P22 = [u8; 22];
    type P23 = [u8; 23];
    type P24 = [u8; 24];
    type P25 = [u8; 25];
    type P26 = [u8; 26];
    type P27 = [u8; 27];
    type P28 = [u8; 28];
    type P29 = [u8; 29];
    type P30 = [u8; 30];
    type P31 = [u8; 31];
    type P32 = [u8; 32];
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Abstract {}

impl ImmediateTypes for Abstract {
    type P1 = Imm<[u8; 1]>;
    type P2 = Imm<[u8; 2]>;
    type P3 = Imm<[u8; 3]>;
    type P4 = Imm<[u8; 4]>;
    type P5 = Imm<[u8; 5]>;
    type P6 = Imm<[u8; 6]>;
    type P7 = Imm<[u8; 7]>;
    type P8 = Imm<[u8; 8]>;
    type P9 = Imm<[u8; 9]>;
    type P10 = Imm<[u8; 10]>;
    type P11 = Imm<[u8; 11]>;
    type P12 = Imm<[u8; 12]>;
    type P13 = Imm<[u8; 13]>;
    type P14 = Imm<[u8; 14]>;
    type P15 = Imm<[u8; 15]>;
    type P16 = Imm<[u8; 16]>;
    type P17 = Imm<[u8; 17]>;
    type P18 = Imm<[u8; 18]>;
    type P19 = Imm<[u8; 19]>;
    type P20 = Imm<[u8; 20]>;
    type P21 = Imm<[u8; 21]>;
    type P22 = Imm<[u8; 22]>;
    type P23 = Imm<[u8; 23]>;
    type P24 = Imm<[u8; 24]>;
    type P25 = Imm<[u8; 25]>;
    type P26 = Imm<[u8; 26]>;
    type P27 = Imm<[u8; 27]>;
    type P28 = Imm<[u8; 28]>;
    type P29 = Imm<[u8; 29]>;
    type P30 = Imm<[u8; 30]>;
    type P31 = Imm<[u8; 31]>;
    type P32 = Imm<[u8; 32]>;
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Spec {}

impl ImmediateTypes for Spec {
    type P1 = ();
    type P2 = ();
    type P3 = ();
    type P4 = ();
    type P5 = ();
    type P6 = ();
    type P7 = ();
    type P8 = ();
    type P9 = ();
    type P10 = ();
    type P11 = ();
    type P12 = ();
    type P13 = ();
    type P14 = ();
    type P15 = ();
    type P16 = ();
    type P17 = ();
    type P18 = ();
    type P19 = ();
    type P20 = ();
    type P21 = ();
    type P22 = ();
    type P23 = ();
    type P24 = ();
    type P25 = ();
    type P26 = ();
    type P27 = ();
    type P28 = ();
    type P29 = ();
    type P30 = ();
    type P31 = ();
    type P32 = ();
}
