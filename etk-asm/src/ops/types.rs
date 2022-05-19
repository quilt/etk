use etk_ops::Immediates;

use super::imm::Imm;

use std::fmt::Debug;

/// Marker type for instructions which may accept labels, variables, or constants
/// as arguments.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Abstract {}

impl Immediates for Abstract {
    type ImmediateRef = Imm;
    type Immediate = Imm;

    type P1 = Imm;
    type P2 = Imm;
    type P3 = Imm;
    type P4 = Imm;
    type P5 = Imm;
    type P6 = Imm;
    type P7 = Imm;
    type P8 = Imm;
    type P9 = Imm;
    type P10 = Imm;
    type P11 = Imm;
    type P12 = Imm;
    type P13 = Imm;
    type P14 = Imm;
    type P15 = Imm;
    type P16 = Imm;
    type P17 = Imm;
    type P18 = Imm;
    type P19 = Imm;
    type P20 = Imm;
    type P21 = Imm;
    type P22 = Imm;
    type P23 = Imm;
    type P24 = Imm;
    type P25 = Imm;
    type P26 = Imm;
    type P27 = Imm;
    type P28 = Imm;
    type P29 = Imm;
    type P30 = Imm;
    type P31 = Imm;
    type P32 = Imm;
}
