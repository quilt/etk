use etk_dasm::sym::{Expr, Sym, Var, Visit};

use std::convert::TryInto;

use z3::ast::{Ast, Dynamic, BV};
use z3::{FuncDecl, Sort};

pub(crate) trait ExprExt {
    fn to_z3<'z>(&self, context: &'z z3::Context) -> BV<'z>;
}

impl ExprExt for Expr {
    fn to_z3<'z>(&self, context: &'z z3::Context) -> BV<'z> {
        let mut visitor = Z3Visit {
            context,
            arguments: vec![],
        };

        self.walk(&mut visitor).unwrap();

        assert_eq!(visitor.arguments.len(), 1);
        visitor.arguments.remove(0)
    }
}

struct Z3Visit<'z> {
    context: &'z z3::Context,
    arguments: Vec<BV<'z>>,
}

impl<'z> Z3Visit<'z> {
    fn make_const(&self, bytes: &[u8; 32]) -> BV<'z> {
        // TODO: This is absolutely not the right way to do this.
        let u0 = u64::from_be_bytes(bytes[0..8].try_into().unwrap());
        let u1 = u64::from_be_bytes(bytes[8..16].try_into().unwrap());
        let u2 = u64::from_be_bytes(bytes[16..24].try_into().unwrap());
        let u3 = u64::from_be_bytes(bytes[24..32].try_into().unwrap());

        let bv0 = BV::from_u64(self.context, u0, 64);
        let bv1 = BV::from_u64(self.context, u1, 64);
        let bv2 = BV::from_u64(self.context, u2, 64);
        let bv3 = BV::from_u64(self.context, u3, 64);

        bv0.concat(&bv1).concat(&bv2).concat(&bv3).simplify()
    }

    fn make_var(&self, var: &Var) -> BV<'z> {
        let name = format!("etk_{}", var);
        BV::new_const(self.context, name, 256)
    }

    fn make_address(&self, name: &str) -> BV<'z> {
        // TODO: Addresses are only 160 bytes.
        BV::new_const(self.context, name, 256)
    }
}

impl<'z> Visit for Z3Visit<'z> {
    type Error = std::convert::Infallible;

    fn exit(&mut self, sym: &Sym) -> Result<(), Self::Error> {
        let node = match sym {
            Sym::Const(value) => self.make_const(value),
            Sym::Var(var) => self.make_var(var),

            Sym::Address => self.make_address("address"),
            Sym::Origin => self.make_address("origin"),
            Sym::Caller => self.make_address("caller"),
            Sym::CallValue => BV::new_const(self.context, "callvalue", 256),
            Sym::CallDataSize => BV::new_const(self.context, "calldatasize", 256),
            Sym::CodeSize => BV::new_const(self.context, "codesize", 256),
            Sym::GasPrice => BV::new_const(self.context, "gasprice", 256),
            Sym::ReturnDataSize => BV::fresh_const(self.context, "returndatasize", 256),
            Sym::Coinbase => self.make_address("coinbase"),
            Sym::Timestamp => BV::new_const(self.context, "timestamp", 256),
            Sym::Number => BV::new_const(self.context, "number", 256),
            Sym::Difficulty => BV::new_const(self.context, "difficulty", 256),
            Sym::GasLimit => BV::new_const(self.context, "gaslimit", 256),
            Sym::ChainId => BV::new_const(self.context, "chainid", 256),
            Sym::SelfBalance => BV::fresh_const(self.context, "selfbalance", 256),
            Sym::BaseFee => BV::new_const(self.context, "basefee", 256),
            Sym::GetPc(pc) => BV::from_u64(self.context, *pc as u64, 256),
            Sym::MSize => BV::fresh_const(self.context, "msize", 256),
            Sym::Gas => BV::fresh_const(self.context, "gas", 256),

            Sym::Add => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                lhs + rhs
            }

            Sym::Sub => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                lhs - rhs
            }

            Sym::Mul => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                lhs * rhs
            }

            Sym::Div => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                let zero = BV::from_u64(self.context, 0, 256);
                rhs._eq(&zero).ite(&zero, &lhs.bvudiv(&rhs))
            }

            Sym::SDiv => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                let zero = BV::from_u64(self.context, 0, 256);
                rhs._eq(&zero).ite(&zero, &lhs.bvsdiv(&rhs))
            }

            Sym::Mod => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                let zero = BV::from_u64(self.context, 0, 256);
                rhs._eq(&zero).ite(&zero, &lhs.bvurem(&rhs))
            }

            Sym::SMod => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                let zero = BV::from_u64(self.context, 0, 256);
                rhs._eq(&zero).ite(&zero, &lhs.bvsmod(&rhs))
            }

            Sym::Exp => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                // TODO: Probably incorrect, certainly inefficient.
                //       Something something discrete log problem?
                lhs.to_int(false).power(&rhs.to_int(false)).to_ast(256)
            }

            Sym::Lt => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                lhs.bvult(&rhs).ite(
                    &BV::from_u64(self.context, 1, 256),
                    &BV::from_u64(self.context, 0, 256),
                )
            }

            Sym::Gt => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                lhs.bvugt(&rhs).ite(
                    &BV::from_u64(self.context, 1, 256),
                    &BV::from_u64(self.context, 0, 256),
                )
            }

            Sym::SLt => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                lhs.bvslt(&rhs).ite(
                    &BV::from_u64(self.context, 1, 256),
                    &BV::from_u64(self.context, 0, 256),
                )
            }

            Sym::SGt => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                lhs.bvsgt(&rhs).ite(
                    &BV::from_u64(self.context, 1, 256),
                    &BV::from_u64(self.context, 0, 256),
                )
            }

            Sym::Eq => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                lhs._eq(&rhs).ite(
                    &BV::from_u64(self.context, 1, 256),
                    &BV::from_u64(self.context, 0, 256),
                )
            }

            Sym::And => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                lhs.bvand(&rhs)
            }

            Sym::Or => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                lhs.bvor(&rhs)
            }

            Sym::Xor => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                lhs.bvxor(&rhs)
            }

            Sym::Shl => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                rhs.bvshl(&lhs)
            }

            Sym::Shr => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                rhs.bvlshr(&lhs)
            }

            Sym::Sar => {
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                rhs.bvashr(&lhs)
            }

            Sym::Not => {
                let arg = self.arguments.pop().unwrap();
                arg.bvnot()
            }

            Sym::IsZero => {
                let arg = self.arguments.pop().unwrap();
                let zero = BV::from_u64(self.context, 0, 256);
                arg._eq(&zero).ite(
                    &BV::from_u64(self.context, 1, 256),
                    &BV::from_u64(self.context, 0, 256),
                )
            }

            Sym::Keccak256 => {
                let _offset = self.arguments.pop().unwrap();
                let _len = self.arguments.pop().unwrap();

                // TODO: Better handling, once memory is implemented.
                BV::fresh_const(self.context, "keccak256", 256)
            }

            Sym::SignExtend => {
                let _bits = self.arguments.pop().unwrap();
                let _value = self.arguments.pop().unwrap();

                todo!()
            }

            Sym::CallDataLoad => {
                let offset = self.arguments.pop().unwrap();

                let sort = Sort::bitvector(self.context, 256);

                let func = FuncDecl::new(self.context, "calldataload", &[&sort], &sort);

                let apply = func.apply(&[&Dynamic::from_ast(&offset)]);
                apply.as_bv().unwrap()
            }

            Sym::ExtCodeSize => {
                let _addr = self.arguments.pop().unwrap();
                BV::fresh_const(self.context, "extcodesize", 256)
            }

            Sym::ExtCodeHash => {
                let _addr = self.arguments.pop().unwrap();
                BV::fresh_const(self.context, "extcodehash", 256)
            }

            Sym::MLoad => {
                let _addr = self.arguments.pop().unwrap();
                BV::fresh_const(self.context, "mload", 256)
            }

            Sym::SLoad => {
                let _addr = self.arguments.pop().unwrap();
                BV::fresh_const(self.context, "sload", 256)
            }

            Sym::Balance => {
                let _addr = self.arguments.pop().unwrap();
                BV::fresh_const(self.context, "balance", 256)
            }

            Sym::BlockHash => {
                let num = self.arguments.pop().unwrap();

                let sort = Sort::bitvector(self.context, 256);

                let func = FuncDecl::new(self.context, "blockhash", &[&sort], &sort);

                let apply = func.apply(&[&Dynamic::from_ast(&num)]);
                apply.as_bv().unwrap()
            }

            Sym::AddMod => {
                let modulus = self.arguments.pop().unwrap();
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                let zero = BV::from_u64(self.context, 0, 256);
                let addmod = (rhs + lhs).bvurem(&modulus);
                modulus._eq(&zero).ite(&zero, &addmod)
            }

            Sym::MulMod => {
                let modulus = self.arguments.pop().unwrap();
                let rhs = self.arguments.pop().unwrap();
                let lhs = self.arguments.pop().unwrap();

                let zero = BV::from_u64(self.context, 0, 256);
                let addmod = (rhs * lhs).bvurem(&modulus);
                modulus._eq(&zero).ite(&zero, &addmod)
            }

            Sym::Create => {
                let _length = self.arguments.pop();
                let _offset = self.arguments.pop();
                let _value = self.arguments.pop();

                BV::fresh_const(self.context, "create", 256)
            }

            Sym::Create2 => {
                let _salt = self.arguments.pop();
                let _length = self.arguments.pop();
                let _offset = self.arguments.pop();
                let _value = self.arguments.pop();

                BV::fresh_const(self.context, "create2", 256)
            }

            Sym::CallCode => {
                let _ret_len = self.arguments.pop();
                let _ret_offset = self.arguments.pop();
                let _args_len = self.arguments.pop();
                let _args_offset = self.arguments.pop();
                let _value = self.arguments.pop();
                let _addr = self.arguments.pop();
                let _gas = self.arguments.pop();

                BV::fresh_const(self.context, "callcode", 256)
            }

            Sym::Call => {
                let _ret_len = self.arguments.pop();
                let _ret_offset = self.arguments.pop();
                let _args_len = self.arguments.pop();
                let _args_offset = self.arguments.pop();
                let _value = self.arguments.pop();
                let _addr = self.arguments.pop();
                let _gas = self.arguments.pop();

                BV::fresh_const(self.context, "call", 256)
            }

            Sym::StaticCall => {
                let _ret_len = self.arguments.pop();
                let _ret_offset = self.arguments.pop();
                let _args_len = self.arguments.pop();
                let _args_offset = self.arguments.pop();
                let _addr = self.arguments.pop();
                let _gas = self.arguments.pop();

                BV::fresh_const(self.context, "staticcall", 256)
            }

            Sym::DelegateCall => {
                let _ret_len = self.arguments.pop();
                let _ret_offset = self.arguments.pop();
                let _args_len = self.arguments.pop();
                let _args_offset = self.arguments.pop();
                let _addr = self.arguments.pop();
                let _gas = self.arguments.pop();

                BV::fresh_const(self.context, "delegatecall", 256)
            }

            Sym::Byte => {
                let value = self.arguments.pop().unwrap();
                let position = self.arguments.pop().unwrap();

                let c248 = BV::from_u64(self.context, 248, 256);
                let c8 = BV::from_u64(self.context, 8, 256);
                let c255 = BV::from_u64(self.context, 255, 256);

                let shift = c248 - (position * c8);
                let shifted = value.bvlshr(&shift);

                shifted.bvand(&c255)
            }
        };

        self.arguments.push(node);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use hex_literal::hex;

    use super::*;

    use z3::ast::{Ast, BV};
    use z3::SatResult;

    #[test]
    fn sym_to_z3_const() {
        let bytes: [u8; 32] =
            hex!("abcdef0123456789aabbccddeeff001122334455667788999876543210fedcba");
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(bytes)
            .to_z3(&ctx)
            .bvadd(&BV::from_u64(&ctx, 1, 256)); // Add 1 to check endianness.

        let expected_highest = BV::from_u64(&ctx, 0xabcdef0123456789, 64);
        let expected_higher = BV::from_u64(&ctx, 0xaabbccddeeff0011, 64);
        let expected_lower = BV::from_u64(&ctx, 0x2233445566778899, 64);
        let expected_lowest = BV::from_u64(&ctx, 0x9876543210fedcbb, 64);

        let actual_lowest = expr.extract(63, 0);
        let actual_lower = expr.extract(127, 64);
        let actual_higher = expr.extract(191, 128);
        let actual_highest = expr.extract(255, 192);

        // TODO: So this is probably overkill, buuuuut that's fine.
        let solver = z3::Solver::new(&ctx);
        solver.assert(&actual_highest._eq(&expected_highest));
        solver.assert(&actual_higher._eq(&expected_higher));
        solver.assert(&actual_lower._eq(&expected_lower));
        solver.assert(&actual_lowest._eq(&expected_lowest));

        assert_eq!(SatResult::Sat, solver.check());
    }

    #[test]
    fn add_one_and_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).add(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(3));
    }

    #[test]
    fn add_one_and_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).add(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn sub_two_from_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).sub(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(1));
    }

    #[test]
    fn sub_max_from_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).sub(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(4));
    }

    #[test]
    fn mul_three_by_four() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).mul(&Expr::constant(&[4]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(12));
    }

    #[test]
    fn mul_max_by_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).mul(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(1));
    }

    #[test]
    fn div_max_by_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).div(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(1));
    }

    #[test]
    fn div_one_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).div(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn div_zero_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0]).div(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn div_zero_by_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0]).div(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn sdiv_max_by_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).s_div(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(1));
    }

    #[test]
    fn sdiv_zero_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0]).s_div(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn sdiv_one_by_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).s_div(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();

        let expected = Expr::constant(&[0xff; 32]).to_z3(&ctx);

        assert_eq!(ast, expected);
    }

    #[test]
    fn mod_three_by_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).modulo(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();

        let expected = BV::from_u64(&ctx, 1, 256);

        assert_eq!(ast, expected);
    }

    #[test]
    fn mod_three_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).modulo(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();

        let expected = BV::from_u64(&ctx, 0, 256);

        assert_eq!(ast, expected);
    }

    #[test]
    fn mod_one_by_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).modulo(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();

        let expected = BV::from_u64(&ctx, 1, 256);

        assert_eq!(ast, expected);
    }

    #[test]
    fn mod_max_by_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).modulo(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();

        let expected = BV::from_u64(&ctx, 0, 256);

        assert_eq!(ast, expected);
    }

    #[test]
    fn smod_zero_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0]).s_modulo(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn smod_one_by_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).s_modulo(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn smod_neg_one_by_neg_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let mut neg_two = [0xff; 32];
        neg_two[31] = 0xfe;

        let expr = Expr::constant(&[0xff; 32]).s_modulo(&Expr::constant(&neg_two));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = Expr::constant(&[0xff; 32]).to_z3(&ctx);
        assert_eq!(ast, expected);
    }

    #[test]
    fn smod_neg_two_by_neg_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let mut neg_two = [0xff; 32];
        neg_two[31] = 0xfe;

        let expr = Expr::constant(&neg_two).s_modulo(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0));
    }

    #[test]
    fn exp_three_raised_four() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).exp(&Expr::constant(&[4]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(0x51));
    }

    #[test]
    fn exp_three_raised_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).exp(&Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        assert_eq!(ast.as_u64(), Some(1));
    }

    #[test]
    fn exp_max_raised_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).exp(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);

        let solver = z3::Solver::new(&ctx);
        solver.assert(&ast._eq(&expected));

        assert_eq!(SatResult::Sat, solver.check());
    }

    #[test]
    fn two_lt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[2]).lt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_lt_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).lt(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_lt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).lt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn two_gt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[2]).gt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_gt_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).gt(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_gt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).gt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn two_sgt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[2]).s_gt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_sgt_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_gt(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_sgt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_gt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_sgt_neg_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_gt(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn two_slt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[2]).s_lt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_slt_two() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_lt(&Expr::constant(&[2]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_slt_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_lt(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_slt_neg_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).s_lt(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_eq_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).is_eq(&Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_eq_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).is_eq(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_and_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).and(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 3, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_and_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).and(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_or_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).or(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = Expr::constant(&[0xff; 32]).to_z3(&ctx);
        assert_eq!(ast, expected);
    }

    #[test]
    fn four_or_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[4]).or(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 5, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn three_xor_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[3]).xor(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 2, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn byte_32() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let value: [_; 32] =
            hex!("00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff");

        let expr = Expr::constant(&[32]).byte(&Expr::constant(&value));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0x0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn byte_31() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let value: [_; 32] =
            hex!("00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff");

        let expr = Expr::constant(&[31]).byte(&Expr::constant(&value));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0xff, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn byte_30() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let value: [_; 32] =
            hex!("00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff");

        let expr = Expr::constant(&[30]).byte(&Expr::constant(&value));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0xee, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn byte_0() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let value: [_; 32] =
            hex!("AB112233445566778899aabbccddeeff00112233445566778899aabbccddeeff");

        let expr = Expr::constant(&[0]).byte(&Expr::constant(&value));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0xab, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn shl_one_by_four() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[4]).shl(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0x10, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn shr_selector_by_224() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let mut value = [0u8; 32];
        value[0] = 0x23;
        value[1] = 0xb8;
        value[2] = 0x72;
        value[3] = 0xdd;

        let expr = Expr::constant(&[224]).shr(&Expr::constant(&value));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0x23b872dd, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn shr_max_by_248() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[248]).shr(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0xff, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn sar_max_by_248() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[248]).sar(&Expr::constant(&[0xff; 32]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = Expr::constant(&[0xff; 32]).to_z3(&ctx);
        assert_eq!(ast, expected);
    }

    #[test]
    fn sar_one_by_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).sar(&Expr::constant(&[1]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn is_zero_one() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[1]).is_zero();
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn is_zero_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0]).is_zero();
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn not_max() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[0xff; 32]).not();
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn add_mod_five_and_eight_mod_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[5]).add_mod(&Expr::constant(&[8]), &Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn add_mod_five_and_eight_mod_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[5]).add_mod(&Expr::constant(&[8]), &Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn mul_mod_five_and_eight_mod_three() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[5]).mul_mod(&Expr::constant(&[8]), &Expr::constant(&[3]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 1, 256);
        assert_eq!(ast, expected);
    }

    #[test]
    fn mul_mod_five_and_eight_mod_zero() {
        let config = z3::Config::new();
        let ctx = z3::Context::new(&config);

        let expr = Expr::constant(&[5]).mul_mod(&Expr::constant(&[8]), &Expr::constant(&[0]));
        let ast = expr.to_z3(&ctx).simplify();
        let expected = BV::from_u64(&ctx, 0, 256);
        assert_eq!(ast, expected);
    }
}
