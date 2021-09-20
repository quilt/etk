use crate::sym::ExprExt;

use etk_dasm::blocks::annotated::Exit;
use etk_dasm::sym::Expr;

use z3::ast::BV;

pub(crate) trait ExitExt {
    fn erase(&self) -> Exit<()>;
    fn to_z3<'z>(&self, context: &'z z3::Context) -> Exit<BV<'z>>;
}

impl ExitExt for Exit<Expr> {
    fn erase(&self) -> Exit<()> {
        match self {
            Self::Terminate => Exit::Terminate,
            Self::FallThrough(f) => Exit::FallThrough(*f),
            Self::Unconditional(_) => Exit::Unconditional(()),
            Self::Branch { when_false, .. } => Exit::Branch {
                condition: (),
                when_true: (),
                when_false: *when_false,
            },
        }
    }

    fn to_z3<'z>(&self, context: &'z z3::Context) -> Exit<BV<'z>> {
        match self {
            Self::Terminate => Exit::Terminate,
            Self::FallThrough(f) => Exit::FallThrough(*f),
            Self::Unconditional(e) => Exit::Unconditional(e.to_z3(context)),
            Self::Branch {
                when_true,
                when_false,
                condition,
            } => {
                let when_true = when_true.to_z3(context);
                let condition = condition.to_z3(context);

                Exit::Branch {
                    when_false: *when_false,
                    when_true,
                    condition,
                }
            }
        }
    }
}
