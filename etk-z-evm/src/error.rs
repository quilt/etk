use snafu::{Backtrace, Snafu};

#[derive(Debug, Snafu)]
#[snafu(visibility(pub(crate)))]
pub enum Error<S>
where
    S: 'static + snafu::Error,
{
    Memory {
        #[snafu(backtrace)]
        source: crate::resolve::Error,
    },

    #[snafu(display("storage operation failed"))]
    Storage { backtrace: Backtrace, source: S },
}
