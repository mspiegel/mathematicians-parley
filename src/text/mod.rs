//! Text as the corpus is written and as the tools quote it.

pub mod encoding;
pub mod pyrepr;
pub mod pystr;

pub use encoding::check_encoding;
pub use pyrepr::repr;
