mod not_prelude {
    // This is not really prelude, but it saves us from adding an auxiliary crate!
    pub use core::prelude::v1;
}

use not_prelude::v1;

// Rename is okay.
use not_prelude::v1 as v2;

fn main() {
    v1::assert!(true);
    v2::assert!(true);
}
