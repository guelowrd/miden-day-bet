// Do not link against libstd (i.e. anything defined in `std::`)
#![no_std]

// However, we could still use some standard library types while
// remaining no-std compatible, if we uncommented the following lines:
//
// extern crate alloc;

use miden::{component, felt, Felt};

/// Main contract structure for the betting example.
#[component]
struct BettingContract;

#[component]
impl BettingContract {
    /// Returns 1 if the input value is strictly greater than 7, otherwise 0.
    pub fn higher_than_seven(&self, input_value: Felt) -> Felt {
        if input_value > felt!(7) {
            felt!(1)
        } else {
            felt!(0)
        }
    }
}
