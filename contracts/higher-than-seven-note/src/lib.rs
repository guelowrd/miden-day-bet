// Do not link against libstd (i.e. anything defined in `std::`)
#![no_std]

// However, we could still use some standard library types while
// remaining no-std compatible, if we uncommented the following lines:
//
extern crate alloc;

use miden::*;

use crate::bindings::miden::betting_account::betting_account;

#[note_script]
fn run(_arg: Word) {
    let inputs = active_note::get_inputs();
    let input_value = inputs[0];
    let expected = inputs[1];

    let result = betting_account::higher_than_seven(input_value);
    assert_eq!(result, expected);
}
