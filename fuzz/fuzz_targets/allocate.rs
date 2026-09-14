//! Fuzz the register allocator against its own checker.
//!
//! Each test case is a `regicide::test::TestInput` (a machine, options, and
//! function) encoded with `postcard`. The fuzz target allocates it and checks
//! the result; the mutator decodes, mutates with `mutatis`, and re-encodes, so
//! that the fuzzer walks through valid inputs rather than through random bytes.

#![no_main]

use libfuzzer_sys::{fuzz_mutator, fuzz_target, fuzzer_mutate};
use mutatis::Session;
use regicide::test::{TestInput, TestInputMutator};

/// Decode a corpus entry into a `TestInput`.
fn decode(bytes: &[u8]) -> Option<TestInput> {
    // Allow trailing bytes, presumably inserted by libFuzzer's cross-over
    // mutation or the raw `fuzzer_mutate` fallback below, rather than throwing
    // away an otherwise-usable test case.
    let (mut input, _rest) = postcard::take_from_bytes::<TestInput>(bytes).ok()?;
    input.fixup();
    Some(input)
}

fuzz_target!(|bytes: &[u8]| {
    let _ = env_logger::try_init();
    let Some(input) = decode(bytes) else { return };
    if let Err(e) = regicide::test::check_allocation(&input) {
        panic!("{e}\n\ninput:\n\n{input:#?}");
    }
});

fuzz_mutator!(|data: &mut [u8], size: usize, max_size: usize, seed: u32| {
    let mut session = Session::new().seed(seed.into()).shrink(max_size < size);

    let input = match decode(&data[..size]) {
        Some(mut input) => match session.mutate(&mut input) {
            Ok(()) => input,
            Err(_) => return fuzzer_mutate(data, size, max_size),
        },
        None => match session.generate_with(&mut TestInputMutator::default()) {
            Ok(input) => input,
            Err(_) => return fuzzer_mutate(data, size, max_size),
        },
    };

    match postcard::to_slice(&input, &mut data[..max_size]) {
        Ok(encoded) => encoded.len(),
        Err(_) => fuzzer_mutate(data, size, max_size),
    }
});
