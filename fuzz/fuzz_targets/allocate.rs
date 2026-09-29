//! Fuzz the register allocator against its own checker.
//!
//! Each test case is a `regicide::test::TestInput` (a machine, options, and
//! function) encoded with `postcard`. The fuzz target allocates it and checks
//! the result; the mutator decodes, mutates with `mutatis`, and re-encodes, so
//! that the fuzzer walks through valid inputs rather than through random bytes.

#![no_main]

use libfuzzer_sys::{fuzz_mutator, fuzz_target, fuzzer_mutate};
use mutatis::Session;
use regicide::{
    serialize::SerializeInput,
    test::{TestInput, TestInputMutator},
};
use std::{
    fs::File,
    hash::{DefaultHasher, Hash, Hasher},
    io::BufWriter,
    path::PathBuf,
};

/// Decode a corpus entry into a `TestInput`.
fn decode(bytes: &[u8]) -> Option<TestInput> {
    // Allow trailing bytes, presumably inserted by libFuzzer's cross-over
    // mutation or the raw `fuzzer_mutate` fallback below, rather than throwing
    // away an otherwise-usable test case.
    let (mut input, _rest) = postcard::take_from_bytes::<TestInput>(bytes).ok()?;
    input.fixup();
    Some(input)
}

/// Write `input` out as JSON and report where it landed.
///
/// The name comes from a hash of the bytes we were handed, so re-running the
/// same input overwrites its file rather than leaving another copy behind.
fn dump(input: &TestInput, bytes: &[u8]) -> Result<PathBuf, String> {
    let mut hasher = DefaultHasher::new();
    bytes.hash(&mut hasher);
    let path = PathBuf::from(format!("input-{:016x}.json", hasher.finish()));
    log::info!("serializing input as JSON to `{}`", path.display());

    let file = File::create(&path).map_err(|e| e.to_string())?;
    input.with_input(|input| {
        serde_json::to_writer(BufWriter::new(file), &SerializeInput::new(input))
            .map_err(|e| e.to_string())
    })?;

    // A relative path is no help when we don't know where libFuzzer left us.
    Ok(path.canonicalize().unwrap_or(path))
}

fuzz_target!(|bytes: &[u8]| {
    let _ = env_logger::try_init();
    let Some(input) = decode(bytes) else { return };
    if let Err(e) = regicide::test::check_allocation(&input) {
        let json = match dump(&input, bytes) {
            Ok(path) => {
                let path = path.display();
                format!(
                    "wrote the input to {path}; replay it with\n\n    \
                     cargo run --example visualize --all-features -- --input {path} \
                     /tmp/regicide.html"
                )
            }
            Err(err) => format!("could not write the input out as JSON: {err}"),
        };
        panic!("{e}\n\n{json}\n\ninput:\n\n{input:#?}");
    }
});

fuzz_mutator!(|data: &mut [u8], size: usize, max_size: usize, seed: u32| {
    let mut session = Session::new().seed(seed.into()).shrink(max_size < size);

    // With low probability, use libfuzzer's default mutator.
    if session.generate::<u8>().is_ok_and(|x| x == 0) {
        return fuzzer_mutate(data, size, max_size);
    }

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
