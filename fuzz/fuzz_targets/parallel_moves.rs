#![no_main]

use libfuzzer_sys::{fuzz_mutator, fuzz_target, fuzzer_mutate};
use mutatis::Session;
use regicide::test::{TestParallelMoves, TestParallelMovesMutator};

/// Decode a corpus entry into a `TestParallelMoves`.
fn decode(bytes: &[u8]) -> Option<TestParallelMoves> {
    // Allow trailing bytes, presumably inserted by libFuzzer's cross-over
    // mutation or the raw `fuzzer_mutate` fallback below, rather than throwing
    // away an otherwise-usable test case.
    let (mut moves, _rest) = postcard::take_from_bytes::<TestParallelMoves>(bytes).ok()?;
    moves.fixup();
    Some(moves)
}

fuzz_target!(|bytes: &[u8]| {
    let _ = env_logger::try_init();
    let Some(moves) = decode(bytes) else { return };
    if let Err(e) = moves.check() {
        panic!(
            "{e}\n\nreproduce this batch with:\n\n{}",
            moves.as_test_case()
        );
    }
});

fuzz_mutator!(|data: &mut [u8], size: usize, max_size: usize, seed: u32| {
    let mut session = Session::new().seed(seed.into()).shrink(max_size < size);

    // With low probability, use libfuzzer's default mutator.
    if session.generate::<u8>().is_ok_and(|x| x == 0) {
        return fuzzer_mutate(data, size, max_size);
    }

    let moves = match decode(&data[..size]) {
        Some(mut moves) => match session.mutate(&mut moves) {
            Ok(()) => moves,
            Err(_) => return fuzzer_mutate(data, size, max_size),
        },
        None => match session.generate_with(&mut TestParallelMovesMutator::default()) {
            Ok(moves) => moves,
            Err(_) => return fuzzer_mutate(data, size, max_size),
        },
    };

    match postcard::to_slice(&moves, &mut data[..max_size]) {
        Ok(encoded) => encoded.len(),
        Err(_) => fuzzer_mutate(data, size, max_size),
    }
});
