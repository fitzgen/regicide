//! Reading a serialized input without being told how it was encoded.
//!
//! `regicide-dump` writes `postcard`, but corpora captured before it did are
//! JSON, and a hand-written or hand-edited input is JSON too. Both are worth
//! replaying, and which one a file holds is cheap to work out, so the examples
//! take either and say nothing about it.
//!
//! Shared by the examples via `#[path = "support/encoding.rs"] mod encoding;`
//! rather than living in the library, because detecting an encoding is a
//! convenience for a command line and not something regicide itself offers.

// Each example uses the part of this module it needs: `visualize` reads the
// one file it was pointed at and never walks a directory.
#![allow(dead_code, reason = "shared by examples that use different parts")]

use regicide::deserialize::DeserializedInput;
use std::{fs, path::Path};

/// Which encoding a file's bytes appear to be in.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Encoding {
    Json,
    Postcard,
}

impl Encoding {
    /// Guess from the bytes themselves rather than from the file's extension,
    /// so that a renamed or extensionless file still reads.
    ///
    /// A serialized input is a struct, so JSON means a leading `{`, possibly
    /// behind whitespace. Postcard is positional and starts with the options'
    /// first field, a bool encoded as one byte, so it can never begin that
    /// way.
    fn sniff(bytes: &[u8]) -> Self {
        match bytes.iter().find(|b| !b.is_ascii_whitespace()) {
            Some(b'{') => Encoding::Json,
            _ => Encoding::Postcard,
        }
    }

    fn decode(self, bytes: &[u8]) -> Result<DeserializedInput, String> {
        match self {
            Encoding::Json => serde_json::from_slice(bytes).map_err(|e| e.to_string()),
            Encoding::Postcard => postcard::from_bytes(bytes).map_err(|e| e.to_string()),
        }
    }

    fn other(self) -> Self {
        match self {
            Encoding::Json => Encoding::Postcard,
            Encoding::Postcard => Encoding::Json,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Encoding::Json => "JSON",
            Encoding::Postcard => "postcard",
        }
    }
}

/// The file extensions a directory of inputs is made of.
///
/// `scripts/make-corpus` writes `.postcard`; `.json` is what it used to write,
/// and what a corpus committed back then still holds.
pub const EXTENSIONS: [&str; 2] = ["postcard", "json"];

/// Does `path` name a file that [`load`] should be handed?
///
/// Only consulted when walking a directory. A path given explicitly is read
/// whatever it is called, since naming it is already the request.
pub fn is_input(path: &Path) -> bool {
    path.extension()
        .is_some_and(|ext| EXTENSIONS.iter().any(|known| ext == *known))
}

/// Read one serialized input, in whichever encoding it turns out to be.
pub fn load(path: &Path) -> Result<DeserializedInput, String> {
    let bytes = fs::read(path).map_err(|e| e.to_string())?;

    // The sniff decides which error is worth reporting, not which encoding is
    // allowed: a file that sniffs as one and parses as the other still loads.
    // That matters because the two failures read very differently, and the
    // useful message is the one from the encoding the file actually is.
    let guess = Encoding::sniff(&bytes);
    match guess.decode(&bytes) {
        Ok(input) => Ok(input),
        Err(e) => match guess.other().decode(&bytes) {
            Ok(input) => Ok(input),
            Err(_) => Err(format!("not a valid {} input: {e}", guess.name())),
        },
    }
}
