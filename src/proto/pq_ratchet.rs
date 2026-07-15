// Copyright 2025 Signal Messenger, LLC
// SPDX-License-Identifier: AGPL-3.0-only

#![allow(clippy::derive_partial_eq_without_eq)]

// Include prost's output. See build.rs
#[cfg(not(feature = "extraction"))]
include!(concat!(env!("OUT_DIR"), "/signal.proto.pq_ratchet.rs"));
#[cfg(feature = "extraction")]
include!("generated/signal.proto.pq_ratchet.rs");
