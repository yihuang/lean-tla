//! Rust support library for Leslie-style round-based protocols.
//!
//! The crate is split into three modules:
//! - `comm`: communication and logical-time abstractions
//! - `protocol`: pure protocol traits
//! - `driver`: execution helpers that run protocols over communication

pub mod ballot_leader_phased;
pub mod comm;
pub mod driver;
pub mod protocol;

pub use crate::ballot_leader_phased::*;
pub use crate::comm::*;
pub use crate::driver::*;
pub use crate::protocol::*;
