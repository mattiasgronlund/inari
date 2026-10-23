//! This module serves additional documentations and no code.

#[allow(unused_imports)]
use crate::*;

#[doc = include_str!("_docs/conformance.md")]
pub mod conformance {}

#[doc = include_str!("_docs/formal_intro.md")]
// The extra indentation aligns the TeX inside display math in list items,
// and it does not change how the list renders.
#[allow(clippy::doc_overindented_list_items)]
pub mod formal_intro {}

#[cfg_attr(feature = "gmp", doc = include_str!("_docs/intro.md"))]
pub mod intro {}
