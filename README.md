raugeas
=======

[![crates.io](https://img.shields.io/crates/v/raugeas.svg)](https://crates.io/crates/raugeas) [![Documentation](https://docs.rs/raugeas/badge.svg)](https://docs.rs/raugeas) [![CI](https://github.com/normation/raugeas/actions/workflows/ci.yml/badge.svg)](https://github.com/normation/raugeas/actions/workflows/ci.yml)

Rust binding for [Augeas](https://github.com/hercules-team/augeas), a configuration editing tool.

These crates were forked from [hercules-team/rust-augeas](https://github.com/hercules-team/rust-augeas).

## Design

This library is a low-level binding to the C API of Augeas, with a few abstractions to make it more idiomatic to use in Rust. It does not aim to provide a high-level API to manipulate configuration files, but rather to provide a safe and idiomatic way to interact with Augeas.

## TODO

* Consider allowing non-UTF-8 strings for paths and values.
* Consider adding missing bindings for the following functions:
  * `aug_to_xml`
* Allow building with older versions of Augeas (currently, it requires 1.13 or later).
* [Add augeas to docs.rs build environment](https://forge.rust-lang.org/docs-rs/add-dependencies.html) to allow building the docs.
