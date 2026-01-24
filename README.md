# rust-accumulator
An optimized rust lib for a POC vector commitment scheme over a BLS based PCS

The recommended way to install this library/dependency is via Nix, but
if you are stubborn and would prefer to do it manually, read on.

## Build and Install

This repo contains a `Makefile` with all the standard `Make` targets.
The `Makefile` only builds the static library.

When this library is used by other packages, `pkg-config` is used to 
find the correct `CFLAGS` and `LIBS` settings so the `Makefile` also
contains a `make pkgconfig` target.

Assuming you have the `cargo` (Rust build tool) installed (installing
`cargo` will probably pull in everything else needed) you only need to
specify an `INSTALL` directory.

It is sensible to have a user local install path for libraries.
Something like `$HOME/Local` and to then set the following environment
variable set:
```
PKG_CONFIG_PATH=$HOME/Local/lib/pkgconfig
```

Building an installing this Rust library is as simple as:
```
INSTALL=$HOME/Local make install
```
