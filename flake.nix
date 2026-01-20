{
  inputs = {
    fenix.url = "github:nix-community/fenix";
    flake-utils.url = "github:numtide/flake-utils";
    naersk.url = "github:nix-community/naersk";
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";
  };

  outputs = { self, fenix, flake-utils, naersk, nixpkgs }:
    flake-utils.lib.eachDefaultSystem (
      system: let
        pkgs = (import nixpkgs) {
          inherit system;
        };

        toolchain = with fenix.packages.${system};
          combine [
            minimal.rustc
            minimal.cargo
            targets.x86_64-unknown-linux-musl.latest.rust-std
          ];

        naersk' = naersk.lib.${system}.override {
          cargo = toolchain;
          rustc = toolchain;
        };

      in rec {
        defaultPackage = naersk'.buildPackage {
          src = ./rust_accumulator;
          doCheck = false;
          copyLibs = true;
          nativeBuildInputs = with pkgs; [ pkgsStatic.stdenv.cc ];

          # Tells Cargo that we're building for musl.
          # (https://doc.rust-lang.org/cargo/reference/config.html#buildtarget)
          CARGO_BUILD_TARGET = "x86_64-unknown-linux-musl";

          # Tells Cargo to enable static compilation.
          # (https://doc.rust-lang.org/cargo/reference/config.html#buildrustflags)
          #
          # Note that the resulting binary might still be considered dynamically
          # linked by ldd, but that's just because the binary might have
          # position-independent-execution enabled.
          # (see: https://github.com/rust-lang/rust/issues/79624#issuecomment-737415388)
          CARGO_BUILD_RUSTFLAGS = "-C target-feature=+crt-static";
          postInstall = ''
            mkdir -p $out/lib/pkgconfig

            version=$(grep '^version = "[^"]*"' Cargo.toml | cut -d '"' -f2 | head -n1)

            mkdir -p $out/include
            cat > $out/include/rust_accumulator.h <<'EOF'
            #include "blst.h"
            #include <stddef.h>

            // Define the Scalar structure as it is in Rust
            typedef struct {
              blst_fr inner;
            } Scalar;

            // Define the G1Projective structure as it is in Rust
            typedef struct {
              blst_p1 inner;
            } G1Projective;

            // Define the G2Projective structure as it is in Rust
            typedef struct {
              blst_p2 inner;
            } G2Projective;

            void get_poly_commitment_g1(G1Projective *return_point, Scalar *scalars_ptr, size_t scalars_len, G1Projective *points_ptr, size_t points_len);

            void get_poly_commitment_g2(G2Projective *return_point, Scalar *scalars_ptr, size_t scalars_len, G2Projective *points_ptr, size_t points_len);

            EOF

            cat > $out/lib/pkgconfig/librust_accumulator.pc <<EOF
            prefix=$out
            libdir=\''${prefix}/lib
            includedir=\''${prefix}/include

            Name: librust_accumulator
            Description: Rust Accumulator Library
            Version: ''${version:-0.1.0}
            Libs: -L\''${libdir} -lrust_accumulator
            Cflags: -I\''${includedir}
            EOF
          '';
        };
      }
    );
}
