{
  description = "A simple flake for building this Rust li";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    naersk = {
      url = "github:nix-community/naersk";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, naersk, fenix, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        toolchain = with fenix.packages.${system}; {
          rustc = stable.rustc;
          cargo = stable.cargo;
          cbindgen = pkgs.rust-cbindgen;
        };

        naersk' = pkgs.callPackage naersk { };

        # Build the Rust library via naersk
        cargoProject = naersk'.buildPackage {
          src = ./rust_accumulator;
          release = true;
          nativeBuildInputs = [ ];
          # Explicitly define the interface for the C library
          installPhase = ''
            mkdir -p $out/lib

            cp target/release/lib*.so $out/lib/ || true
            cp target/release/lib*.dylib $out/lib/ || true
            cp target/release/lib*.dll $out/lib/ || true


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
          '';
        };

        # This derivation is the C version of the library that can be imported via Haskell.nix
        cLibrary = pkgs.stdenv.mkDerivation {
          name = "librust_accumulator";
          version = "1.0";
          src = cargoProject;

          buildInputs = [ pkgs.pkg-config ];

          installPhase = ''
            mkdir -p $out/lib
            if [ -f $src/lib/librust_accumulator.so ]; then
              cp $src/lib/librust_accumulator.so $out/lib/
            fi
            if [ -f $src/lib/librust_accumulator.dylib ]; then
              cp $src/lib/librust_accumulator.dylib $out/lib/
            fi
            if [ -f $src/lib/librust_accumulator.dll ]; then
              cp $src/lib/librust_accumulator.dll $out/lib/
            fi
            mkdir -p $out/include
            cp $src/include/rust_accumulator.h $out/include/

            # Adding pkg-config support
            mkdir -p $out/lib/pkgconfig
            cat <<EOF > $out/lib/pkgconfig/librust_accumulator.pc
            prefix=$out
            exec_prefix=\''${prefix}
            libdir=\''${exec_prefix}/lib
            includedir=\''${prefix}/include

            Name: librust_accumulator
            Description: A rust based lib for a PCS based accumulator
            Version: 1.0

            Cflags: -I\''${includedir}
            Libs: -L\''${libdir} -lrust_accumulator
            EOF
          '';
        };

      in rec {
        defaultPackage = cLibrary;

        devShell = pkgs.mkShell {
          buildInputs =
            [ toolchain.rustc toolchain.cargo pkgs.rustfmt pkgs.nixfmt ];
        };
      });
}
