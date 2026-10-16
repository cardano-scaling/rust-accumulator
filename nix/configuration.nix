{ self, inputs, ...}: {
  perSystem = {system, pkgs, lib, ...}:

    let
      toolchain = with inputs.fenix.packages.${system};
        combine [
          minimal.rustc
          minimal.cargo
          targets.x86_64-unknown-linux-musl.latest.rust-std
        ];

      naersk' = inputs.naersk.lib.${system}.override {
        cargo = toolchain;
        rustc = toolchain;
      };

      cargoToml = builtins.fromTOML (builtins.readFile "${self}/rust_accumulator/Cargo.toml");
      version = cargoToml.package.version or "0.1.0";

      proofPkgs = inputs.nixpkgs-proof.legacyPackages.${system};
      leanMathlib = proofPkgs.leanPackages.mathlib;
      leanPath = lib.makeSearchPath ".lake/build/lib/lean"
        ([ leanMathlib ] ++ leanMathlib.allLeanDeps);
      bendKernel = proofPkgs.stdenv.mkDerivation {
        pname = "bendtt";
        version = "2.0.37";
        # Match the compiler's release archive, not the newer repository HEAD.
        src = "${inputs.bend.packages.${system}.default}/libexec/bend";
        nativeBuildInputs = [ proofPkgs.lean4 ];
        buildPhase = ''
          lean -c bendtt.c bend2/bendtt.lean
          leanc -O3 -DNDEBUG bendtt.c -o bendtt
        '';
        installPhase = ''
          install -Dm755 bendtt $out/bin/bendtt
        '';
      };

      mkBendAccumulator = algorithm: pkgs.stdenv.mkDerivation {
        pname = if algorithm == "verified" then "bend-accumulator-prototype"
          else "bend-accumulator-karatsuba-experimental";
        version = "0.1.0";
        src = self;
        nativeBuildInputs = [ inputs.bend.packages.${system}.default pkgs.clang pkgs.python3 proofPkgs.lean4 ];
        LEAN_PATH = leanPath;
        BENDTT = "${bendKernel}/bin/bendtt";
        BEND_NO_TELEMETRY = "1";
        buildPhase = ''
          python3 bend/build.py --algorithm ${algorithm} --output build
        '';
        doCheck = true;
        checkPhase = ''
          bend bend/PROOF.bend --verdict
          ${lib.optionalString (algorithm == "karatsuba") "bend bend/karatsuba/PROOF.bend --verdict"}
          python3 bend/test.py --no-rust --library build/libbend_accumulator.so ${lib.optionalString (algorithm == "karatsuba") "--exhaustive"}
        '';
        installPhase = ''
          install -Dm755 build/libbend_accumulator.so $out/lib/libbend_accumulator.so
          install -Dm644 build/build.json $out/lib/build.json
          install -Dm644 bend/adapter.h $out/include/bend_accumulator.h
        '';
      };

    in {
      devShells.default = pkgs.mkShell ({
        packages = [ toolchain ];
      } // lib.optionalAttrs pkgs.stdenv.isLinux {
        LEAN_PATH = leanPath;
        BENDTT = "${bendKernel}/bin/bendtt";
        BEND_NO_TELEMETRY = "1";
        packages = [
          toolchain
          inputs.bend.packages.${system}.default
          pkgs.clang
          pkgs.python3
          proofPkgs.lean4
        ];
      });

      packages = lib.optionalAttrs pkgs.stdenv.isLinux {
        bend = inputs.bend.packages.${system}.default;
        bend-kernel = bendKernel;

        bend-accumulator = mkBendAccumulator "verified";
        bend-accumulator-karatsuba = mkBendAccumulator "karatsuba";
      } // {
        default = naersk'.buildPackage {
          src = lib.cleanSource "${self}/rust_accumulator";
          stdenv = pkgs.stdenv;
          doCheck = false;
          copyLibs = true;

          CARGO_BUILD_TARGET = if system == "x86_64-linux" then "x86_64-unknown-linux-musl" else null;
          CARGO_BUILD_RUSTFLAGS = if system == "x86_64-linux" then "-C target-feature=+crt-static" else null;

          postInstall = ''
            mkdir -p $out/lib/pkgconfig

            cp "${self}/include" $out/ -r

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
      };

      checks = lib.optionalAttrs pkgs.stdenv.isLinux {
        bend-arithmetic = pkgs.runCommand "bend-accumulator-arithmetic" {
          nativeBuildInputs = [ proofPkgs.lean4 pkgs.python3 ];
          LEAN_PATH = leanPath;
        } ''
          python3 ${self}/bend/arithmetic/check.py --mutations
          touch $out
        '';
        bend-laws = pkgs.runCommand "bend-accumulator-laws" {
          nativeBuildInputs = [ inputs.bend.packages.${system}.default pkgs.python3 ];
          BENDTT = "${bendKernel}/bin/bendtt";
          BEND_NO_TELEMETRY = "1";
        } ''
          python3 ${self}/bend/test_proofs.py
          touch $out
        '';
        bend-native = self.packages.${system}.bend-accumulator;
        bend-karatsuba-native = self.packages.${system}.bend-accumulator-karatsuba;
      };
    };
}
