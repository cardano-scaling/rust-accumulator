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

      # Conditional stdenv: cross on darwin/non-x86 linux, native musl on x86_64-linux
      targetStdenv = if pkgs.stdenv.isDarwin || pkgs.stdenv.isAarch64
        then pkgs.pkgsCross.musl64.stdenv
        else pkgs.pkgsMusl.stdenv;

    in rec {
      packages.default = naersk'.buildPackage {
        src = lib.cleanSource "${self}/rust_accumulator";
        stdenv = targetStdenv;
        doCheck = false;
        copyLibs = true;

        CARGO_BUILD_TARGET = if pkgs.stdenv.isDarwin then null else "x86_64-unknown-linux-musl";
        CARGO_BUILD_RUSTFLAGS = "-C target-feature=+crt-static";

        postInstall = ''
          mkdir -p $out/lib/pkgconfig

          version=$(grep '^version = "[^"]*"' Cargo.toml | cut -d '"' -f2 | head -n1)

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
}
