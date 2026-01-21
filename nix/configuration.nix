{ self, inputs, ...}: {
  perSystem = {system, pkgs, lib, ...}:
    let
      toolchain = with inputs.fenix.packages.${system};
        combine [
          minimal.rustc
          minimal.cargo
        ];

      naersk' = inputs.naersk.lib.${system}.override {
        cargo = toolchain;
        rustc = toolchain;
      };


    in rec {
      packages.default = naersk'.buildPackage {
        src = lib.cleanSource "${self}/rust_accumulator";
        stdenv = pkgs.stdenv;
        doCheck = false;
        copyLibs = true;

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
