{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages."${system}";
          vm = pkgs.haskellPackages.developPackage {
            root = ./vm;
        };
      in {
        devShells.default = pkgs.mkShell {
          nativeBuildInputs = with pkgs.buildPackages; with pkgs; [
            haskell.compiler.ghc983
            rustc
            cargo
            cargo-nextest
            pkg-config
          ];
          buildInputs = with pkgs; [ openssl clang gdb ghc ];
          shellHook = ''
            export LIBCLANG_PATH="${pkgs.llvmPackages.libclang.lib}/lib"
          '';
        };
        devShells.vm = vm.shell;
        packages.vm  = vm;
      });
}
