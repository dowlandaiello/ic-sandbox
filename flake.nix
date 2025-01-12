{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.forEachDefaultSystem (system:
      let pkgs = nixpkgs.legacyPackages."${system}";
      in {
        shells.default = pkgs.mkShell {
          nativeBuildInputs = with pkgs.buildPackages; [
            rust-bin.stable.latest.default
            pkg-config
          ];
          buildInputs = with pkgs; [ openssl clang gdb ];
          shellHook = ''
            export LIBCLANG_PATH="${pkgs.llvmPackages.libclang.lib}/lib"
          '';
        };
      });
}
