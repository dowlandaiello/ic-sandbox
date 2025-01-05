{ pkgs ? import <nixpkgs> {
  overlays = [
    (import (builtins.fetchTarball
      "https://github.com/oxalica/rust-overlay/archive/master.tar.gz"))
  ];
} }:
pkgs.mkShell {
  nativeBuildInputs = with pkgs.buildPackages; [
    rust-bin.stable.latest.default
    pkg-config
    capnproto
  ];
  buildInputs = with pkgs; [ openssl clang capnproto ];
  shellHook = ''
  export LIBCLANG_PATH="${pkgs.llvmPackages.libclang.lib}/lib"
  '';
}
