{ pkgs ? import <nixpkgs> { } }:

with pkgs;

mkShell rec {
  nativeBuildInputs = [ cargo rustc ];
  buildInputs =
    [ tikzit (pkgs.texlive.combine { inherit (pkgs.texlive) scheme-full tikz-inet tikz-ext; }) ];
}
