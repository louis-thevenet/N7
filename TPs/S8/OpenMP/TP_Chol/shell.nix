{ pkgs ? import <nixpkgs> {  } }:
let
  derivation = pkgs.callPackage ./derivation.nix {};
in
pkgs.stdenv.mkDerivation {
  name = "env-${derivation.name}";

  buildInputs = derivation.buildInputs ++  [ pkgs.clang-tools ];

  nativeBuildInputs = derivation.nativeBuildInputs;
}
