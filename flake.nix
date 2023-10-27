{
  description = "A Nix flake dev environment for N7 assignements (Matlab, Coq, Gnat, X2GO, ...)";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    nix-matlab.url = "gitlab:doronbehar/nix-matlab";
  };
  outputs = {
    self,
    nixpkgs,
    flake-utils,
    nix-matlab,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells = {
        default = pkgs.mkShell {
          # Matlab
          buildInputs = with nix-matlab.packages.x86_64-linux; [
            matlab
            matlab-mlint
            matlab-mex
          ];
          shellHook = nix-matlab.shellHooksCommon;

          packages = with pkgs; [
            # Modélisation
            coq
            coqPackages.coqide

            # PIM
            gnat
            gprbuild

            # Utilitaires
            unzip
            vpnc
            filezilla
            typst
            typst-lsp
            typst-fmt
            x2goclient
          ];
        };
      };
    });
}
