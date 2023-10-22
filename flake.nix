{
  description = "A Nix flake dev environment for N7 assignements (Matlab, Coq, Gnat, X2GO, ...)";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs = {
    self,
    nixpkgs,
    nix-matlab,
  }: let
    supportedSystems = ["x86_64-linux"];
    forEachSupportedSystem = f:
      nixpkgs.lib.genAttrs supportedSystems (system:
        f {
          pkgs = import nixpkgs {inherit system;};
        });
  in {
    devShells = forEachSupportedSystem ({pkgs}: {
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
    });
  };
}
