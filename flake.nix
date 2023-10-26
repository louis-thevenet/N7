{
  description = "A Nix flake dev environment for N7 assignements (Matlab, Coq, Gnat, X2GO, ...)";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    nix-matlab = {
      url = "gitlab:doronbehar/nix-matlab";
    };
  };
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
          opam # il faut installer les packages why3-coq, why3
          # et run : eval $(opam env)
          autoconf
          pkg-config
          gtk3
          gtksourceview
          coqPackages.coqide
          coq
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
