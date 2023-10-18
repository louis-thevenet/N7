{
  description = "A Nix flake dev environment for N7 assignements";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";

  outputs = {
    self,
    nixpkgs,
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
        packages = with pkgs; [
          # Modélisation
          coq
          coqPackages.coqide

          # PIM
          gnat

          # Utilitaires
          unzip
          vpnc
          filezilla
          x2goclient
        ];
      };
    });
  };
}
