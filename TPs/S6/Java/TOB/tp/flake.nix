{
  description = "A Nix flake dev environment for Java development";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = {
    self,
    nixpkgs,
    flake-utils,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      pkgs = nixpkgs.legacyPackages.${system};
    in {
      devShells = {
        default = pkgs.mkShell {
          shellHook = "export CLASSPATH=./junit4.jar:.";
          packages = with pkgs; [
            # Nix
            nil
            alejandra

            # Typst
            typst
            typst-lsp
            #typst-fmt

            # Java
            jdk21
          ];
        };
      };
    });
}
