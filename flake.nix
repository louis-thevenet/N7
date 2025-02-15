{
  description = "A Nix flake dev environment for N7 assignements (Matlab, Coq, Gnat, X2GO, ...)";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    nixpkgs-old.url = "github:NixOS/nixpkgs/c407032be28ca2236f45c49cfb2b8b3885294f7f";

    flake-parts.url = "github:hercules-ci/flake-parts";
    systems.url = "github:nix-systems/default";

    nix-matlab.url = "gitlab:doronbehar/nix-matlab";
  };
  outputs =
    inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      systems = import inputs.systems;
      perSystem =
        {
          config,
          self',
          pkgs,
          lib,
          system,
          ...
        }:
        let
          base = with pkgs; [
            nixd
            tinymist
            typstyle

          ];
          utils = with pkgs; [

            unzip
            vpnc
            filezilla
            x2goclient
          ];
          modelisation = with pkgs; [
            opam # il faut installer les packages why3-coq, why3
            # et run : eval $(opam env)
            autoconf
            pkg-config
            gtk3
            gtksourceview
            coqPackages.coqide
            coq
          ];
          pim = with pkgs; [
            gnat
            gprbuild
            valgrind
            gdb
            hyperfine
          ];
          c = with pkgs; [
            python310Packages.jupyter-c-kernel
            jupyter
            cmake
            clang-tools
          ];
          apprentissage = with pkgs; [

            (pkgs.python3.withPackages (python-pkgs: [
              python-pkgs.pytest
              python-pkgs.jupyter
              python-pkgs.numpy
              python-pkgs.matplotlib
              python-pkgs.scikit-learn
              python-pkgs.tensorflow
              python-pkgs.keras
              python-pkgs.treelib
            ]))
          ];
          java = with pkgs; [
            jdk21
          ];
          arduino = with pkgs; [
            # Arduino (needs aditionnal udev rules:
            # see https://github.com/louis-thevenet/nixos-config/blob/67c87176c875801dd2a65a699189bd9959da4837/hosts/hircine/default.nix#L70C1-L75C6)
            arduino-core
            arduino-ide
          ];
          ocaml = with pkgs.nixpkgs-ocaml-old; [
            ocaml
            dune_2
            ocamlPackages.utop
            ocamlPackages.ocamlformat
            ocamlPackages.menhir
            ocamlPackages.ppx_inline_test
            ocamlPackages.ppx_expect
          ];
          julia = with pkgs; [
            julia_19
          ];
          ro = with pkgs; [
            glpk
          ];
          sys-transitions = with pkgs; [
            tlaplus
            tlaps
            tlaplusToolbox
            texliveSmall
          ];
          web = with pkgs; [
            tomcat
            jdk17
          ];
        in
        {
          _module.args.pkgs = import inputs.nixpkgs {
            inherit system;
            overlays = [
              (final: prev: {
                nixpkgs-ocaml-old = (
                  import inputs.nixpkgs-old {
                    system = system;
                  }
                );
              })
            ];
          };
          devShells.default = pkgs.mkShell {
            #   # Matlab (needs a working matlab install elsewhere, see https://gitlab.com/doronbehar/nix-matlab)
            #   shellHook = nix-matlab.shellHooksCommon;
            #   buildInputs = with nix-matlab.packages.x86_64-linux; [
            #     matlab
            #     matlab-mlint
            #     matlab-mex
            #   ];

            packages = base ++ utils ++ ocaml ++ sys-transitions ++ web;
          };
        };
    };
}
