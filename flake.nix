{
  description = "A Nix flake dev environment for N7 assignements (Matlab, Coq, Gnat, X2GO, ...)";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
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
        {
          devShells.default = pkgs.mkShell {
            #   # Matlab (needs a working matlab install elsewhere, see https://gitlab.com/doronbehar/nix-matlab)
            #   shellHook = nix-matlab.shellHooksCommon;
            #   buildInputs = with nix-matlab.packages.x86_64-linux; [
            #     matlab
            #     matlab-mlint
            #     matlab-mex
            #   ];

            packages = with pkgs; [
              # Nix
              nil
              alejandra

              # Typst
              typst
              tinymist
              typst-fmt

              # # Modélisation
              # opam # il faut installer les packages why3-coq, why3
              # # et run : eval $(opam env)
              # autoconf
              # pkg-config
              # gtk3
              # gtksourceview
              # coqPackages.coqide
              # coq
              # # PIM (Ada)
              # gnat
              # gprbuild
              # valgrind
              # gdb
              # hyperfine

              # # C
              # python310Packages.jupyter-c-kernel
              # jupyter
              # cmake
              # clang-tools

              # # Apprentissage (il manque des modules, je conseille pas de l'utiliser)
              (pkgs.python3.withPackages (python-pkgs: [
                python-pkgs.pytest
                # python-pkgs.jupyter
                # python-pkgs.numpy
                # python-pkgs.matplotlib
                # python-pkgs.scikit-learn
                # python-pkgs.tensorflow
                # python-pkgs.keras
                # python-pkgs.treelib
              ]))

              # # Arduino (needs aditionnal udev rules:
              # # see https://github.com/louis-thevenet/nixos-config/blob/67c87176c875801dd2a65a699189bd9959da4837/hosts/hircine/default.nix#L70C1-L75C6)
              # arduino-core
              # arduino-ide

              # # Java
              # jdk23

              # OCaml
              ocaml
              dune_3
              ocamlPackages.ocamlbuild
              ocamlPackages.utop
              ocamlPackages.ocamlformat
              ocamlPackages.menhir
              ocamlPackages.graphics
              ocamlPackages.ppx_inline_test
              ocamlPackages.ppx_expect

              # # Julia
              # julia_19

              # # Recherche opérationnelle
              # glpk

              # Systèmes de transition
              tlaplus
              tlaps
              tlaplusToolbox
              texliveSmall

              # OpenMP
              clang
              openblas
              gfortran
              hyperfine

              # Web
              tomcat
              jdk17

              # Prolog
              swi-prolog
              gprolog

              # Utilitaires
              unzip
              vpnc
              filezilla
              x2goclient
            ];
          };
        };
    };
}
