{ pkgs ? import <nixpkgs> {} }:
pkgs.llvmPackages_13.libcxxStdenv.mkDerivation {
  name = "omp_tp2";
  src = ./.;
  buildInputs = [ pkgs.gcc pkgs.llvmPackages_13.openmp pkgs.gfortran pkgs.lapack pkgs.blas ];

  installPhase = ''
    make install PREFIX=$out
  '';
}
