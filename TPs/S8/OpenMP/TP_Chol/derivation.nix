{ pkgs ? import <nixpkgs> {} }:
pkgs.llvmPackages_13.libcxxStdenv.mkDerivation {
  name = "omp_test";
  src = ./.;
  buildInputs = [ pkgs.gcc pkgs.llvmPackages_13.openmp pkgs.gfortran pkgs.lapack pkgs.blas ];

  installPhase = ''
    make install PREFIX=$out
  '';
}
