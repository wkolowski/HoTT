{ pkgs ? import <nixpkgs> {} }:

let
  coq = pkgs.coq_8_20;
in

pkgs.stdenv.mkDerivation
{
  name = "HoTT";

  src = ./src;

  enableParallelBuilding = true;

  buildInputs =
  [
    coq
  ];

  buildPhase =
  ''
    patchShebangs build.sh
    ./build.sh
  '';

  installPhase =
  ''
    INSTALLPATH=$out/lib/coq/${coq.coq-version}/user-contrib/HoTT

    mkdir -p $INSTALLPATH

    find . -name "*.v" -o -name "*.vo" -o -name "*.glob" | xargs cp --parents -t $INSTALLPATH/
  '';
}
