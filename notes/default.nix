{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation
{
  name = "HoTT";

  src = pkgs.lib.cleanSource ./.;

  nativeBuildInputs = with pkgs;
  [
    (texlive.combine
    {
      inherit (texlive)
        scheme-small

        # Build tool.
        latexmk
        ;
    })
  ];

  buildPhase =
  ''
    patchShebangs build.sh
    ./build.sh
  '';

  installPhase =
  ''
    INSTALLPATH=$out/share/pdf/

    mkdir -p $INSTALLPATH
    cp *.pdf $INSTALLPATH/
  '';
}
