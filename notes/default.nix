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
        babel-polish
        lh              # OT4 font encoding for Polish
        cm-super
        polski

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
