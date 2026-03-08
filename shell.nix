{ pkgs ? import <nixpkgs> {} }:

let
  coq = pkgs.coq_8_20;
  coqPackages = pkgs.coqPackages_8_20;
in

pkgs.mkShell
{
  buildInputs = with pkgs;
  [
    coq
    coqPackages.coqide
  ];

  shellHook =
  ''
    GREEN="\033[1;32m"
    RESET="\033[0m"

    export PROJECT_ROOT=$(pwd)
    export PS1="\n\[''${GREEN}\]HoTT\''${PWD#\''$PROJECT_ROOT}>\[''${RESET}\] "

    echo ""
    echo -e "Homotopy Type Theory in Coq"
    echo ""
    echo -e "''${GREEN}./src/build.sh''${RESET} — Regenerate the makefile, then build"
    echo -e "''${GREEN}make''${RESET}           — Build"
    echo -e "''${GREEN}make clean''${RESET}     — Clean build artifacts"
    echo -e "''${GREEN}coqide''${RESET}         — Start CoqIDE"
  '';
}
