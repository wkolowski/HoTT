{ pkgs ? import <nixpkgs> {} }:

let
  coq = import ./default.nix { inherit pkgs; };
in

pkgs.mkShell
{
  inputsFrom =
  [
    coq
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
