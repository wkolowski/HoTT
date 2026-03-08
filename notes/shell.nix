{ pkgs ? import <nixpkgs> {} }:

let
  tex = import ./default.nix { inherit pkgs; };
in

pkgs.mkShell
{
  inputsFrom =
  [
    tex
  ];

  shellHook =
  ''
    GREEN="\033[1;32m"
    RESET="\033[0m"

    export PROJECT_ROOT=$(pwd)
    export PS1="\n\[''${GREEN}\]HoTT\''${PWD#\''$PROJECT_ROOT}>\[''${RESET}\] "

    echo ""
    echo -e "Homotopy Type Theory notes"
    echo ""
    echo -e "''${GREEN}./notes/build.sh''${RESET} — Build the notes to PDF"
  '';
}
