{ pkgs ? import <nixpkgs> {} }:

let
  build =
  {
    coq = import ./src/default.nix { inherit pkgs; };
    tex = import ./notes/default.nix { inherit pkgs; };
  };
in

{
  coq = import ./src/shell.nix { inherit pkgs; };
  tex = import ./notes/shell.nix { inherit pkgs; };

  default = pkgs.mkShell
  {
    inputsFrom =
    [
      build.coq
      build.tex
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
      echo -e "''${GREEN}./build.sh''${RESET}       — Build the project"
      echo -e "''${GREEN}./src/build.sh''${RESET}   — Build the Coq development"
      echo -e "''${GREEN}./notes/build.sh''${RESET} — Build the notes to PDF"
      echo -e "''${GREEN}coqide''${RESET}           — Start CoqIDE"
    '';
  };
}
