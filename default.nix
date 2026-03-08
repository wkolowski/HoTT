{ pkgs ? import <nixpkgs> {} }:

let
  coq = import ./src/default.nix { inherit pkgs; };
  tex = import ./notes/default.nix { inherit pkgs; };

  all = pkgs.symlinkJoin
  {
    name = "HoTT";

    paths =
    [
      coq
      tex
    ];
  };
in

{
  inherit coq tex all;

  default = all;
}