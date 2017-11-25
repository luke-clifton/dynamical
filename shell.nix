{ nixpkgs ? import <nixpkgs> {}}:
let
  inherit (nixpkgs) pkgs;
  dynamical = pkgs.haskellPackages.callPackage ./dynamical.nix {};
in
  dynamical.env
