{ pkgs ? import <nixpkgs> {}, enableExecutableProfiling ? false}:
let
  hp = if enableExecutableProfiling
    then pkgs.haskellPackages.override {
      overrides = self: super: {
        mkDerivation = args: super.mkDerivation (args // {
          enableLibraryProfiling = true;
          });
        };
      }
    else pkgs.haskellPackages;
in
  hp.callPackage ./dynamical.nix {inherit enableExecutableProfiling;}
