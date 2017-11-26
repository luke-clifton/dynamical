{ mkDerivation, lib, base, Chart, Chart-cairo, Chart-diagrams
, containers, data-default-class, deepseq, ghc-prim, linear, mtl
, scientific, stable-memo, stdenv, time, vector, llvm_37, enableExecutableProfiling ? false
}:
mkDerivation {
  pname = "dynamical";
  version = "0.0.0.1";
  src = ./.;
  isLibrary = true;
  isExecutable = true;
  libraryHaskellDepends = [
    base Chart Chart-cairo Chart-diagrams containers data-default-class
    deepseq ghc-prim linear mtl scientific stable-memo time vector
  ];
  executableHaskellDepends = [ base data-default-class ];
  buildDepends = [llvm_37];
  description = "FRP based simulation of dynamical systems";
  license = stdenv.lib.licenses.bsd3;
  configureFlags = lib.optionals enableExecutableProfiling ["--enable-executable-profiling"];
}
