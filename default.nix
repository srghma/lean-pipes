{
  pkgs ? import <nixpkgs> { },
}:

pkgs.stdenv.mkDerivation {
  pname = "libcanonical";
  version = "0.1.0";

  src = /home/srghma/projects/lean-pipes/.lake/packages/Canonical/.lake/build/lib;

  nativeBuildInputs = [
    pkgs.autoPatchelfHook
  ];

  buildInputs = [
    pkgs.glibc
    pkgs.stdenv.cc.cc.lib # Provides libm.so.6, libpthread.so.0, etc.
  ];

  installPhase = ''
    mkdir -p $out/lib
    cp libCanonical.so $out/lib/
  '';
}
