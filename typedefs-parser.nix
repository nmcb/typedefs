{ stdenv, pkgs, idrisPackages }:

let
  build-idris-package = pkgs.callPackage ./.build-idris-package.nix {};
  tparsec = pkgs.callPackage ./.tparsec.nix {
    inherit build-idris-package;
  };
  typedefs = pkgs.callPackage ./typedefs.nix { };
in

build-idris-package {
  name = "typedefs-parser";
  version = "dev";
  src = ./.;

  idrisDeps = with idrisPackages; [
    typedefs
  ];

  postInstall = ''
    install -D typedefs_parser $out/bin/typedefs-parser
  '';

  meta = {
    description = "Programming language agnostic type construction language based on polynomials - parser";
    homepage = "http://typedefs.com";
  };
}
