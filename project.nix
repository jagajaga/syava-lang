{ rustPlatform }:
with rustPlatform;

buildRustPackage rec {
  name = "holmes";
  src  = ./.;
  buildInputs = [ ];
  depsSha256 = "";
}
