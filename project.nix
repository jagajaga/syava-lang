{ rustUnstable, pkgs }:
with rustUnstable;
with pkgs;

buildRustPackage rec {
  name = "syava-lang";
  src  = ./.;
  buildInputs = [ ncurses zlib ];
  depsSha256 = "1wmd5b7hvszsdakjd4iy9zy0nj1a3j1mdynln0a8amai7176vhg7";
}
