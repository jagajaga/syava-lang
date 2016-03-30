{ rustUnstable, pkgs }:
with rustUnstable;
with pkgs;

buildRustPackage rec {
  name = "syava-lang";
  src  = ./.;
  buildInputs = [ ncurses zlib ];
  depsSha256 = "0fg52a59ssr69q4xk8hq2nmhb4j1f7cmr598qn6hc531cb60pnfh";
}
