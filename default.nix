{ pkgs ? (import <nixpkgs> {}).pkgs }:

with pkgs;
with rustUnstable;

import ./project.nix {inherit rustUnstable; inherit pkgs;}
