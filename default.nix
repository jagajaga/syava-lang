{ pkgs ? (import <nixpkgs> {}).pkgs }:

with pkgs;
with rustPlatform;

import ./project.nix {inherit rustPlatform;}
