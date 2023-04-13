{ inputs, cell }:

let
  inherit (cell) library;
in

library.haskell-nix.haskellLib.parseIndexState (builtins.readFile (inputs.self + "/cabal.project"))
