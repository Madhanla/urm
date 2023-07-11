# file
let
  pkgs = import <nixpkgs> {
    overlays = [overlayTFG];
  };

  overlayTFG = (nixSelf: nixSuper: {
    myHaskellPackages = nixSelf.haskellPackages.override (oldHaskellPkgs: {
      overrides = nixSelf.lib.composeExtensions (oldHaskellPkgs.overrides or (_:_: {})) haskellOverlay;
    });
  });

  haskellOverlay = (hSelf: hSuper: {
    TFG = hSelf.callCabal2nix "TFG" ./. {};
  });

  myDevTools = with pkgs; [
    # general dev tools
    git
    ripgrep # rg: fast alternative to grep
    # haskell tools
    cabal-install # terminal app cabal
    # ghc # Haskell compiler
    haskellPackages.ghcid # code checker
    haskellPackages.hoogle
    haskellPackages.haskell-language-server
    haskellPackages.hlint
    haskellPackages.ormolu
  ];

  myShellHook = ''
   alias repl="cabal new-repl"
 '';

in
pkgs.myHaskellPackages.TFG.env.overrideAttrs (oldEnv: {
  nativeBuildInputs = oldEnv.nativeBuildInputs ++ myDevTools;
  shellHook = myShellHook;
})
