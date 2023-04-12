# pre-flake wrangling

# { pkgs ? import <nixpkgs> {} }:

# let 
#   # agda-stdlib = pkgs.agdaPackages.standard-library.overrideAttrs (oldAttrs: {
#   #   version = "90c2debd";
#   #   src = pkgs.fetchFromGitHub {
#   #     repo = "agda-stdlib";
#   #     owner = "agda";
#   #     rev = "90c2debd6bb8c42df2bdf3050ca1a2ede5679310";
#   #     hash = "sha256-KQL73o0Xkm3XjU1tf02S8CNj2OgXb8PeWJMUONTzVkg=";
#   #   };
#   # });
#   # generics = pkgs.agdaPackages.mkDerivation {
#   #   meta = {};
#   #   pname = "generics";
#   #   version = "1.0.0";
#   #   src = generics-src;
#   #   buildInputs = [ agda-stdlib ];
#   # };
#   # generics-src = pkgs.fetchFromGitHub {
#   #   repo = "generics";
#   #   owner = "cmcmA20";
#   #   rev = "6ee8ccbcc18b6582bb2bf95a173c12d952780105";
#   #   hash = "sha256-sgRzYrKEF9za1QXvArNufnfPViCncKtl9PGWD9/b57I=";
#   # };

#   cubical-mini-src = pkgs.fetchFromGitHub {
#     repo = "cubical-mini";
#     owner = "cmcmA20";
#     rev = "e3298d8e2daebe51eb8adfa8c29b054984ab31ac";
#     hash = "sha256-lh2Zyg+zBTp+mzE3PDZEmGqFYCrOB93vMKRoKiiEVFs=";
#   };
#   cubical-mini = pkgs.agdaPackages.mkDerivation {
#     meta = {};
#     pname = "cubical-mini";
#     version = "0.1";
#     src = cubical-mini-src;
#     buildInputs = [ ];
#   };
# in

# pkgs.mkShell {
#   nativeBuildInputs = [ 
#     # withPackages can eat a function that eats the attrset of (known) agda packages and outputs the list of pkgs to use
#     (pkgs.agda.withPackages ([ 
#       cubical-mini
#       # agda-stdlib
#       # generics
#     ]))
#   ];
# }

# flake compat
(import
  (
    let lock = builtins.fromJSON (builtins.readFile ./flake.lock); in
    fetchTarball {
      url = "https://github.com/edolstra/flake-compat/archive/${lock.nodes.flake-compat.locked.rev}.tar.gz";
      sha256 = lock.nodes.flake-compat.locked.narHash;
    }
  )
  { src = ./.; }
).defaultNix