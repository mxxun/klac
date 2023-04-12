# stolen & adapted from https://github.com/agda/cubical/blob/master/flake.nix

{
  description = "cubical-mini";

  inputs.nixpkgs.url = "nixpkgs/nixpkgs-unstable";
  inputs.flake-utils.url = "github:numtide/flake-utils";
  inputs.flake-compat = {
    url = "github:edolstra/flake-compat";
    flake = false;
  };
  inputs.agda = {
    url = "github:agda/agda/e4b6c53966b7c6a73ea573a1a7e6eb2572db2dce"; # nightly-2023-04-11
    inputs = {
      nixpkgs.follows = "nixpkgs";
      flake-utils.follows = "flake-utils";
    };
  };
  inputs.cubical-mini-src = {
    url = "github:cmcmA20/cubical-mini/e3298d8e2daebe51eb8adfa8c29b054984ab31ac"; # nightly-2023-04-11
    flake = false;
  };

  outputs = { self, flake-compat, flake-utils, nixpkgs, agda, cubical-mini-src }:
    let
      inherit (nixpkgs.lib) cleanSourceWith hasSuffix;
      overlay = final: prev: {
        cubical-mini = final.agdaPackages.mkDerivation rec {
          pname = "cubical"; # must agree with %name%.agda-lib in the repo root
          version = "0.1";

          src = cleanSourceWith {
            filter = name: type:
              !(hasSuffix ".nix" name)
            ;
            src = cubical-mini-src;
          };


          LC_ALL = "C.UTF-8";

          # The cubical library has several `Everything.agda` files, which are
          # compiled through the make file they provide.
          nativeBuildInputs = [ final.ghc ];
          buildPhase = ''
            make
          '';
          meta = {
            description = "An experimental wrangling of cubical-mini";
            homepage = "https://github.com/cmcmA20/cubical-mini";
            license = "MIT License";
          };
        };
        agdaWithCubical = final.agdaPackages.agda.withPackages [final.cubical-mini];
      };
      overlays = [ agda.overlay overlay ];
      
    in
    { overlays.default = overlay; } //
    # https://nixos.wiki/wiki/Flakes#Output_schema might be informative
    # https://github.com/numtide/flake-utils likewise
    flake-utils.lib.eachSystem [ "x86_64-linux" ] (system:
      let pkgs = import nixpkgs { inherit system overlays; };
      in rec {
        packages = with pkgs; rec {
          inherit cubical-mini agdaWithCubical;
          default = agdaWithCubical;
        };
        # makes `nix-shell` and `nix develop` have the right agda on path
        devShells.default = with pkgs; mkShell { 
          buildInputs = [ agdaWithCubical ]; 
        };
      });
}
