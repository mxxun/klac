{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell {
  nativeBuildInputs = [ 
    # withPackages can eat a function that eats the attrset of (known) agda packages and outputs the list of pkgs to use
    (pkgs.agda.withPackages (p: [ p.standard-library ]))
  ];
}
