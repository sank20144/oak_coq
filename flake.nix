{
  description = "A very basic flake";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }: (
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        packages = {
          oak_coq = pkgs.coqPackages.callPackage  ({ coq, stdenv }: pkgs.coqPackages.mkCoqDerivation {
            pname = "oak_coq";
            useDune = true;
            src = ./oak_coq;
            buildInputs = [
              pkgs.coqPackages.stdpp
              pkgs.coqPackages.coq-lsp
            ];
          }) {};
        };
      }
    )
  );
}
