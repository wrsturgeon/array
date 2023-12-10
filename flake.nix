{
  description =
    "Common array operations and useful properties, defined on Coq lists.";
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };
  outputs = { flake-utils, nixpkgs, self }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pname = "array";
        version = "0.0.1";
        os-pkgs = import nixpkgs { inherit system; };
        pkgs = os-pkgs.coqPackages;
      in {
        packages.default = pkgs.mkCoqDerivation {
          inherit pname version;
          src = ./.;
          owner = "wrsturgeon";
        };
      });
}
