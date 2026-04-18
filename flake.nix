{
  description = "Concrete Semantics";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    flake-parts.inputs.nixpkgs-lib.follows = "nixpkgs";
  };

  outputs = inputs@{ flake-parts, ... }: flake-parts.lib.mkFlake { inherit inputs; } {
    systems = [
      "x86_64-linux"
      "aarch64-darwin"
    ];

    perSystem = { pkgs, ... }: {
      devShells.default = pkgs.mkShell {
        buildInputs = [
          pkgs.isabelle
          pkgs.just
        ];
      };
    };
  };
}
