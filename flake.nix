{
  description = "Proving the Coding Interview";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    parts.url = "github:hercules-ci/flake-parts";
  };
  outputs = { self, nixpkgs, parts }@inputs:
    parts.lib.mkFlake { inherit inputs; } {
      systems =
        [ "aarch64-linux" "aarch64-darwin" "x86_64-darwin" "x86_64-linux" ];
      imports = let
        buildInputs = pkgs:
          with pkgs; [
            pnpm
            typescript
            nodePackages.ts-node
            uv
            nodePackages.prettier
            nixfmt
            typst
            typstyle
          ];
        shell = { self, inputs, ... }: {
          perSystem = { config, self', inputs', pkgs, ... }: {
            devShells.default = pkgs.mkShell {
              name = "Proving the Coding Interview";
              buildInputs = buildInputs pkgs;
            };
          };
        };
      in [ shell ];
    };
}
