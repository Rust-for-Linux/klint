{
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    treefmt-nix = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      nixpkgs,
      flake-utils,
      rust-overlay,
      treefmt-nix,
      ...
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        inherit (nixpkgs) lib;
        overlays = [ (import rust-overlay) ];
        pkgs = import nixpkgs {
          inherit system overlays;
        };

        toolchain = (builtins.fromTOML (builtins.readFile ./rust-toolchain.toml)).toolchain;
        rustc = pkgs.rust-bin.fromRustupToolchain toolchain;
      in
      {
        devShells.rustup = pkgs.mkShell {
          buildInputs = with pkgs; [ sqlite ];
          nativeBuildInputs = with pkgs; [ rustup ];
        };

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [ sqlite ];
          nativeBuildInputs = [
            (pkgs.rust-bin.fromRustupToolchain (
              toolchain // { components = toolchain.components ++ [ "rust-analyzer" ]; }
            ))
          ];
        };

        packages.default =
          (pkgs.rustPlatform.buildRustPackage.override {
            inherit rustc;
            cargo = rustc;
          })
            {
              pname = "klint";
              version = "0.1.0";

              src = lib.fileset.toSource {
                root = ./.;
                fileset = lib.fileset.unions [
                  ./Cargo.toml
                  ./Cargo.lock
                  ./build.rs
                  ./.cargo
                  ./src
                ];
              };
              cargoLock = {
                lockFile = ./Cargo.lock;
                outputHashes = {
                  "compiletest_rs-0.11.2" = "sha256-kjdqn9MggFypzB6SVWAsNqD21wZYiv+dtPvyGNi/Wqo=";
                };
              };

              buildInputs = with pkgs; [ sqlite ];
              doCheck = false;

              # If kernel rustdoc tests are enabled, user would need a matching version of rustdoc.
              # klint provides a klint-rustdoc binary to ease the process. However, for nix, we already
              # know the path to the rustdoc binary, so just symlink and replace the wrapper.
              postInstall = ''
                ln -sf "${lib.getExe' rustc "rustdoc"}" $out/bin/klint-rustdoc
              '';

              passthru.rustc = rustc;
            };

        apps = {
          latest-rustc = {
            type = "app";
            program = "${pkgs.writers.writeBash "latest-rustc" ''
              echo ${pkgs.rust-bin.nightly.latest.rustc.version} | grep -Po 'nightly.*'
            ''}";
          };

          update-rustc = {
            type = "app";
            program = "${pkgs.writers.writeBash "update-rustc" ''
              nix flake update
              sed -i "s/channel = .*/channel = \"$(nix run .#latest-rustc)\"/" rust-toolchain.toml
            ''}";
          };
        };

        formatter = (treefmt-nix.lib.evalModule pkgs ./treefmt.nix).config.build.wrapper;
      }
    );
}
