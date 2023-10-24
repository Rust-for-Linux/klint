{pkgs ? import <nixpkgs> {}}:
pkgs.mkShell {
  buildInputs = with pkgs; [sqlite];
  nativeBuildInputs = with pkgs; [rustup];
}
