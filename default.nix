{ pkgs ? import <nixpkgs> {} 
}:
pkgs.mkShell {
  name = "dev";
  buildInputs = [
    pkgs.coq_8_9
  ];
}
