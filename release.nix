let
  pkgs = import <nixpkgs> {};
  craneSource = fetchTarball "https://github.com/ipetkov/crane/archive/refs/tags/v0.23.1.tar.gz";

  targets = [
    "gnu64"
    "musl64"
    "aarch64-multiplatform"
    "aarch64-multiplatform-musl"
    "mingwW64"
    # "x86_64-openbsd"
    # "x86_64-darwin"
    # "aarch64-darwin"
  ];

  build = crossAttr:
    let
      crossPkgs = pkgs.pkgsCross.${crossAttr};
      craneLib = import craneSource { pkgs = crossPkgs; };
      endsWith = path: ext: builtins.match ".*\.${ext}$" path != null;
      allowedExts = ["c" "h" "json" "egg"];
      pathAllowed = path: builtins.any (endsWith path) allowedExts;
      srcFilter = path: type: (pathAllowed path) || (craneLib.filterCargoSources path type);
    in
      craneLib.buildPackage {
        NIX_OUTPATH_USED_AS_RANDOM_SEED = "aaaaaaaaaa";
        pname = "saturn-v";
        pnameSuffix = crossAttr;
        doCheck = false;
        nativeBuildInputs = with crossPkgs; [
          rustPlatform.bindgenHook
        ];

        src = pkgs.lib.cleanSourceWith {
          src = ./.;
          filter = srcFilter;
        };
      };

in pkgs.lib.genAttrs targets build
