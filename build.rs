// Copyright 2025 Signal Messenger, LLC
// SPDX-License-Identifier: AGPL-3.0-only

fn main() {
    let protos = ["src/proto/pq_ratchet.proto"];
    let mut prost_build = prost_build::Config::new();

    // Where prost emits the generated Rust.
    //
    // * Normal builds: the standard per-build `$OUT_DIR`
    // * Verification builds (`--features extraction`): `src/proto/generated/`.
    let out_dir = if std::env::var_os("CARGO_FEATURE_EXTRACTION").is_some() {
        let dir = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap())
            .join("src/proto/generated");
        std::fs::create_dir_all(&dir).unwrap();
        prost_build.out_dir(&dir);
        dir.to_str().unwrap().to_owned()
    } else {
        std::env::var("OUT_DIR").unwrap()
    };

    prost_build
        .compile_protos(&protos, &["src"])
        .expect("Protobufs in src are valid");

    // Gate as_str_name/from_str_name with #[cfg(not(feature = "extraction"))] — these
    // return &'static str which Aeneas cannot translate ("no bottoms in value" error),
    // and they are never called by spqr.
    let path = format!("{out_dir}/signal.proto.pq_ratchet.rs");
    let content = std::fs::read_to_string(&path).unwrap();
    let content = content
        .replace("pub fn as_str_name(", "#[cfg(not(feature = \"extraction\"))]\n        pub fn as_str_name(")
        .replace("pub fn from_str_name(", "#[cfg(not(feature = \"extraction\"))]\n        pub fn from_str_name(");
    std::fs::write(&path, content).unwrap();

    for proto in &protos {
        println!("cargo:rerun-if-changed={proto}");
    }
}
