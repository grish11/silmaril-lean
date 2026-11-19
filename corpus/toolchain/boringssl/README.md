# BoringSSL toolchain extension

This separate image adds CMake 3.31.6-2, Ninja 1.12.1-1 and official Go 1.27.4 to the unchanged standard corpus toolchain. The pinned BoringSSL checkout requires Go >=1.27.0; its shared FIPS configuration uses Go integrity tooling. These tools do not establish FIPS validation or certification.

Run `bash corpus/toolchain/boringssl/image.sh /absolute/inventory/output` after building the standard image. The script uses its immutable local image ID as the parent, host networking and bounded per-build resources. Debian packages come from the parent's 20251103 snapshot; the Go archive is SHA256 checked in the Dockerfile.

`image.json` records the actual successful image and parent IDs. `lock.txt` contains all 220 installed packages, including the exact unchanged 210-package base. `tools.json` records executable hashes and versions; `go-tree.sha256` covers every file in the installed Go tree. Image filesystem IDs may differ on independent rebuilds, so artifact receipts must record their actual image IDs and compare complete installed locks in both workers before compiling.

The image was built successfully and inventory was copied from a never-started container. This change contains no BoringSSL corpus artifacts. Artifact recipes/builds are a separate contribution.
