import Silmaril.Containers.HttpOnce.Defs

/-!
Writes the OCI image layout of `Silmaril.Containers.HttpOnce` (the blobs whose digests
`Silmaril.Containers.HttpOnce.Thms` proves) into `layout/`, or, with `check`, compares the files there
with them. Usage, from the repository root:

    lake env lean --run examples/containers/http-once/Generate.lean          # write
    lake env lean --run examples/containers/http-once/Generate.lean check    # compare

`oci-layout`, `index.json` and Docker's `manifest.json` are not read by the Lean reader (it starts
from the manifest digest); they are what `docker load` needs.
-/

open Silmaril.Containers.HttpOnce

def hex (bs : List UInt8) : String := String.join (bs.map fun b =>
  String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)])

def files : List (String × List UInt8) :=
  [("oci-layout", Silmaril.Containers.Fixtures.ascii "{\"imageLayoutVersion\":\"1.0.0\"}"),
   ("index.json", Silmaril.Containers.Fixtures.ascii
     ("{\"schemaVersion\":2,\"mediaType\":\"application/vnd.oci.image.index.v1+json\",\"manifests\":[{\"mediaType\":\"application/vnd.oci.image.manifest.v1+json\",\"digest\":\"sha256:" ++
      hex manifestDigest ++ "\",\"size\":" ++ toString manifest.length ++
      ",\"annotations\":{\"org.opencontainers.image.ref.name\":\"silmaril-http-once:pinned\"}}]}")),
   ("manifest.json", Silmaril.Containers.Fixtures.ascii
     ("[{\"Config\":\"blobs/sha256/" ++ hex configDigest ++ "\",\"RepoTags\":[\"silmaril-http-once:pinned\"],\"Layers\":[\"blobs/sha256/" ++
      hex layerDigest ++ "\"]}]")),
   ("blobs/sha256/" ++ hex manifestDigest, manifest),
   ("blobs/sha256/" ++ hex configDigest, config),
   ("blobs/sha256/" ++ hex layerDigest, layer)]

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := "examples/containers/http-once/layout"
  let check := args == ["check"]
  let mut bad := 0
  for (name, bytes) in files do
    let path := root / name
    if check then
      let ok ← try
          pure ((← IO.FS.readBinFile path).toList == bytes)
        catch _ => pure false
      unless ok do
        IO.eprintln s!"differs: {path}"
        bad := bad + 1
    else
      if let some parent := path.parent then IO.FS.createDirAll parent
      IO.FS.writeBinFile path ⟨bytes.toArray⟩
      IO.println s!"wrote {path} ({bytes.length} octets)"
  return (if bad = 0 then 0 else 1)
