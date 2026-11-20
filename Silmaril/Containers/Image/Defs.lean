module

public import Silmaril.Containers.Cas.Defs
public import Silmaril.Net.Ip.Addr.Defs

/-!
# Container images: data models, levels of refinement, and shapes

**Experimental API** (`docs/projects/containers.md`): definitions and statements may change.

An image is described at three levels, each a refinement of the one above:

1. **Flat** (`Flat C`): a configuration and a root file tree whose files hold contents of an
   abstract type `C`. This is what a process sees when it starts, and it is the level at which
   preconditions are stated ("the file at the entry point is …").
2. **Layered** (`Layered D`): a manifest naming a configuration and a list of layers by digest
   `D`; each layer is a list of file changes whose files are again named by digest
   (whiteouts are `none`). Flattening (`Layered.flatten`) looks every digest up in content
   stores (`Silmaril.Containers.Cas.Store`) and applies the layers, lowest first. It fails when a
   blob is missing.
3. **Octets** (planned): the OCI image layout, manifests and configurations as JSON, layers as
   (compressed) tar streams, SHA-256 digests. A decoder from octets to level 2 and an
   integrity check (`Cas.Store.checked`) connect them; `Cas.Thms.sound_decode` is the step.

The file contents `C` are abstract. The fixtures use small programs as contents
(`Silmaril.Containers.Fixtures`); the intended refinement is octets read through the ELF
verification API (`Silmaril.Elf`), where facts about one file (its kind, `DT_NEEDED`, the
interpreter it names) are stated over the octets at a path of the flat tree.

**Shapes.** A shape (`Shape C P`) says how a runtime finds the program `P` it starts in a flat
image of contents `C`, and is the data-model variant a verification problem is posed in: a
single static executable at the entry point, a dynamically linked one with its interpreter and
libraries, a script and its interpreter, a WebAssembly module or component, or a general
distribution root file system. `ShapeKind` names the variants for tables; `Shape.entry` is the
single-file shape the fixtures use.

Not modelled here: file modes beyond "executable", ownership, symbolic-link resolution during
lookup, opaque whiteouts and the removal of a directory's children by a whiteout, hard links,
extended attributes, and platform selection from an image index.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers

open Silmaril.Containers.Cas

/-- A path inside an image: its components, from the root. -/
abbrev Path : Type := List String

/-- **A file-tree entry** whose files hold contents of type `C`. -/
inductive Entry (C : Type) where
  /-- A regular file with its content, and whether it is executable. -/
  | file (c : C) (exec : Bool)
  /-- A directory. -/
  | dir
  /-- A symbolic link to a path. -/
  | link (target : Path)
  deriving DecidableEq, Repr

/-- **A root file tree**: the entry at each path, if any. -/
abbrev Tree (C : Type) : Type := Path → Option (Entry C)

/-- **A layer**: entries set (`some`) or removed (`none`, a whiteout), in order. -/
abbrev Layer (C : Type) : Type := List (Path × Option (Entry C))

namespace Tree

variable {C : Type}

/-- The empty tree. -/
def empty : Tree C := fun _ => none

/-- One change applied to a tree. -/
def set (t : Tree C) (p : Path) (e : Option (Entry C)) : Tree C :=
  fun q => if q = p then e else t q

/-- A layer applied over a tree. -/
def apply (t : Tree C) (l : Layer C) : Tree C := l.foldl (fun t x => t.set x.1 x.2) t

/-- Layers applied over a tree, the lowest first. -/
def applyAll (t : Tree C) (ls : List (Layer C)) : Tree C := ls.foldl apply t

/-- The contents of a tree of digests, looked up in a store. An entry whose blob is missing is
missing. -/
def resolve {D : Type} (S : Store D C) (t : Tree D) : Tree C := fun p =>
  match t p with
  | some (.file d x) => (S d).map (fun c => .file c x)
  | some .dir => some .dir
  | some (.link q) => some (.link q)
  | none => none

/-- Every file of a tree of digests is in the store. -/
def Complete {D : Type} (S : Store D C) (t : Tree D) : Prop :=
  ∀ p d x, t p = some (.file d x) → (S d).isSome

end Tree

/-- Transport protocols a container can declare a port for. -/
inductive Proto where
  | tcp
  | udp
  deriving DecidableEq, Repr

/-- **A declared port** (`ExposedPorts` in an OCI configuration). -/
structure PortSpec where
  proto : Proto
  port : Silmaril.Net.Ip.Port
  deriving DecidableEq, Repr

/-- A port a service is meant to listen on: not 0, which asks the system for any free port. -/
def PortSpec.Valid (p : PortSpec) : Prop := p.port ≠ 0

instance (p : PortSpec) : Decidable p.Valid := inferInstanceAs (Decidable (_ ≠ _))

/-- **The runtime configuration of an image** (the parts of an OCI image configuration this
development uses). -/
structure Config where
  entrypoint : List String := []
  cmd : List String := []
  env : List (String × String) := []
  workdir : Path := []
  /-- The numeric user the process runs as; `none` is the runtime's default (often root). -/
  user : Option Nat := none
  exposed : List PortSpec := []
  deriving DecidableEq, Repr

/-- The argument vector a runtime starts with: entry point, then command. -/
def Config.argv (c : Config) : List String := c.entrypoint ++ c.cmd

/-- The characters of a path split at `/` (a structural definition, so that the kernel can
evaluate it on literals). -/
def splitSlash : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    let r := splitSlash cs
    if c = '/' then [] :: r else
      match r with
      | w :: ws => (c :: w) :: ws
      | [] => [[c]]

/-- A path string read as components: split at `/`, empty components dropped (so `/app` and
`app` are both `["app"]`; there is no working-directory resolution). -/
def Path.ofString (s : String) : Path :=
  ((splitSlash s.toList).filter (· ≠ [])).map String.ofList

/-- The path of the program a configuration starts: the first word of the argument vector. -/
def Config.entryPath (c : Config) : Option Path := c.argv.head?.map Path.ofString

/-- **A flat image**: a configuration and a root file tree of contents `C`. -/
structure Flat (C : Type) where
  config : Config
  root : Tree C

/-- **A manifest**: the digest of the configuration and of each layer, lowest first. -/
structure Manifest (D : Type) where
  config : D
  layers : List D
  deriving DecidableEq, Repr

/-- **The stores a layered image is read from**: configurations, layers (whose files are named
by digest) and file contents. A runtime reads them from a registry or a local cache. -/
structure Stores (D C : Type) where
  configs : Store D Config
  layers : Store D (Layer D)
  blobs : Store D C

/-- **A layered image**: a manifest, read from stores. -/
abbrev Layered (D : Type) : Type := Manifest D

/-- **Flattening**: the configuration and the layers by digest, the layers applied lowest
first, and the files looked up by digest. `none` when the configuration or a layer is missing;
a missing file blob makes that file missing (`Tree.Complete` says none is). -/
def Layered.flatten {D C : Type} (S : Stores D C) (m : Layered D) : Option (Flat C) := do
  let cfg ← S.configs m.config
  let ls ← m.layers.mapM S.layers
  pure ⟨cfg, (Tree.empty.applyAll ls).resolve S.blobs⟩

/-- The variants of image shape, as names for tables. -/
inductive ShapeKind where
  /-- One statically linked executable at the entry point (`FROM scratch`). -/
  | static
  /-- A dynamically linked executable with its interpreter (`PT_INTERP`) and `DT_NEEDED`
  libraries in the image. -/
  | dynamic
  /-- A script and the interpreter its `#!` line names. -/
  | script
  /-- A WebAssembly module or component run by a host in the image or by the runtime. -/
  | wasm
  /-- A general root file system (a distribution) with an arbitrary entry point. -/
  | distro
  deriving DecidableEq, Repr

/-- **A shape**: how a runtime finds the program it starts in a flat image (`none`: the image
does not have this shape, and the runtime refuses it). -/
structure Shape (C P : Type) where
  kind : ShapeKind
  program : Flat C → Option P

/-- **The entry-point shape**: the program is the content of the executable file at the
configured entry point, read by `dec`. -/
def Shape.entry {C P : Type} (kind : ShapeKind) (dec : C → Option P) : Shape C P where
  kind := kind
  program img := do
    let p ← img.config.entryPath
    match img.root p with
    | some (.file c true) => dec c
    | _ => none

end Silmaril.Containers
