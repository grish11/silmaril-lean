module

public import Silmaril.Crypto.Interface.Defs

/-!
# Content-addressed stores: digests, contents and integrity

**Experimental API** (`docs/projects/containers.md`): definitions and statements may change.

A container image names everything it contains by digest: the manifest names the configuration
and the layers, and a runtime fetches each blob from a registry or a local store by that name.
This module separates three things that are easy to conflate:

* **a store** (`Store D C`): a partial map from digests `D` to contents `C`. Nothing about a
  store says that its contents have anything to do with their names;
* **integrity** (`Store.Sound h S`): every content the store returns hashes, under `h`, to the
  digest it was asked for. This is what a runtime establishes by *checking* a pulled blob
  (`Store.checked`), not something the digest establishes by itself;
* **binding** (`Store.InjOn h P`): on the contents `P` under consideration, `h` has no
  collisions, so a digest determines at most one content. For SHA-256 this is a computational
  assumption (collision resistance) that this library does not state as a theorem or an axiom
  (see `Silmaril.Crypto.HashFn`); results that need it take it as an explicit hypothesis.

So "the image is `sha256:…`" proves nothing about the bytes a runtime executes unless the
runtime checked integrity (`Sound`) *and* one assumes the hash binds (`InjOn`). Both appear as
hypotheses in `Thms.agree_of_sound`, and `Thms.digest_not_binding` shows that integrity alone
does not pin contents down.

**Refinement to bytes.** Abstract contents (a layer as a list of file changes, a parsed
configuration) are related to the octets a registry serves by a decoder (`Store.decode`): if the
byte store is sound for `h` and the decoder is left-inverse to an encoder, the decoded store is
sound for `h ∘ encode` (`Thms.sound_decode`). The OCI instance (SHA-256 over the canonical
octets of a blob, tar layers, JSON manifests) is planned (docs/projects/containers.md).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Containers.Cas

/-- **A content-addressed store**: the content a digest names, if the store has it. -/
abbrev Store (D C : Type) : Type := D → Option C

namespace Store

variable {D C C' : Type}

/-- The empty store. -/
def empty : Store D C := fun _ => none

/-- The store with `c` under the digest `d`, and `S` elsewhere. -/
def insert [DecidableEq D] (S : Store D C) (d : D) (c : C) : Store D C :=
  fun d' => if d' = d then some c else S d'

/-- The store with `c` under its own digest `h c`. -/
def put [DecidableEq D] (h : C → D) (S : Store D C) (c : C) : Store D C := S.insert (h c) c

/-- `S ≤ T`: every blob of `S` is in `T`, with the same content. -/
def Le (S T : Store D C) : Prop := ∀ d c, S d = some c → T d = some c

/-- `c` is in the store, under some digest. -/
def Holds (S : Store D C) (c : C) : Prop := ∃ d, S d = some c

/-- **Integrity**: every content the store returns hashes to the digest that named it. -/
def Sound (h : C → D) (S : Store D C) : Prop := ∀ d c, S d = some c → h c = d

/-- **Binding**: `h` has no collisions on the contents `P`. For a cryptographic hash this is an
assumption about the contents at hand, never a theorem. -/
def InjOn (h : C → D) (P : C → Prop) : Prop :=
  ∀ c₁ c₂, P c₁ → P c₂ → h c₁ = h c₂ → c₁ = c₂

/-- **The checked store**: what a runtime that verifies each blob before use returns. A blob
whose hash is not its digest is treated as missing. -/
def checked [DecidableEq D] (h : C → D) (S : Store D C) : Store D C :=
  fun d => match S d with
    | some c => if h c = d then some c else none
    | none => none

/-- The store read through a decoder: contents that do not decode are missing. -/
def decode (S : Store D C) (dec : C → Option C') : Store D C' := fun d => (S d).bind dec

/-- Byte stores: digests and contents are octet strings, as in OCI. -/
abbrev Bytes : Type := List UInt8

/-- **Integrity for a byte hash** (`Silmaril.Crypto.HashFn`, for example SHA-256). -/
def Verified (H : Silmaril.Crypto.HashFn) (S : Store Bytes Bytes) : Prop := Sound H.hash S

end Store

end Silmaril.Containers.Cas
