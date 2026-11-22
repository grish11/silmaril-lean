module

public import Silmaril.Wasm.Wac.Dasl.Codec.Thms
public import Silmaril.Formats.Dasl.Resolve.Thms
import Silmaril.Proofs.Wasm.Wac.Dasl

@[expose] public section

namespace Silmaril.Wasm.Wac.Dasl

open Silmaril.Formats.Dasl
open Silmaril.Semantics.Naming (Binding)

variable {Name : Type} {store : Store Name} {root : Name}

def ExpandedNames (store : Store Name) (root : Name) (value : Composition (Name × ByteArray)) : Prop :=
  ∃ tree, FullNames store root tree ∧ expanded.decode? tree = some value

theorem expansion_iff (value : Composition (Name × ByteArray)) :
    Expands store (shallow.encode value.names) (expanded.encode value) ↔
      ∀ row ∈ value.packages, store.blobs row.2.1 row.2.2 :=
  Proofs.Wasm.Wac.Dasl.expansion_iff value

theorem expanded_shallow (value : Composition (Name × ByteArray)) :
    (Named.embed (expanded.encode value)).shallow = shallow.encode value.names :=
  Proofs.Wasm.Wac.Dasl.expanded_shallow value

theorem full_iff (value : Composition (Name × ByteArray)) :
    FullNames store root (expanded.encode value) ↔
      store.objects root (shallow.encode value.names) ∧ ∀ row ∈ value.packages, store.blobs row.2.1 row.2.2 := by
  refine ⟨fun ⟨_, stored, hit⟩ => ?_, fun ⟨stored, hits⟩ => ⟨_, stored, (expansion_iff value).2 hits⟩⟩
  have view := (expanded_shallow value).symm.trans hit.shallow_eq
  exact ⟨view ▸ stored, (expansion_iff value).1 (view.symm ▸ hit)⟩

theorem expandedNames_binding (bound : store.Binding) : Binding (ExpandedNames store) := by
  rintro _ _ _ ⟨first, left, leftHit⟩ ⟨second, right, rightHit⟩
  exact Option.some.inj (leftHit.symm.trans (fullNames_binding bound left right ▸ rightHit))

theorem recovered (value : Composition (Name × ByteArray))
    (stored : store.objects root (shallow.encode value.names))
    (support : ∀ row ∈ value.packages, store.blobs row.2.1 row.2.2) : ExpandedNames store root value :=
  ⟨_, (full_iff value).2 ⟨stored, support⟩, expanded.recovers value⟩

end Silmaril.Wasm.Wac.Dasl
