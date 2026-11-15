module

public import Silmaril.Wasm.Examples.JsonAccept.Thms
public import Silmaril.Wasm.Examples.JsonAccept.Instance.Defs
public import Silmaril.Wasm.Game.Accept.Export.Defs
public import Silmaril.Wasm.Game.SpecInst.Defs
import Silmaril.Proofs.Wasm.Examples.JsonAccept.Instance

/-! # The JSON-subset acceptor, instantiated and embedded

End-to-end statements about `prog` as a module instantiated by the specification and called by
a host. The host writes the input into the instance's memory and invokes the export `accept`
(`Silmaril.Wasm.Game.Accept.exportAccepted`), for every profile and every set of host relations:

* `isSpecInstance`: `prog` has a spec instance, so the embedding is not vacuous;
  `spec_instance_eq`: every spec instance is that one (`prepare?` by kernel evaluation);
* **`exportAccepted_subset_intText`**: every input some run of the embedding accepts (answers
  `1`) is an integer text, hence a JSON text (`exportAccepted_subset_json`);
* **`exportRejected_inter_intText`**: no run of the embedding rejects (answers `0`) an integer
  text. So among inputs on which `accept` returns, it accepts exactly the integer texts.

**Gap: termination.** The proofs are partial correctness. That every invocation *returns* is
not proved here, so the converse inclusion (`intText ⊆ exportAccepted`) is not established.
Proving it needs a total-correctness proof of the loop (`Silmaril.Wasm.Logic.Total`, a variant
`len - i`).
-/

@[expose] public section

namespace Silmaril.Wasm.Examples.JsonAccept

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Game
open Silmaril.Wasm.Game.Accept
open Silmaril.Wasm.Numerics (Profile)

/-- `prog` has a spec instance. -/
theorem isSpecInstance :
    IsSpecInstance prog specMT
      specInst
      specPrep.1 :=
  Silmaril.Proofs.Wasm.Examples.JsonAccept.isSpecInstance

/-- Every spec instance of `prog` is that one. -/
theorem spec_instance_eq {mt : CModuleType} {I : ScalarInstance} {c₀ : Config Nat}
    (hI : IsSpecInstance prog mt I c₀) :
    mt = specMT ∧
      c₀ = specPrep.1 :=
  Silmaril.Proofs.Wasm.Examples.JsonAccept.spec_instance_eq hI

/-- A run of the embedding answering `r` answers `1` iff the input is an integer text. -/
theorem exportAnswered_iff {P : Profile} {Hosts : Set (HostSemantics Nat)} {r : BitVec 32}
    {w : List UInt8} (hw : w ∈ exportAnswered P Hosts prog "accept" r) :
    (r = 1 ↔ w ∈ intText) :=
  Silmaril.Proofs.Wasm.Examples.JsonAccept.exportAnswered_iff hw

/-- **Soundness of the embedded acceptor**: what it accepts is an integer text. -/
theorem exportAccepted_subset_intText (P : Profile) (Hosts : Set (HostSemantics Nat)) :
    exportAccepted P Hosts prog "accept" ⊆ intText :=
  fun _ hw => (exportAnswered_iff hw).1 rfl

/-- **Soundness against JSON**: what the embedded acceptor accepts is a JSON text. -/
theorem exportAccepted_subset_json (P : Profile) (Hosts : Set (HostSemantics Nat))
    (q : Silmaril.Formats.JsonBytes.Profile) :
    exportAccepted P Hosts prog "accept" ⊆ Silmaril.Formats.JsonBytes.language q :=
  fun _ hw => intText_le_json q (exportAccepted_subset_intText P Hosts hw)

/-- **No false rejection on the subset**: no run of the embedding rejects an integer text. -/
theorem exportRejected_inter_intText (P : Profile) (Hosts : Set (HostSemantics Nat)) :
    exportRejected P Hosts prog "accept" ∩ intText = ∅ := by
  ext w
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hw, hi⟩
  exact absurd ((exportAnswered_iff hw).2 hi) (by decide)

end Silmaril.Wasm.Examples.JsonAccept
