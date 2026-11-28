module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Pass.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (Program)
open AddPhi.Rotate.Pair.Dispatch.Materialize (suffix)
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse
open AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (word)
open Silmaril.SSA.SeaOfNodes.Pure.RightIdentityPass (wordProducers)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Program inputs sigs [word]}

theorem find_none_iff :
    findRepresentative? p = none ↔ ∀ rep : EntryAdd p, check p rep = false := by
  rw [findRepresentative?, List.find?_eq_none]
  constructor
  · intro missed rep
    have listed : rep ∈ wordProducers p.diamond.shared :=
      List.mem_filterMap.mpr ⟨⟨word, rep⟩, Silmaril.SSA.SeaOfNodes.GVN.Pass.mem_candidates rep, rfl⟩
    exact Bool.eq_false_of_not_eq_true (missed rep listed)
  · intro missed rep _
    simp [missed rep]

theorem rewrite_none_iff :
    discoverAndRewrite? p = none ↔ ∀ rep : EntryAdd p, rewrite? p rep = none := by
  constructor
  · intro missed rep
    cases nominated : rewrite? p rep with
    | none => rfl
    | some target =>
      obtain ⟨value, shape, checked, _⟩ := rewrite?_eq_some_iff.mp nominated
      cases found : findRepresentative? p with
      | none => simp [find_none_iff.mp found rep] at checked
      | some first =>
        have firstChecked : check p first = true := List.find?_some found
        have rewritten : rewrite? p first = some (emit p first value) :=
          rewrite?_eq_some_iff.mpr ⟨value, shape, firstChecked, rfl⟩
        simp [discoverAndRewrite?, found, rewritten] at missed
  · intro missed
    cases found : findRepresentative? p <;> simp [discoverAndRewrite?, found, missed]

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.EntryReuse.Discovery
