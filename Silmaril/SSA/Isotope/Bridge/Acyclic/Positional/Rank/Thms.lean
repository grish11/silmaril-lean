module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Rank.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.RankRounds

/-! # Soundness and completeness of finite rank synthesis -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Rank

variable {n : Nat} (targets : Fin n → List (Fin n))

/-- Every listed entry target has a removal round. -/
theorem ranked_of_checkFrom {entry : List (Fin n)} (ok : checkFrom targets entry = true)
    {i : Fin n} (edge : i ∈ entry) : ((rounds targets n).get i).isSome = true :=
  List.all_eq_true.mp ok i edge

/-- A whole-table check suffices for every choice of entry targets. -/
theorem checkFrom_of_check (entry : List (Fin n)) (ok : check targets = true) :
    checkFrom targets entry = true :=
  List.all_eq_true.mpr fun i _ => ranked_of_checkFrom targets ok (List.mem_finRange i)

/-- Successors of a ranked row have strictly earlier removal rounds. -/
theorem ranked_successor {i j : Fin n} (hi : ((rounds targets n).get i).isSome = true)
    (edge : j ∈ targets i) :
    ((rounds targets n).get j).isSome = true ∧
      ((rounds targets n).get j).getD 0 < ((rounds targets n).get i).getD 0 :=
  ranked_successor_proof targets hi edge

/-- Ranks produced by a successful check strictly decrease along local edges. -/
theorem check_sound (ok : check targets = true) {i j : Fin n} (edge : j ∈ targets i) :
    ((rounds targets n).get j).getD 0 < ((rounds targets n).get i).getD 0 :=
  (ranked_successor targets (ranked_of_checkFrom targets ok (List.mem_finRange i)) edge).2

/-- The entry check is equivalent to a bounded decreasing rank on a successor-closed
set containing the entry targets. No rank is required outside that set. -/
theorem checkFrom_iff (entry : List (Fin n)) :
    checkFrom targets entry = true ↔
      ∃ (live : Fin n → Prop) (rank : Fin n → Nat),
        (∀ i ∈ entry, live i) ∧
        (∀ i j, live i → j ∈ targets i → live j ∧ rank j < rank i) ∧
        ∀ i, live i → rank i < n :=
  checkFrom_iff_proof targets entry

/-- A bounded decreasing rank guarantees that all vertices are ranked within
the number of rounds used by the checker. -/
theorem check_complete (rank : Fin n → Nat)
    (decreases : ∀ i j, j ∈ targets i → rank j < rank i) (bounded : ∀ i, rank i < n) :
    check targets = true :=
  check_complete_proof targets rank decreases bounded

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Rank
