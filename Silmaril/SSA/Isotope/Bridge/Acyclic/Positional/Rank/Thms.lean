module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Rank.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.RankRounds

/-! # Soundness and completeness of finite rank synthesis -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Rank

variable {n : Nat} (targets : Fin n → List (Fin n))

/-- Ranks produced by a successful check strictly decrease along local edges. -/
theorem check_sound (ok : check targets = true) {i j : Fin n} (edge : j ∈ targets i) :
    ((rounds targets n).get j).getD 0 < ((rounds targets n).get i).getD 0 :=
  check_sound_proof targets ok edge

/-- A bounded decreasing rank guarantees that all vertices are ranked within
the number of rounds used by the checker. -/
theorem check_complete (rank : Fin n → Nat)
    (decreases : ∀ i j, j ∈ targets i → rank j < rank i) (bounded : ∀ i, rank i < n) :
    check targets = true :=
  check_complete_proof targets rank decreases bounded

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Rank
