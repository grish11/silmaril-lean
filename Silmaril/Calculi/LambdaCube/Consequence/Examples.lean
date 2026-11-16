module

public import Silmaril.Calculi.LambdaCube.Consequence.Thms
public import Silmaril.Calculi.LambdaCube.STLC.Defs

/-!
# Lambda-cube judgements as consequence systems: examples

* `admissible c`: the one-model semantics whose model satisfies exactly the judgements derivable
  at `c`. Its `seq` is **admissibility**: `Js ⊢ j` iff `j` is derivable whenever every judgement
  of `Js` is. At the dependent corner `Corner.cc` it is a semantics in the sense of `Semantics`
  (sound by construction) without any model construction.
* Theoremhood is below admissibility; admissibility is reflexive while theoremhood need not be.
* The STLC set institution (`STLC.institution`, over signatures) gives `institutionSeq`, a
  translation of `Sen* ⊢ Sen` along each signature morphism.
-/

@[expose] public section

namespace Silmaril.Calculi.LambdaCube.ConsequenceExamples

open CategoryTheory Silmaril.Consequence

/-- The one-model semantics of derivability at a corner. -/
def admissible (c : Corner) : Semantics c where
  Model := Discrete PUnit
  sat _ j := j.Derivable c
  sound hj _ := hj

theorem admissible_seq_iff (c : Corner) (Js : List PTSJudgment) (j : PTSJudgment) :
    (admissible c).seq Js j ↔ ((∀ k ∈ Js, k.Derivable c) → j.Derivable c) :=
  ⟨fun h hk => h ⟨⟨⟩⟩ hk, fun h _ hk => h hk⟩

example (j : PTSJudgment) : (admissible Corner.cc).seq [j] j :=
  (admissible Corner.cc).seq_closed.refl trivial (List.mem_singleton_self j)

example : derivableSys Corner.cc ≤ (admissible Corner.cc).seq := derivableSys_le_seq _

example : derivableSys Corner.lambdaP ≤ derivableSys Corner.cc := derivableSys_mono ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

example {S S' : Silmaril.Calculi.TypedLambda.Signature} (σ : S ⟶ S') :
    Translation (roomSeq (STLC.institution.obj S)) (roomSeq (STLC.institution.obj S')) :=
  institutionSeq STLC.institution σ

end Silmaril.Calculi.LambdaCube.ConsequenceExamples
