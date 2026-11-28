module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Semantics.Erasure.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot
open LambdaSSA.Semantics.Categorical (ofMonadicTypeModel ofMonadicInstructionModel RegionTypingCoherent)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues typeModel)
open Isotope.Semantics (encodeValue encodeValue_injective InstructionModel)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance : AtomValues Empty := ⟨Empty.elim⟩
attribute [local instance] typeModel

private theorem typeModel_eq : ofMonadicTypeModel (τ := Ty Empty) = types := by
  unfold ofMonadicTypeModel LambdaSSA.Subtyping.Semantics.Categorical.exactTypeModel
    LetIter.ProofRelevant.Semantics.Categorical.ofTypeModel types
    LetIter.Semantics.Categorical.ofTypeModel
  congr 1
  exact Subsingleton.elim _ _

variable {m : Type → Type} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
  {P : InstrSig (Ty Empty) Bool}

theorem regionCoherent_proof (M : InstructionModel value P.Instr m)
    (pureM : InstructionModel.RespectsPure (ε := Bool) M) (bad : {X : Type} → m X) :
    letI := instructions M
    RegionTypingCoherent (Φ := P.Instr) (J (m := m)) types := by
  classical
  let _ : LetIter.ProofRelevant.Semantics.InstructionModel P.Instr (Ty Empty) Bool m :=
    ⟨M.eval, (fun f h => (pureM f h).choose), (fun f h x => (pureM f h).choose_spec x)⟩
  let F : Empty → Type := Empty.elim
  let raw (f : P.Instr) (x : Value (Sigma F)) : m (Value (Sigma F)) :=
    if h : ∃ a, encodeValue F (instrSrc f) a = x then
      M.eval f h.choose >>= fun y => pure (encodeValue F (instrTrg f) y)
    else bad
  have compatible (f : P.Instr) (x : value (instrSrc f)) :
      raw f (encodeValue F (instrSrc f) x) =
        (M.eval f x >>= fun y => pure (encodeValue F (instrTrg f) y)) := by
    let h : ∃ a, encodeValue F (instrSrc f) a = encodeValue F (instrSrc f) x := ⟨x, rfl⟩
    unfold raw
    rw [dite_eq_left h, encodeValue_injective F _ h.choose_spec]
  have coherent := LambdaSSA.Semantics.Erasure.regionTypingCoherent
    (κ := Empty) (m := m) raw bad bad compatible
  let Types := LetIter.Semantics.Categorical.TypeModel (Ty Empty) Type
  let Instr (T : Types) := LetIter.Semantics.Categorical.InstructionModel (J (m := m)) T P.Instr
  let arrow {T : Types} (I : Instr T) (f : P.Instr) :=
    LetIter.Semantics.Categorical.InstructionModel.denote (self := I) f
  let coherentModel (T : Types) (I : Instr T) :=
    letI _ : LetIter.Semantics.Categorical.InstructionModel (J (m := m)) T P.Instr := I
    RegionTypingCoherent (Φ := P.Instr) (J (m := m)) T
  have transport {T U : Types} (e : T = U) (I : Instr T) (K : Instr U)
      (same : ∀ f, HEq (arrow I f) (arrow K f))
      (h : coherentModel T I) : coherentModel U K := by
    cases e
    have eq : I = K := by
      cases I
      cases K
      congr 1
      funext f
      exact eq_of_heq (same f)
    cases eq
    exact h
  exact transport typeModel_eq (ofMonadicInstructionModel (τ := Ty Empty) (ε := Bool) (m := m))
    (instructions M) (fun _ => HEq.rfl) coherent

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli
