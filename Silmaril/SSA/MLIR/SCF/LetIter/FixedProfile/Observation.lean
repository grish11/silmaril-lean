module

public import Silmaril.SSA.MLIR.SCF.LetIter.FixedProfile.Native

/-! # Returns and divergence of the two fixed-profile presentations -/

@[expose] public section

namespace Silmaril.MLIR.SCF.LetIter.FixedProfile

open CategoryTheory
open Silmaril.MLIR.Arith (Env)
open Silmaril.MLIR.Pure (Eval)
open Silmaril.Isotope
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.Institution.Observational (Observation iterBeh iterBeh_eq_of_obs)

variable {P : Profile} {S T : Signature}

private def canonicalBody (test : Before P S) (next : After P S) : Term P S .body :=
  .case (.op (.before test) (.bv 0)) (.inl (.bv 0)) (.inr (.op (.yield next) (.bv 0)))

private def canonical : (k : Phase) → Decoded P S k → Term P S k
  | .initializer, args => .op (.init args) .unit
  | .condition, code => .op (.before code) (.bv 0)
  | .yield, code => .op (.yield code) (.bv 0)
  | .parent, code => .op (.parent code) (.bv 0)
  | .body, (test, next) => canonicalBody test next
  | .loop, (args, test, next) => .iter (.op (.init args) .unit) (canonicalBody test next)
  | .program, p => (encode p).val

/-- Erasing identity wires preserves native returns, faults, and divergence
before specializing to a pure scalar model. -/
private theorem Grammar.obs_decode {k : Phase} {term : Term P S k} (h : Grammar P S k term) :
    Tm.Obs.{0, 0, 0, 0} term (canonical k h.decode) := by
  induction h with
  | initializer | condition | yield | parent => exact .refl _
  | branch _ _ test next => exact test.case (.refl _) next.inr
  | iterate _ _ init body => exact init.iter body
  | sequence _ _ loop parent => exact loop.let₁ parent
  | wire _ ih => exact (obs_letEta _).trans ih

/-- How the typed data extracted at a phase changes under opcode relabelling. -/
def Decoded.rename (f : S ⟶ T) : (k : Phase) → Decoded P S k → Decoded P T k
  | .initializer, args => args
  | .condition, code => renameCode f code
  | .yield, code => renameCode f code
  | .parent, code => renameCode f code
  | .body, code => (renameCode f code.1, renameCode f code.2)
  | .loop, code => (code.1, renameCode f code.2.1, renameCode f code.2.2)
  | .program, p => Scalar.rename f p

/-- The derivation decoder commutes with the native instruction map. -/
theorem Grammar.decode_rename (f : S ⟶ T) {k : Phase} {term : Term P S k} (h : Grammar P S k term) :
    (h.rename f).decode = Decoded.rename f k h.decode := by
  induction h with
  | initializer | condition | yield | parent => rfl
  | branch _ _ ihTest ihNext =>
      simp only [Grammar.rename, Grammar.decode, Decoded.rename, ihTest, ihNext]
  | iterate _ _ ihInit ihBody =>
      simp [Grammar.rename, Grammar.decode, Decoded.rename, ihInit, ihBody]
  | sequence _ _ ihLoop ihParent =>
      simp [Grammar.rename, Grammar.decode, Decoded.rename, Scalar.rename, ihLoop, ihParent]
  | wire _ ih => exact ih

/-- Observable results at the fixed typed interface. -/
inductive Answer (P : Profile) where
  | ret (result : Env P.result)
  | diverge

/-- SCF observations come directly from the independent scalar evaluator. -/
def Scalar.observe (p : Scalar P S) (M : Eval S.op) (input : Env P.input) : Set (Answer P) :=
  {a | match a with
    | .ret result => ∃ fuel, p.toWhile.run M fuel input = some result
    | .diverge => p.toWhile.Diverges M input}

/-- Full native observations before projecting answers to the typed result interface. -/
def Native.beh (p : Native P S) (M : Eval S.op) (input : Env P.input) :=
  iterBeh (ScalarWhile.model M input) p.val

/-- Native observations from actual LetIter semantics in the chosen scalar model. -/
def Native.observe (p : Native P S) (M : Eval S.op) (input : Env P.input) : Set (Answer P) :=
  {a | match a with
    | .ret result => Observation.ret () (.atom (.result result)) () ∈ p.beh M input
    | .diverge => Observation.diverge () ∈ p.beh M input}

theorem Scalar.observe_rename (f : S ⟶ T) (p : Scalar P S) (M : Eval T.op) (input : Env P.input) :
    (p.rename f).observe M input = p.observe (reduct f M) input := by
  ext a
  cases a with
  | ret result =>
      change (∃ fuel, (p.rename f).toWhile.run M fuel input = some result) ↔
        (∃ fuel, p.toWhile.run (reduct f M) fuel input = some result)
      simp only [p.run_rename]
  | diverge =>
      change (∀ fuel, (p.rename f).toWhile.run M fuel input = none) ↔
        (∀ fuel, p.toWhile.run (reduct f M) fuel input = none)
      simp only [p.run_rename]

/-- The existing checked lowering compares the independent observations. -/
theorem observe_encode (p : Scalar P S) (M : Eval S.op) (input : Env P.input) :
    (encode p).observe M input = p.observe M input := by
  ext o
  cases o with
  | ret result =>
      change Observation.ret () (.atom (.result result)) () ∈ ScalarWhile.observe p.toWhile M input ↔
        ∃ fuel, p.toWhile.run M fuel input = some result
      rw [ScalarWhile.returns_iff]
      constructor
      · rintro ⟨other, heq, run⟩
        cases heq
        exact run
      · intro run
        exact ⟨result, rfl, run⟩
  | diverge => exact ScalarWhile.diverges_iff p.toWhile M input

private theorem beh_of_derivation (p : Native P S) (h : Grammar P S .program p.val)
    (M : Eval S.op) (input : Env P.input) :
    p.beh M input = ScalarWhile.observe h.decode.toWhile M input :=
  iterBeh_eq_of_obs h.obs_decode (ScalarWhile.model M input)

/-- The typed observations agree with the program decoded from any admission derivation. -/
theorem observe_of_derivation (p : Native P S) (h : Grammar P S .program p.val)
    (M : Eval S.op) (input : Env P.input) :
    p.observe M input = h.decode.observe M input := by
  rw [← observe_encode]
  ext o
  cases o <;>
    simp only [Native.observe, Set.mem_ofPred_eq, beh_of_derivation p h M input]
  all_goals rfl

/-- Decoding an admitted native term preserves and reflects the typed observations. -/
theorem observe_decode (p : Native P S) (M : Eval S.op) (input : Env P.input) :
    p.decode.observe M input = p.observe M input :=
  (observe_of_derivation p (Classical.choice p.property) M input).symm

/-- Every return is a typed result vector. The observation vocabulary loses no native returns. -/
theorem Native.ret_iff (p : Native P S) (M : Eval S.op) (input : Env P.input)
    (out : Value (ScalarWhile.Atom P.state P.payload P.result)) :
    Observation.ret () out () ∈ p.beh M input ↔
      ∃ result, out = .atom (.result result) ∧ ∃ fuel, p.decode.toWhile.run M fuel input = some result := by
  rw [beh_of_derivation p (Classical.choice p.property) M input]
  exact ScalarWhile.returns_iff p.decode.toWhile M input out

/-- The admitted scalar models and wiring have no native faults. -/
theorem Native.no_fault (p : Native P S) (M : Eval S.op) (input : Env P.input) :
    Observation.fault () () ∉ p.beh M input := by
  rw [beh_of_derivation p (Classical.choice p.property) M input]
  exact ScalarWhile.no_fault p.decode.toWhile M input

/-- The typed answer set is complete for all native observations in the scalar model. -/
theorem Native.observe_eq_iff_beh_eq (p q : Native P S) (M : Eval S.op) (input : Env P.input) :
    p.observe M input = q.observe M input ↔ p.beh M input = q.beh M input := by
  constructor
  · intro h
    refine Observation.set_eq_iff.mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨⟩ value ⟨⟩
      constructor
      · intro ret
        obtain ⟨result, rfl, _⟩ := (p.ret_iff M input value).mp ret
        exact (Set.ext_iff.mp h (.ret result)).mp ret
      · intro ret
        obtain ⟨result, rfl, _⟩ := (q.ret_iff M input value).mp ret
        exact (Set.ext_iff.mp h (.ret result)).mpr ret
    · rintro ⟨⟩ ⟨⟩
      exact ⟨fun fault => (p.no_fault M input fault).elim, fun fault => (q.no_fault M input fault).elim⟩
    · rintro ⟨⟩
      exact Set.ext_iff.mp h .diverge
  · intro h
    ext answer
    cases answer <;> simp only [Native.observe, Set.mem_ofPred_eq, h]

/-- Native reindexing agrees with reduct, derived using its relabelled admission derivation. -/
theorem Native.observe_rename (f : S ⟶ T) (p : Native P S) (M : Eval T.op) (input : Env P.input) :
    (p.rename f).observe M input = p.observe (reduct f M) input := by
  let h := Classical.choice p.property
  calc
    (p.rename f).observe M input = (h.rename f).decode.observe M input :=
      observe_of_derivation (p.rename f) (h.rename f) M input
    _ = (h.decode.rename f).observe M input :=
      congrArg (fun q : Scalar P T => q.observe M input) (Grammar.decode_rename f h)
    _ = h.decode.observe (reduct f M) input := Scalar.observe_rename f h.decode M input
    _ = p.observe (reduct f M) input := (observe_of_derivation p h (reduct f M) input).symm

end Silmaril.MLIR.SCF.LetIter.FixedProfile
