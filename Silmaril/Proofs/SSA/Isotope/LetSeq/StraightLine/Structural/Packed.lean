module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Coverage
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Environment
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Replay
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Separation
import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms
import Silmaril.SSA.Isotope.LetCase.AbortSequence.Thms

import Silmaril.SSA.Isotope.LetSeq.StraightLine.Binders.Thms

public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural

open LocallyNameless (Derivation Equiv HasType Tm)
open Silmaril.Isotope.Semantics (BoundEnv InstructionModel)
open scoped Structural

variable {α Φ : Type} [Signature α Φ]
open Binders

set_option backward.isDefEq.respectTransparency false

private def packedSubst (s : Shape α) : AssemblyEnv (Packed s) (packedUnpack s).context :=
  Fin.cases (packedUnpack s).value (fun i => i.elim0)

private theorem packed_eta {s : Shape α} {t : Term Φ 1} {A : Ty α}
    (d : Derivation Φ Γ₀ (Packed s) t A) :
    Equiv false Γ₀ (Packed s) t ((packedUnpack s).split.wrap (t.bsubst (packedSubst s).terms)) A := by
  let intoBinder : Fin 1 → Fin 2 := fun _ => 0
  let p := packedUnpack s
  have kt : HasType Φ Γ₀ ((Packed s).snoc s.ty) (t.rename intoBinder) A :=
    d.toHasType.renameAlong (ρ := intoBinder) (Fin.cases rfl (fun i => i.elim0))
  have inputType : HasType Φ Γ₀ (Packed s) (.bv 0) s.ty := .bv
  have enter := Equiv.letBeta (pureEff := false) .bv inputType kt
  have enter_subst : Tm.instantiate (t.rename intoBinder) (.bv (0 : Fin 1)) = t := by
    rw [Tm.instantiate, Tm.bsubst_rename]
    exact (Tm.bsubst_congr (Fin.cases rfl (fun i => i.elim0)) t).trans (Tm.bsubst_id t)
  rw [enter_subst] at enter
  have unpack := Equiv.let₁ (unpack_eta (Φ := Φ) s (β := Packed s) ⟨0, rfl⟩) (.refl kt)
  have across := p.split.bind p.value.derivation kt
  have beta := Equiv.letBeta p.value.pure p.value.derivation.toHasType (kt.rename (p.split.rename.up s.ty))
  have beta_subst : Tm.instantiate ((t.rename intoBinder).rename (Tm.up p.split.rename.toFun)) p.value.term =
      t.bsubst (packedSubst s).terms := by
    rw [instantiate_renamed, Tm.bsubst_rename]
    exact Tm.bsubst_congr (Fin.cases rfl (fun i => i.elim0)) t
  change Equiv false Γ₀ p.context _ (Tm.instantiate
    ((t.rename intoBinder).rename (Tm.up p.split.rename.toFun)) p.value.term) A at beta
  rw [beta_subst] at beta
  exact enter.symm.trans (unpack.trans (across.trans (p.split.congr beta)))

theorem normalize_packed_proof {s : Shape α} {t : Term Φ 1} {A : Ty α}
    (d : Derivation Φ Γ₀ (Packed s) t A) :
    ∃ u : Term Φ (packedUnpack s).size, ∃ _ : Normal (packedUnpack s).context u A,
      Equiv false Γ₀ (Packed s) t ((packedUnpack s).split.wrap u) A := by
  obtain ⟨u, p, replay⟩ := normalize_exact_proof d (packedSubst s)
  exact ⟨u, p, (packed_eta d).trans ((packedUnpack s).split.congr replay)⟩

private theorem model_respectsPure : InstructionModel.RespectsPure (ε := Bool) (model (α := α) (Φ := Φ)) := by
  intro f h
  cases h

theorem sound [DecidableEq α] {n : Nat} {β : Context α n} {t u : Term Φ n} {A : Ty α}
    (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A) (h : Equiv false Γ₀ β t u A)
    (ρ : BoundEnv Value β) : run d ρ = run e ρ := by
  let d' := Morphism.SeqCase.derivation d
  let e' := Morphism.SeqCase.derivation e
  have eq := Morphism.SeqCase.embed_equiv h
  have abort : LetCase.LocallyNameless.AbortEquiv false Γ₀ β
      (Morphism.SeqCase.embed t) (Morphism.SeqCase.embed u) A := .equiv eq
  have sound := LetIter.Semantics.Categorical.denote_eq_of_abortEquiv_nil (fun _ : α => Nat)
    model model_respectsPure abort.toLetIter (Morphism.CaseIter.derivation d') (Morphism.CaseIter.derivation e') ρ
  simpa only [d', e', Morphism.CaseIter.denote_derivation, Morphism.SeqCase.denote_derivation, run] using sound

omit [Signature α Φ] in
private theorem packed_separates (s : Shape α) :
    Separates ((packedUnpack s).split.env (packedEnv s (s.fresh 0))) (Set.Iio s.leaves) := by
  let empty : BoundEnv (Value (α := α)) (.nil : Context α 0) := fun i => i.elim0
  have separates : Separates empty (Set.Iio 0) :=
    ⟨fun _ i => i.1.elim0, fun _ i => i.1.elim0⟩
  simpa only [Nat.zero_add, packedUnpack, packedEnv, empty] using fresh_after separates s

theorem packed_reflect_proof [DecidableEq α] {s : Shape α} {t u : Term Φ 1} {A : Ty α}
    (d : Derivation Φ Γ₀ (Packed s) t A) (e : Derivation Φ Γ₀ (Packed s) u A) :
    run d (packedEnv s (s.fresh 0)) = run e (packedEnv s (s.fresh 0)) ↔
      Equiv false Γ₀ (Packed s) t u A := by
  let p := packedUnpack s
  let ρ := packedEnv s (s.fresh 0)
  refine ⟨fun equal => ?_, fun h => sound d e h ρ⟩
  obtain ⟨t', nt, ht⟩ := normalize_packed_proof d
  obtain ⟨u', nu, hu⟩ := normalize_packed_proof e
  rw [sound d (p.split.derivation nt.derivation) ht ρ,
    sound e (p.split.derivation nu.derivation) hu ρ, run_split, run_split] at equal
  have same := normal_eq_of_run nt nu (p.split.env ρ) s.leaves (packed_separates s) equal
  rw [same] at ht
  exact ht.trans hu.symm

end Silmaril.Isotope.LetSeq.StraightLine.Structural
