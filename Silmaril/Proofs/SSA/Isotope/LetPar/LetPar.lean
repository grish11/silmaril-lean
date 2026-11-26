module

public import Silmaril.SSA.Isotope.LetPar.Native.Defs
public import Silmaril.SSA.Isotope.LetPar.Structural.Thms
public import Silmaril.Raw.SSA.Isotope.LetSeq.LocallyNameless.Equiv
public import Silmaril.Raw.SSA.Isotope.LetSeq.Semantics.Monadic

@[expose] public section

namespace Silmaril.Isotope.LetPar.Proofs

open Parallel Semantics

universe u v w q r

variable {ν : Type v} {Φ : Type w} {n m : Nat}

theorem embed_injective : Function.Injective (embed : LetSeq.LocallyNameless.Tm ν Φ n → Tm ν Φ n) := by
  intro a
  induction a <;> intro b eq <;> cases b <;> simp_all [embed] <;> grind

theorem embed_rename (ρ : Fin n → Fin m) (t : LetSeq.LocallyNameless.Tm ν Φ n) :
    embed (t.rename ρ) = (embed t).rename ρ := by
  induction t generalizing m <;> simp [embed, LetSeq.LocallyNameless.Tm.rename,
    Parallel.Tm.rename, *] <;> rfl

theorem embed_upSub (σ : Fin n → LetSeq.LocallyNameless.Tm ν Φ m) :
    (fun i => embed (LetSeq.LocallyNameless.Tm.upSub σ i)) =
      Parallel.Tm.upSub (fun i => embed (σ i)) := by
  funext i
  exact Fin.cases rfl (fun j => embed_rename Fin.succ (σ j)) i

theorem embed_bsubst (σ : Fin n → LetSeq.LocallyNameless.Tm ν Φ m) (t : LetSeq.LocallyNameless.Tm ν Φ n) :
    embed (t.bsubst σ) = (embed t).bsubst (fun i => embed (σ i)) := by
  induction t generalizing m <;> simp [embed, LetSeq.LocallyNameless.Tm.bsubst,
    Parallel.Tm.bsubst, embed_upSub, *]

theorem embed_instantiate (b : LetSeq.LocallyNameless.Tm ν Φ (n + 1))
    (a : LetSeq.LocallyNameless.Tm ν Φ n) :
    embed (b.instantiate a) = (embed b).instantiate (embed a) := by
  rw [LetSeq.LocallyNameless.Tm.instantiate, embed_bsubst, Parallel.Tm.instantiate]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem embed_pure {ε : Type r} [HasEff Φ ε] {pureEff : ε} {t : LetSeq.LocallyNameless.Tm ν Φ n}
    (h : LetSeq.LocallyNameless.Pure pureEff t) : Parallel.Pure pureEff (embed t) := by
  induction h with
  | fv => exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op hf ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb

variable {τ : Type u} [HasProduct τ] [HasUnit τ] [DecidableEq ν] [HasTy Φ τ]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ} {t : LetSeq.LocallyNameless.Tm ν Φ n}

theorem embed_hasType (h : LetSeq.LocallyNameless.HasType Φ Γ β t A) :
    Parallel.HasType Φ Γ β (embed t) A := by
  exact (LetSeq.LocallyNameless.Derivation.ofHasType h).map derivation

variable {ε : Type r} [HasEff Φ ε] {pureEff : ε}

omit [DecidableEq ν] in
theorem embed_seqRule {a b : LetSeq.LocallyNameless.Tm ν Φ n}
    (h : LetSeq.LocallyNameless.CoreAxiom pureEff a b) :
    SeqRule pureEff (embed a) (embed b) := by
  cases h with
  | structural h =>
    cases h with
    | letBeta hp =>
      simp only [embed, embed_instantiate]
      exact (.letBeta (embed_pure hp))
    | letEta => exact (.letEta _)
    | unitEta => exact (.unitEta _)
    | pairEta => exact (.pairEta _)
    | pairBeta =>
      simp only [embed, LetSeq.LocallyNameless.Tm.lift, embed_rename]
      exact (.pairBeta _ _ _)
  | sequencing h =>
    cases h with
    | bindOp =>
      simp only [embed, LetSeq.LocallyNameless.Tm.underBinder, embed_rename]
      exact (.bindOp _ _)
    | bindLet =>
      simp only [embed, LetSeq.LocallyNameless.Tm.underBinder, embed_rename]
      exact (.bindLet _ _ _)
    | bindLetPair =>
      simp only [embed, LetSeq.LocallyNameless.Tm.underBinder, embed_rename]
      exact (.bindLetPair _ _ _)
    | bindPair =>
      simp only [embed, LetSeq.LocallyNameless.Tm.underTwoBinders, embed_rename]
      exact (.bindPair _ _)

theorem embed_equiv {b : LetSeq.LocallyNameless.Tm ν Φ n}
    (h : LetSeq.LocallyNameless.Equiv pureEff Γ β t b A) :
    LetPar.Equiv pureEff Γ β (embed t) (embed b) A := by
  induction h with
  | refl h => exact .refl (embed_hasType h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .refl ⟨.unit⟩
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | ax hr ha hb => exact .seqRule (embed_seqRule hr) (embed_hasType ha) (embed_hasType hb)

theorem denote_derivation (D : τ → Type q) [ProductModel D] [UnitModel D]
    {m : Type q → Type q} [Monad m] (M : InstructionModel D Φ m) (P : ParOp m)
    (d : LetSeq.LocallyNameless.Derivation Φ Γ β t A) (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (derivation d).denote D M P (Control.seq D m) γ ρ = d.denote D M γ ρ := by
  induction d with
  | fv | bv | unit => rfl
  | op _ ih =>
    simp only [derivation, embed, Parallel.Derivation.denote, LetSeq.LocallyNameless.Derivation.denote, ih]
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb =>
    simp only [derivation, embed, Parallel.Derivation.denote,
      LetSeq.LocallyNameless.Derivation.denote, iha, ihb]

end Silmaril.Isotope.LetPar.Proofs
