module

public import Silmaril.SSA.Isotope.LetParCase.Defs
public import Silmaril.SSA.Isotope.LetPar.Thms
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Equiv
public import Silmaril.Raw.SSA.Isotope.LetCase.Semantics.Monadic
public import Silmaril.Raw.SSA.Isotope.Morphism.SeqCase.Monadic

@[expose] public section

namespace Silmaril.Isotope.LetParCase.Proofs

open Parallel Semantics

universe u v w q r

variable {ν : Type v} {Φ : Type w} {n m : Nat}

theorem embed_injective : Function.Injective (embed : LetCase.LocallyNameless.Tm ν Φ n → Tm ν Φ n) := by
  intro a
  induction a <;> intro b eq <;> cases b <;> simp_all [embed] <;> grind

theorem embed_rename (ρ : Fin n → Fin m) (t : LetCase.LocallyNameless.Tm ν Φ n) :
    embed (t.rename ρ) = (embed t).rename ρ := by
  induction t generalizing m <;> simp [embed, LetCase.LocallyNameless.Tm.rename,
    Parallel.Tm.rename, *] <;> first | rfl | exact ⟨rfl, rfl⟩

theorem embed_upSub (σ : Fin n → LetCase.LocallyNameless.Tm ν Φ m) :
    (fun i => embed (LetCase.LocallyNameless.Tm.upSub σ i)) =
      Parallel.Tm.upSub (fun i => embed (σ i)) := by
  funext i
  exact Fin.cases rfl (fun j => embed_rename Fin.succ (σ j)) i

theorem embed_bsubst (σ : Fin n → LetCase.LocallyNameless.Tm ν Φ m) (t : LetCase.LocallyNameless.Tm ν Φ n) :
    embed (t.bsubst σ) = (embed t).bsubst (fun i => embed (σ i)) := by
  induction t generalizing m <;> simp [embed, LetCase.LocallyNameless.Tm.bsubst,
    Parallel.Tm.bsubst, embed_upSub, *]

theorem embed_instantiate (b : LetCase.LocallyNameless.Tm ν Φ (n + 1))
    (a : LetCase.LocallyNameless.Tm ν Φ n) :
    embed (b.instantiate a) = (embed b).instantiate (embed a) := by
  rw [LetCase.LocallyNameless.Tm.instantiate, embed_bsubst, Parallel.Tm.instantiate]
  congr 1
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem embed_pure {ε : Type r} [HasEff Φ ε] {pureEff : ε} {t : LetCase.LocallyNameless.Tm ν Φ n}
    (h : LetCase.LocallyNameless.Pure pureEff t) : Parallel.Pure pureEff (embed t) := by
  induction h with
  | fv => exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op hf ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih

theorem embed_seqCase (t : LetSeq.LocallyNameless.Tm ν Φ n) :
    embed (Morphism.SeqCase.embed t) = ofLetPar (LetPar.embed t) := by
  induction t <;> simp [embed, Morphism.SeqCase.embed, ofLetPar, Parallel.Tm.widen, LetPar.embed, *]

theorem ofLetPar_injective : Function.Injective (ofLetPar : LetPar.Tm ν Φ n → Tm ν Φ n) := by
  exact Parallel.Tm.widen_injective Tier.seqCase

variable {τ : Type u} [TypeFormers τ] [DecidableEq ν] [HasTy Φ τ]
  {Γ : Ctx ν τ} {β : BoundCtx τ n} {A : τ} {t : LetCase.LocallyNameless.Tm ν Φ n}

theorem embed_hasType (h : LetCase.LocallyNameless.HasType Φ Γ β t A) :
    Parallel.HasType Φ Γ β (embed t) A := by
  exact (LetCase.LocallyNameless.Derivation.ofHasType h).map derivation

variable {ε : Type r} [HasEff Φ ε] {pureEff : ε}

omit [DecidableEq ν] in
theorem embed_seqRule {a b : LetCase.LocallyNameless.Tm ν Φ n}
    (h : LetCase.LocallyNameless.CoreAxiom pureEff a b) :
    SeqRule pureEff (embed a) (embed b) ∨ CaseRule pureEff (embed a) (embed b) := by
  cases h with
  | structural h =>
    cases h with
    | letBeta hp =>
      simp only [embed, embed_instantiate]
      exact Or.inl (.letBeta (embed_pure hp))
    | letEta => exact Or.inl (.letEta _)
    | unitEta => exact Or.inl (.unitEta _)
    | pairEta => exact Or.inl (.pairEta _)
    | pairBeta =>
      simp only [embed, LetCase.LocallyNameless.Tm.lift, embed_rename]
      exact Or.inl (.pairBeta _ _ _)
    | caseBetaL => exact .inr (.betaL hasCase _ _ _)
    | caseBetaR => exact .inr (.betaR hasCase _ _ _)
    | caseEta => exact .inr (.eta hasCase _)
    | emptyInitial => exact .inr (.emptyInitial hasCase _ _ _)
  | sequencing h =>
    cases h with
    | bindOp =>
      simp only [embed, LetCase.LocallyNameless.Tm.underBinder, embed_rename]
      exact Or.inl (.bindOp _ _)
    | bindLet =>
      simp only [embed, LetCase.LocallyNameless.Tm.underBinder, embed_rename]
      exact Or.inl (.bindLet _ _ _)
    | bindLetPair =>
      simp only [embed, LetCase.LocallyNameless.Tm.underBinder, embed_rename]
      exact Or.inl (.bindLetPair _ _ _)
    | bindPair =>
      simp only [embed, LetCase.LocallyNameless.Tm.underTwoBinders, embed_rename]
      exact Or.inl (.bindPair _ _)
    | bindLetCase =>
      simp only [embed, LetCase.LocallyNameless.Tm.underBinder, embed_rename]
      exact Or.inr (.bindLetCase hasCase _ _ _ _)
    | bindCase =>
      simp only [embed, LetCase.LocallyNameless.Tm.underBinder, embed_rename]
      exact Or.inr (.bindCase hasCase _ _ _)

theorem embed_equiv {b : LetCase.LocallyNameless.Tm ν Φ n}
    (h : LetCase.LocallyNameless.Equiv pureEff Γ β t b A) :
    LetParCase.Equiv pureEff Γ β (embed t) (embed b) A := by
  induction h with
  | refl h => exact .refl (embed_hasType h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .refl ⟨.unit⟩
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih
  | ax hr ha hb =>
    rcases embed_seqRule hr with hs | hc
    · exact .seqRule hs (embed_hasType ha) (embed_hasType hb)
    · exact .extraRule hc (embed_hasType ha) (embed_hasType hb)

theorem denote_derivation (D : τ → Type q) [ProductModel D] [UnitModel D] [CoproductModel D] [EmptyModel D]
    {m : Type q → Type q} [Monad m] (M : InstructionModel D Φ m) (P : ParOp m)
    (d : LetCase.LocallyNameless.Derivation Φ Γ β t A) (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (derivation d).denote D M P (Control.case D m) γ ρ = d.denote D M γ ρ := by
  induction d with
  | fv | bv | unit => rfl
  | op _ ih =>
    simp only [derivation, embed, Parallel.Derivation.denote, LetCase.LocallyNameless.Derivation.denote, ih]
  | let₁ _ _ iha ihb | pair _ _ iha ihb | let₂ _ _ iha ihb =>
    simp only [derivation, embed, Parallel.Derivation.denote,
      LetCase.LocallyNameless.Derivation.denote, iha, ihb]
  | inl _ ih | inr _ ih =>
    simp only [derivation, embed, Parallel.Derivation.denote,
      LetCase.LocallyNameless.Derivation.denote, ih]
    rfl
  | abort _ ih =>
    simp only [derivation, embed, Parallel.Derivation.denote,
      LetCase.LocallyNameless.Derivation.denote]
    congr 1
    exact ih ρ
  | case _ _ _ ihe ihl ihr =>
    simp only [derivation, embed, Parallel.Derivation.denote,
      LetCase.LocallyNameless.Derivation.denote, ihl, ihr]
    congr 1
    exact ihe ρ

variable {a b : LetPar.Tm ν Φ n}

theorem ofLetPar_hasType (h : Parallel.HasType Φ Γ β a A) :
    Parallel.HasType Φ Γ β (ofLetPar a) A := by
  exact h.map ofLetParDerivation

omit [DecidableEq ν] in
theorem ofLetPar_seqRule (h : SeqRule pureEff a b) :
    SeqRule pureEff (ofLetPar a) (ofLetPar b) := by
  cases h with
  | letBeta hp =>
    simp only [ofLetPar, Parallel.Tm.widen, Parallel.Tm.widen_instantiate]
    exact .letBeta (hp.widen Tier.seqCase)
  | letEta => exact .letEta _
  | unitEta => exact .unitEta _
  | pairEta => exact .pairEta _
  | pairBeta =>
    simp only [ofLetPar, Parallel.Tm.widen, Parallel.Tm.lift, Parallel.Tm.widen_rename]
    exact .pairBeta _ _ _
  | bindOp =>
    simp only [ofLetPar, Parallel.Tm.widen, Parallel.Tm.underBinder, Parallel.Tm.widen_rename]
    exact .bindOp _ _
  | bindLet =>
    simp only [ofLetPar, Parallel.Tm.widen, Parallel.Tm.underBinder, Parallel.Tm.widen_rename]
    exact .bindLet _ _ _
  | bindLetPair =>
    simp only [ofLetPar, Parallel.Tm.widen, Parallel.Tm.underBinder, Parallel.Tm.widen_rename]
    exact .bindLetPair _ _ _
  | bindPair =>
    simp only [ofLetPar, Parallel.Tm.widen, Parallel.Tm.underTwoBinders, Parallel.Tm.widen_rename]
    exact .bindPair _ _

omit [DecidableEq ν] in
theorem ofLetPar_parRule (h : ParRule pureEff a b) :
    ParRule pureEff (ofLetPar a) (ofLetPar b) := by
  cases h with
  | swap => exact .swap _ _
  | assoc => exact .assoc _ _ _
  | purePair ha hb => exact .purePair (ha.widen Tier.seqCase) (hb.widen Tier.seqCase)
  | unitLeft => exact .unitLeft _
  | unitRight => exact .unitRight _
  | map hf hg =>
    simp only [ofLetPar, Parallel.Tm.widen, Parallel.Tm.leftResult, Parallel.Tm.underBinder,
      Parallel.Tm.widen_rename]
    exact .map (hf.widen Tier.seqCase) (hg.widen Tier.seqCase)

theorem ofLetPar_equiv (h : LetPar.Equiv pureEff Γ β a b A) :
    LetParCase.Equiv pureEff Γ β (ofLetPar a) (ofLetPar b) A := by
  induction h with
  | refl h => exact .refl (ofLetPar_hasType h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | op _ ih => exact .op ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | par _ _ iha ihb => exact .par iha ihb
  | inl | inr | case | abort => exact False.elim (‹Tier.HasCase .seq› rfl)
  | iter => exact nomatch ‹Tier.HasIter .seq›
  | seqRule hr ha hb =>
    exact .seqRule (ofLetPar_seqRule hr) (ofLetPar_hasType ha) (ofLetPar_hasType hb)
  | parRule hr ha hb =>
    exact .parRule (ofLetPar_parRule hr) (ofLetPar_hasType ha) (ofLetPar_hasType hb)
  | extraRule h => exact h.elim

theorem denote_ofLetParDerivation (D : τ → Type q) [ProductModel D] [UnitModel D]
    [CoproductModel D] [EmptyModel D] {m : Type q → Type q} [Monad m]
    (M : InstructionModel D Φ m) (P : ParOp m) (d : Parallel.Derivation Φ Γ β a A)
    (γ : FreeEnv D Γ) (ρ : BoundEnv D β) :
    (ofLetParDerivation d).denote D M P (Control.case D m) γ ρ =
      d.denote D M P (Control.seq D m) γ ρ := by
  induction d with
  | fv | bv | unit => rfl
  | op _ ih =>
    simp only [ofLetParDerivation, ofLetPar, Parallel.Tm.widen, Parallel.Derivation.denote]
    congr 1
    exact ih ρ
  | let₁ _ _ iha ihb | let₂ _ _ iha ihb =>
    simp only [ofLetParDerivation, ofLetPar, Parallel.Tm.widen, Parallel.Derivation.denote]
    congr 1
    · exact iha ρ
    · funext a
      exact ihb _
  | pair _ _ iha ihb =>
    simp only [ofLetParDerivation, ofLetPar, Parallel.Tm.widen, Parallel.Derivation.denote]
    congr 1
    · exact iha ρ
    · funext a
      congr 1
      exact ihb ρ
  | par _ _ iha ihb =>
    simp only [ofLetParDerivation, ofLetPar, Parallel.Tm.widen, Parallel.Derivation.denote]
    congr 1
    congr 1
    · exact iha ρ
    · exact ihb ρ
  | inl | inr | case | abort => exact False.elim (‹Tier.HasCase .seq› rfl)
  | iter => exact nomatch ‹Tier.HasIter .seq›

theorem parCaseLeft {e t : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {X Y B : τ}
    (hp : Parallel.Pure pureEff e) (he : Parallel.HasType Φ Γ β e (coprod X Y))
    (hl : Parallel.HasType Φ Γ (.snoc β X) l A) (hr : Parallel.HasType Φ Γ (.snoc β Y) r A)
    (ht : Parallel.HasType Φ Γ β t B) :
    LetParCase.Equiv pureEff Γ β (.par (.case hasCase e l r) t)
      (.case hasCase e (.par l t.lift) (.par r t.lift)) (product A B) := by
  obtain ⟨de⟩ := he
  obtain ⟨dl⟩ := hl
  obtain ⟨dr⟩ := hr
  obtain ⟨dx⟩ := ht.lift (B := X)
  obtain ⟨dy⟩ := ht.lift (B := Y)
  obtain ⟨dt⟩ := ht
  exact .extraRule (.parCaseLeft hasCase hp) ⟨.par (.case de dl dr) dt⟩
    ⟨.case de (.par dl dx) (.par dr dy)⟩

theorem parCaseRight {e t : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {X Y B : τ}
    (hp : Parallel.Pure pureEff e) (he : Parallel.HasType Φ Γ β e (coprod X Y))
    (hl : Parallel.HasType Φ Γ (.snoc β X) l B) (hr : Parallel.HasType Φ Γ (.snoc β Y) r B)
    (ht : Parallel.HasType Φ Γ β t A) :
    LetParCase.Equiv pureEff Γ β (.par t (.case hasCase e l r))
      (.case hasCase e (.par t.lift l) (.par t.lift r)) (product A B) := by
  obtain ⟨de⟩ := he
  obtain ⟨dl⟩ := hl
  obtain ⟨dr⟩ := hr
  obtain ⟨dx⟩ := ht.lift (B := X)
  obtain ⟨dy⟩ := ht.lift (B := Y)
  obtain ⟨dt⟩ := ht
  exact .extraRule (.parCaseRight hasCase hp) ⟨.par dt (.case de dl dr)⟩
    ⟨.case de (.par dx dl) (.par dy dr)⟩

end Silmaril.Isotope.LetParCase.Proofs
