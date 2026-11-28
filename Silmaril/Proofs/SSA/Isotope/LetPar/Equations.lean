module

public import Silmaril.SSA.Isotope.LetPar.Structural.Thms

@[expose] public section

namespace Silmaril.Isotope.Parallel.Proofs

universe u v w x

variable {tier : Tier} {τ : Type u} [HasProduct τ] [HasUnit τ] [CaseTypes tier τ]
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] {ε : Type x} [HasEff Φ ε]
  {pureEff : ε} {extra : EqScheme tier ν Φ} {Γ : Ctx ν τ}
  {n : Nat} {β : BoundCtx τ n} {a b c : Tm tier ν Φ n} {A B C D E : τ}

theorem hasType (h : Equiv pureEff extra Γ β a b A) :
    HasType Φ Γ β a A ∧ HasType Φ Γ β b A := by
  induction h with
  | refl h => exact ⟨h, h⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | op _ ih => exact ⟨ih.1.map Derivation.op, ih.2.map Derivation.op⟩
  | inl _ ih => exact ⟨ih.1.map Derivation.inl, ih.2.map Derivation.inl⟩
  | inr _ ih => exact ⟨ih.1.map Derivation.inr, ih.2.map Derivation.inr⟩
  | abort _ ih => exact ⟨ih.1.map Derivation.abort, ih.2.map Derivation.abort⟩
  | let₁ _ _ iha ihb =>
    exact ⟨iha.1.map2 Derivation.let₁ ihb.1, iha.2.map2 Derivation.let₁ ihb.2⟩
  | pair _ _ iha ihb =>
    exact ⟨iha.1.map2 Derivation.pair ihb.1, iha.2.map2 Derivation.pair ihb.2⟩
  | let₂ _ _ iha ihb =>
    exact ⟨iha.1.map2 Derivation.let₂ ihb.1, iha.2.map2 Derivation.let₂ ihb.2⟩
  | case _ _ _ ihe ihl ihr =>
    exact ⟨(ihe.1.map2 Derivation.case ihl.1).map2 id ihr.1,
      (ihe.2.map2 Derivation.case ihl.2).map2 id ihr.2⟩
  | iter _ _ iha ihb =>
    exact ⟨iha.1.map2 Derivation.iter ihb.1, iha.2.map2 Derivation.iter ihb.2⟩
  | par _ _ iha ihb =>
    exact ⟨iha.1.map2 Derivation.par ihb.1, iha.2.map2 Derivation.par ihb.2⟩
  | seqRule _ ha hb | parRule _ ha hb | extraRule _ ha hb => exact ⟨ha, hb⟩

theorem parSwap (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
    Equiv pureEff extra Γ β ((Tm.par a b).swap) (.par b a) (product B A) := by
  obtain ⟨da⟩ := ha
  obtain ⟨db⟩ := hb
  exact .parRule (.swap a b) ⟨.let₂ (.par da db) (.pair .bv .bv)⟩ ⟨.par db da⟩

theorem parAssoc (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
    (hc : HasType Φ Γ β c C) :
    Equiv pureEff extra Γ β ((Tm.par (.par a b) c).assoc) (.par a (.par b c))
      (product A (product B C)) := by
  obtain ⟨da⟩ := ha
  obtain ⟨db⟩ := hb
  obtain ⟨dc⟩ := hc
  exact .parRule (.assoc a b c)
    ⟨.let₂ (.par (.par da db) dc) (.let₂ (.bv (i := 1)) (.pair .bv (.pair .bv .bv)))⟩
    ⟨.par da (.par db dc)⟩

theorem parPure (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
    (hpa : Pure pureEff a) (hpb : Pure pureEff b) :
    Equiv pureEff extra Γ β (.par a b) (.pair a b) (product A B) := by
  obtain ⟨da⟩ := ha
  obtain ⟨db⟩ := hb
  exact .parRule (.purePair hpa hpb) ⟨.par da db⟩ ⟨.pair da db⟩

theorem parUnitLeft (ha : HasType Φ Γ β a A) :
    Equiv pureEff extra Γ β ((Tm.par .unit a).dropLeft) a A := by
  obtain ⟨da⟩ := ha
  exact .parRule (.unitLeft a) ⟨.let₂ (.par .unit da) .bv⟩ ⟨da⟩

theorem parUnitRight (ha : HasType Φ Γ β a A) :
    Equiv pureEff extra Γ β ((Tm.par a .unit).dropRight) a A := by
  obtain ⟨da⟩ := ha
  exact .parRule (.unitRight a) ⟨.let₂ (.par da .unit) .bv⟩ ⟨da⟩

theorem parMap {f g : Tm tier ν Φ (n + 1)}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
    (hf : HasType Φ Γ (.snoc β A) f D) (hg : HasType Φ Γ (.snoc β B) g E)
    (hpf : Pure pureEff f) (hpg : Pure pureEff g) :
    Equiv pureEff extra Γ β (.par (.let₁ a f) (.let₁ b g))
      (.let₂ (.par a b) (.pair f.leftResult g.underBinder)) (product D E) := by
  obtain ⟨da⟩ := ha
  obtain ⟨db⟩ := hb
  obtain ⟨df'⟩ := hf.leftResult (B := B)
  obtain ⟨dg'⟩ := hg.underBinder (A := A)
  obtain ⟨df⟩ := hf
  obtain ⟨dg⟩ := hg
  exact .parRule (.map hpf hpg) ⟨.par (.let₁ da df) (.let₁ db dg)⟩
    ⟨.let₂ (.par da db) (.pair df' dg')⟩

end Silmaril.Isotope.Parallel.Proofs
