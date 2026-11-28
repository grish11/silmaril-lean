module

public import Silmaril.SSA.Isotope.LetPar.Structural.Thms
import Silmaril.Proofs.SSA.Isotope.LetPar.Equations

@[expose] public section

namespace Silmaril.Isotope.Parallel.Equiv

universe u v w x

variable {tier : Tier} {τ : Type u} [HasProduct τ] [HasUnit τ] [CaseTypes tier τ]
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] {ε : Type x} [HasEff Φ ε]
  {pureEff : ε} {extra : EqScheme tier ν Φ} {Γ : Ctx ν τ}
  {n : Nat} {β : BoundCtx τ n} {a b c : Tm tier ν Φ n} {A B C D E : τ}

/-- Both sides of a parallel equation have the stated exact type. -/
theorem hasType (h : Equiv pureEff extra Γ β a b A) :
    HasType Φ Γ β a A ∧ HasType Φ Γ β b A :=
  Proofs.hasType h

/-- Swapping the returned tuple corresponds to swapping the independent branches. -/
theorem parSwap (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
    Equiv pureEff extra Γ β ((Tm.par a b).swap) (.par b a) (product B A) :=
  Proofs.parSwap ha hb

/-- Reassociate parallel computations with the corresponding pure tuple map. -/
theorem parAssoc (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
    (hc : HasType Φ Γ β c C) :
    Equiv pureEff extra Γ β ((Tm.par (.par a b) c).assoc) (.par a (.par b c))
      (product A (product B C)) :=
  Proofs.parAssoc ha hb hc

/-- Two pure branches return the ordinary pair of their values. -/
theorem parPure (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
    (hpa : Pure pureEff a) (hpb : Pure pureEff b) :
    Equiv pureEff extra Γ β (.par a b) (.pair a b) (product A B) :=
  Proofs.parPure ha hb hpa hpb

/-- Projecting away a pure left unit retains the right computation. -/
theorem parUnitLeft (ha : HasType Φ Γ β a A) :
    Equiv pureEff extra Γ β ((Tm.par .unit a).dropLeft) a A :=
  Proofs.parUnitLeft ha

/-- Projecting away a pure right unit retains the left computation. -/
theorem parUnitRight (ha : HasType Φ Γ β a A) :
    Equiv pureEff extra Γ β ((Tm.par a .unit).dropRight) a A :=
  Proofs.parUnitRight ha

/-- Pure continuations can be applied to the two results of one parallel computation. -/
theorem parMap {f g : Tm tier ν Φ (n + 1)}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
    (hf : HasType Φ Γ (.snoc β A) f D) (hg : HasType Φ Γ (.snoc β B) g E)
    (hpf : Pure pureEff f) (hpg : Pure pureEff g) :
    Equiv pureEff extra Γ β (.par (.let₁ a f) (.let₁ b g))
      (.let₂ (.par a b) (.pair f.leftResult g.underBinder)) (product D E) :=
  Proofs.parMap ha hb hf hg hpf hpg

end Silmaril.Isotope.Parallel.Equiv
