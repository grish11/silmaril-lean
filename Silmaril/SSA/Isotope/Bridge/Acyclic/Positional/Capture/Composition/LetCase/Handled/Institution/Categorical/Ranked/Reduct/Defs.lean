module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.Categorical.Ranked.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Institution.Reduct.Thms
public import Silmaril.Raw.SSA.Isotope.Morphism.Instructions.LetIter

/-! # Supported models under primitive relabellings

A relabelling of instruction signatures keeps every source type, target
type and effect. Its source signature is the target signature read through
the instruction map. The existing reduct of a coherent region model along a
relabelling keeps the type interpretation and reads each primitive through
the map.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open CategoryTheory CategoryTheory.Limits
open Silmaril.Logic.Institution (Room)
open Silmaril.Isotope.Institution (InstrSig)
open Silmaril.Isotope.Institution.Acyclic (CoherentRegionModel)
open Silmaril.Isotope.Institution.Acyclic.Captured (RankedEquation)
open LetIter.LocallyNameless (Derivation)

section Pull

variable {τ ε : Type} (Q : InstrSig τ ε) {Φ : Type} (r : Φ → Q.Instr)

/-- The target signature read through an instruction map. -/
def pullSig : InstrSig τ ε :=
  @InstrSig.mk τ ε Φ ⟨fun x => instrSrc (r x), fun x => instrTrg (r x)⟩ ⟨fun x => instrEff (r x)⟩

/-- The instruction map as a relabelling. Its three equations hold by
definition. -/
def pullHom : pullSig Q r ⟶ Q :=
  ⟨r, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

variable {Q r} [TypeFormers τ] {ν : Type} [DecidableEq ν] {Γ : Ctx ν τ}

/-- Relabel every primitive of an exact LetIter derivation over the
pulled-back signature. No type changes. -/
def relabelIter : {n : Nat} → {β : BoundCtx τ n} → {t : LetIter.LocallyNameless.Tm ν Φ n} → {A : τ} →
    Derivation (pullSig Q r).Instr Γ β t A → Derivation Q.Instr Γ β (t.mapInstr r) A
  | _, _, _, _, .fv h => .fv h
  | _, _, _, _, .bv => .bv
  | _, _, _, _, .op (f := f) ha => .op (f := r f) (relabelIter ha)
  | _, _, _, _, .let₁ ha hb => .let₁ (relabelIter ha) (relabelIter hb)
  | _, _, _, _, .unit => .unit
  | _, _, _, _, .pair ha hb => .pair (relabelIter ha) (relabelIter hb)
  | _, _, _, _, .let₂ ha hb => .let₂ (relabelIter ha) (relabelIter hb)
  | _, _, _, _, .inl ha => .inl (relabelIter ha)
  | _, _, _, _, .inr hb => .inr (relabelIter hb)
  | _, _, _, _, .case he hl hr => .case (relabelIter he) (relabelIter hl) (relabelIter hr)
  | _, _, _, _, .abort ha => .abort (relabelIter ha)
  | _, _, _, _, .iter ha hb => .iter (relabelIter ha) (relabelIter hb)

end Pull

variable {τ ε : Type} [TypeFormers τ]
  {V C : Type 1} [Category.{0} V] [Category.{0} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]

/-- The supported models of the ranked room over one functor. -/
abbrev SupportedModel (pe : ε) (P : InstrSig τ ε) := {K : CoherentRegionModel J P // Supported pe K}

/-- The existing ranked room restricted to its supported models. Sentences
and satisfaction are unchanged. -/
noncomputable def supportedRankedRoom (pe : ε) (P : InstrSig τ ε) : Room.{0, 0, 1} where
  Sen := RankedEquation P
  Mod := Cat.of (ShrinkHoms (Discrete (SupportedModel J pe P)))
  Sat N e := (Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P).Sat
    (ShrinkHoms.toShrinkHoms (Discrete.mk N.fromShrinkHoms.as.1)) e

/-- Every model of the room, viewed from the supported models: sentences
are unchanged and a supported model is sent to itself. -/
noncomputable def includeSupported (pe : ε) (P : InstrSig τ ε) :
    Silmaril.Isotope.Institution.Acyclic.Captured.rankedRoom J P ⟶ supportedRankedRoom J pe P where
  sen := id
  mod := ShrinkHoms.inverse.{0} (Discrete (SupportedModel J pe P)) ⋙
    Discrete.functor (fun N => Discrete.mk N.1) ⋙
    ShrinkHoms.functor.{0} (Discrete (CoherentRegionModel J P))
  sat _ _ := Iff.rfl

/-- Reduct of supported models along a relabelling, given that the
reduct of each supported model is supported. -/
noncomputable def supportedReductOf (pe : ε) {P Q : InstrSig τ ε} (f : P ⟶ Q)
    (closed : ∀ N : SupportedModel J pe Q, Supported pe (N.1.reduct f)) :
    (supportedRankedRoom J pe Q).Mod ⥤ (supportedRankedRoom J pe P).Mod :=
  ShrinkHoms.inverse.{0} (Discrete (SupportedModel J pe Q)) ⋙
    Discrete.functor (fun N => Discrete.mk ⟨N.1.reduct f, closed N⟩) ⋙
    ShrinkHoms.functor.{0} (Discrete (SupportedModel J pe P))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
