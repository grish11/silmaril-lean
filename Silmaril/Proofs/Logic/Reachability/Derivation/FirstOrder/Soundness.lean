module

public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Calculus.Thms
public import Silmaril.Logic.Reachability.Derivation.FirstOrder.Stock.Extension.Thms
public import Silmaril.Logic.Reachability.Derivation.Thms

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation.FirstOrder
open Silmaril.Logic.Institution.Examples
variable {Sg : FOL.Signature} {cfg : Sg.S} {k : Nat} {Γ : Fin k → Sg.S}
variable (M : FOL.Structure Sg) {ι : Type}
variable (rules : ι → RuleSystem.Scheme (M.carrier cfg))

/-- Closed soundness at every original finite assignment, via proved stock
extension and the existing full semantic soundness theorem. Explicit defaults
suffice; no arithmetic, countability, termination or finite-rule premise occurs. -/
theorem Derives.sound_with_defaults {c : Claim Sg cfg Γ}
    (d : Derives M rules ∅ ∅ c) (wellDefined : RuleSystem.WeaklyWellDefined rules)
    (defaults : (s : Sg.S) → M.carrier s)
    (a : (i : Fin k) → M.carrier (Γ i)) (w : M.carrier cfg)
    (pre : Pattern.localHolds c.pre M a w) :
    AllPartial (RuleSystem.Induced rules) (fun v => Pattern.localHolds c.post M a v) w := by
  let e : Embedding Γ := Embedding.canonical Γ
  let stock := e.extendLocal M defaults a
  have projection : e.assignment M stock = a := e.assignment_extendLocal M defaults a
  have closed : Derivation.Derives rules ∅ ∅ (c.interpret M e) := by
    simpa only [environment, Set.image_empty] using d.interpret M e
  have source : (c.interpret M e).pre stock w := by
    change FOL.Formula.Holds M c.pre
      (Silmaril.Logic.FirstOrder.Variables.consAssignment M cfg Γ w (e.assignment M stock))
    rw [projection]
    exact pre
  have target := closed.sound wellDefined stock w source
  have samePost : (c.interpret M e).post stock =
      (fun v => Pattern.localHolds c.post M a v) := by
    funext v
    change FOL.Formula.Holds M c.post
      (Silmaril.Logic.FirstOrder.Variables.consAssignment M cfg Γ v (e.assignment M stock)) = _
    rw [projection]
    rfl
  rw [samePost] at target
  exact target

/-- Nonempty carriers are used only here, to choose the explicit sorted defaults
needed to extend an arbitrary original captured assignment. -/
theorem Derives.sound {c : Claim Sg cfg Γ} (d : Derives M rules ∅ ∅ c)
    (wellDefined : RuleSystem.WeaklyWellDefined rules)
    (nonemptySorts : ∀ s, Nonempty (M.carrier s))
    (a : (i : Fin k) → M.carrier (Γ i)) (w : M.carrier cfg)
    (pre : Pattern.localHolds c.pre M a w) :
    AllPartial (RuleSystem.Induced rules) (fun v => Pattern.localHolds c.post M a v) w := by
  classical
  exact d.sound_with_defaults M rules wellDefined (fun s => Classical.choice (nonemptySorts s)) a w pre

end Silmaril.Logic.Reachability.Derivation.FirstOrder
