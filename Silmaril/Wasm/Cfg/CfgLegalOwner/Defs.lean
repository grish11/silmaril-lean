module

public import Silmaril.Wasm.Cfg.CfgInst.Defs
public import Silmaril.Wasm.Component.Reference.LinkedSessionDAdeq.Defs
public import Silmaril.Wasm.Component.Reference.LinkedGInf.Defs

/-!
# What a legal reference injection needs from the reference owner: definitions

The concrete reference injections of the reference owner (`docs/projects/component-semantics.md`)
are `Linked2.refSessEquivFull_iff_denD`, which relates the reference machine's
`Linked2.RefSessEquivFull` to `l.toComp.denD (impSemD (profile o))`, and
`LinkedG.compSession_inj_full`. This module states the legal counterpart and the **exact**
obligation the owner must discharge. The proofs from those obligations are in
`Silmaril.Wasm.Cfg.CfgLegalOwner.Thms`.

* `impSemLD P`: the owner's `impSemD P` with the legal node semantics `CfgInst.legalSemD P` in
  place of `core3SemD P` (a module without an instance traps, as in `impSemD`).
* `OwnerObligations o prof RefL`: a relation `RefL` on `Linked2` (the owner's reference
  equivalence restricted to legal environments) is **stated at the same boundary as the IR**: on
  adequate links it coincides with `Linked2.RefSessEquivFull (profile o) prof`. This is what has
  to be proved on the reference side. It is plausible because the reference engine traps on an
  exception escaping a canon call (`Engine.Core3`, the canonical ABI's `call_and_trap_on_throw`),
  so no exception crosses an instance boundary there. The IR boundary (`importH`/`exportH`) does
  the same. That is a statement about the reference machine, and it is not proved here.
* `OwnerObligationsG o prof RefL`: the same for `LinkedG` under `LinkedG.ProfOk o`.
-/

@[expose] public section

namespace Silmaril.Wasm.Cfg.CfgLegalOwner

open Silmaril.Games
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

open Classical in
/-- **The owner's `impSemD` with legal node sessions.** -/
noncomputable def impSemLD (P : Numerics.Profile) : DCoreSem ImpModule where
  sem m :=
    if h : ∃ I, m.IsInst I then (CfgInst.legalSemD P).sem (m.numInst h)
    else DStrategy.ofHandler fun _ => .pure none

/-- **The owner's obligation (`Linked2`)**: the legal reference equivalence `RefL` is stated at
the IR's exception-free boundary; on adequate links it is the reference equivalence. -/
structure OwnerObligations (o : GrowOracle) (prof : ProfileKind)
    (RefL : Linked2 → Linked2 → Prop) : Prop where
  /-- The legal reference equivalence is the reference equivalence on adequate links. -/
  same_boundary : ∀ {l l' : Linked2}, l.Adequate → l'.Adequate →
    (RefL l l' ↔ Linked2.RefSessEquivFull (profile o) prof l l')

/-- **The owner's obligation (`LinkedG`)**: the same under `LinkedG.ProfOk o`. -/
structure OwnerObligationsG (o : GrowOracle) (prof : ProfileKind)
    (RefL : LinkedG → LinkedG → Prop) : Prop where
  /-- The legal reference equivalence is the reference equivalence on `ProfOk` links. -/
  same_boundary : ∀ {g g' : LinkedG}, g.ProfOk o → g'.ProfOk o →
    (RefL g g' ↔ LinkedG.RefSessEquivFull (profile o) prof g g')

end Silmaril.Wasm.Cfg.CfgLegalOwner
