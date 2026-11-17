module

public import Silmaril.Wasm.Cfg.CfgLegalOwner.Defs
public import Silmaril.Wasm.Cfg.CfgLegalComp.Thms
public import Silmaril.Wasm.Component.Reference.LinkedSessionDAdeq.Thms
public import Silmaril.Wasm.Component.Reference.LinkedGSession.Thms

/-!
# What a legal reference injection needs from the reference owner: theorems

Proved here, without owner obligations:

* `impSemLD_eq`: `impSemLD (profile o) = impSemD (profile o)`, from `CfgLegalComp.legalSemD_eq`
  (`importH` never answers with an exception). Hence `denD_impSemLD_eq` and `denUD_impSemLD_eq`
  hold for every component of `ImpModule`s, so the owner's `IRDivEq (profile o)` and
  `IRInfEq (profile o)`, which are stated with `impSemD (profile o)`, are already their legal
  versions.

From the owner's obligations:

* `legal_injection_of`: for `Linked2`, under `OwnerObligations o prof RefL`, `RefL` on adequate
  links is the same export types, the same `pubPlays` of `l.toComp.denD (impSemLD (profile o))`,
  `IRDivEq` and `IRInfEq`. It is proved from the owner's `refSessEquivFull_iff_denD`.
* `legal_injectionG_of`: for `LinkedG`, under `OwnerObligationsG o prof RefL`, `RefL` on
  `ProfOk` links is the same export types and session objects. It is proved from the owner's
  `compSession_inj_full`.

Nothing here is a reference-side fact. If the reference relation the owner restricts to legal
environments is **not** at the IR boundary (for instance, if it passes exceptions between
instances), the obligation fails, and these theorems say nothing.
-/

public section

namespace Silmaril.Wasm.Cfg.CfgLegalOwner

open Silmaril.Games
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {o : GrowOracle}

/-- **The legal `impSemD` is `impSemD`** at a deterministic profile. -/
theorem impSemLD_eq : impSemLD (profile o) = impSemD (profile o) := by
  unfold impSemLD impSemD
  rw [CfgLegalComp.legalSemD_eq]

/-- Equal component denotations at `sigU`. -/
theorem denUD_impSemLD_eq (c : Comp ImpModule) :
    c.denUD (impSemLD (profile o)) = c.denUD (impSemD (profile o)) := by
  rw [impSemLD_eq]

/-- Equal component denotations at the interface signatures. -/
theorem denD_impSemLD_eq (c : Comp ImpModule) :
    c.denD (impSemLD (profile o)) = c.denD (impSemD (profile o)) := by
  rw [impSemLD_eq]

/-- **The legal injection for `Linked2`, from the owner's obligation.** -/
theorem legal_injection_of {prof : ProfileKind} {RefL : Linked2 → Linked2 → Prop}
    (h : OwnerObligations o prof RefL) {l l' : Linked2} (hl : l.Adequate) (hl' : l'.Adequate) :
    RefL l l' ↔ Linked2.SameTypes l l' ∧
      pubPlays (l.toComp.denD (impSemLD (profile o))).toStrategy =
        pubPlays (l'.toComp.denD (impSemLD (profile o))).toStrategy ∧
      Linked2.IRDivEq (profile o) l l' ∧ Linked2.IRInfEq (profile o) l l' := by
  rw [h.same_boundary hl hl', denD_impSemLD_eq, denD_impSemLD_eq]
  exact Linked2.refSessEquivFull_iff_denD o prof hl hl'

/-- **The legal injection for `LinkedG`, from the owner's obligation.** -/
theorem legal_injectionG_of {prof : ProfileKind} {RefL : LinkedG → LinkedG → Prop}
    (h : OwnerObligationsG o prof RefL) {g g' : LinkedG} (hg : g.ProfOk o) (hg' : g'.ProfOk o) :
    RefL g g' ↔ LinkedG.SameTypes g g' ∧
      LinkedG.compSession (profile o) g = LinkedG.compSession (profile o) g' := by
  rw [h.same_boundary hg hg']
  exact LinkedG.compSession_inj_full hg hg'

end Silmaril.Wasm.Cfg.CfgLegalOwner
