module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.Games
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq.Imp
public import Silmaril.Wasm.Component.Reference.LinkedSessionD.Thms

/-!
# Reading back the divergences of a simple component with imports

`imp_div_readback`: a divergence of `c.toComp.denUD (impSemD P)` after typed complete rounds
`up` and a typed pending export call `(j, .vals vs)` with the lower calls `cs` is, layer by layer
(the export handler, the import mask, `splitH`, the pairing, the `canon lower` wiring `implsN`,
`widenH`, `core3Sem`'s import and export handlers, `SimpleI.div_coreNode_impSemD`), a play of
the core instance from its store: rounds `ri` read back as in `imp_readback` (`RdI`), then the
lowered core question `f` pending after core import calls `ics` related to `cs` (`ImpRel`), at a
running state that diverges host-free (`Linked2.DivB`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.SingleThreaded (ofFlat toFlat? Thread)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-- The game positions along a run of a core instance. -/
theorem ipath_pos {I : SInst} {P : Profile} {x y : I.HState} {a : List (Move I.E I.F)}
    (h : I.Path P x a y) : Path x.pos a y.pos := by
  induction h with
  | nil => exact .nil _
  | cons t _ ih =>
    cases t with
    | call s f => exact .cons (.ask f) ih
    | ucall _ _ _ => exact .cons (.call _ _) ih
    | uret v => exact .cons (.reply _ _ v) ih
    | oret _ _ _ => exact .cons (.ret _ _) ih

/-- The divergences of the core node of a simple component, at an instance `J` of its module
(the set of `SimpleI.div_coreNode_impSemD`). -/
def CoreDivAt (P : Profile) (e : Nat) (c : SimpleI) (J : SInst) (hJ : c.mod.IsInst J) :
    Set (List (Move sigU sigU)) :=
  {p | ∃ u v, Zip u v p ∧
    u ∈ Strategy.ofHandler (implsN e (SimpleI.lowerArgs c.imports) c.mod.imports.length) ∧
      ∃ a b, Zip a b v ∧ (∃ x y, Zip x y a ∧
        x ∈ Strategy.ofHandler (importH (instNumI hJ)) ∧ ∃ a' b', Zip a' b' y ∧
          (∃ f s t, J.Path P (.idle J.store) a' (.running f s t) ∧ Linked2.DivB P s t) ∧
          b' ∈ Strategy.ofHandler (exportH (instNumI hJ))) ∧
        b ∈ Strategy.ofHandler (widenH c.mod.exports.length)}

theorem coreDivAt_eq (P : Profile) (e : Nat) (c : SimpleI) {I : SInst} (hI : c.mod.IsInst I) :
    ∀ (J : SInst) (hJ : c.mod.IsInst J), J = I → CoreDivAt P e c J hJ = CoreDivAt P e c I hI := by
  rintro J hJ rfl
  rfl

/-- `SimpleI.div_coreNode_impSemD` at the instance of the module. -/
theorem div_coreNode_inst (P : Profile) (e : Nat) (c : SimpleI) {I : SInst}
    (hI : c.mod.IsInst I) :
    (Node.denD (impSemD P) e c.coreNode).div = CoreDivAt P e c I hI := by
  have h : ∃ J, c.mod.IsInst J := ⟨I, hI⟩
  rw [SimpleI.div_coreNode_impSemD P e c h]
  exact coreDivAt_eq P e c hI _ h.choose_spec (ImpModule.IsInst.unique h.choose_spec hI)

/-- **The read-back of a divergence of the importer's IR**: a divergence of
`c.toComp.denUD (impSemD P)` after typed complete rounds `up` and the pending typed export call
`(j, .vals vs)` with the lower calls `cs` is a play of the core instance from its store: rounds
`ri` read back by `RdI`, then the lowered core question `f` pending after core import calls `ics`
related to `cs` by `ImpRel`, at a running state that diverges host-free. -/
theorem imp_div_readback {P : Profile} {c : SimpleI} (hc : c.Good) {I : SInst}
    (hI : c.mod.IsInst I) {up : List (CRound sigU sigU)} (htop : ∀ u ∈ up, TopI c u)
    {j : Fin c.exports.length} {vs : List IVal}
    (hck : ValTy.checkList c.exports[j].ty.params vs = true) {cs : List (Round sigU)}
    (h : rplay up (j.val, .vals vs) cs ∈
      ((Comp.mk c.imports [c.coreNode] c.compExports).denUD (impSemD P)).div) :
    ∃ (ri : List (CRound I.E I.F)) (f : I.F.Op) (ics : List (Round I.E))
      (dss : List (List (Round (sigN c.imports.length)))) (s : Store Nat) (t : Thread),
      List.Forall₂ (RdI c I) ri up ∧
      I.Path P (.idle I.store) (rplay ri f ics) (.running f s t) ∧ Linked2.DivB P s t ∧
      f.1.val = c.exports[j].core ∧
      f.2.1 = (lowerArgs c.exports[j].ty.params vs).map ofFlat ∧
      List.Forall₂ (ImpRel c I) ics dss ∧ cs = dss.flatten.map Round.forget := by
  rw [SimpleI.div_denUD_impSemD P c ⟨I, hI⟩] at h
  obtain ⟨s, t, hz, hs, ht⟩ := h
  obtain ⟨s₁, t₁, hz₁, hs₁, a, b, hz₂, ⟨ha, haN⟩, hb⟩ := hs
  -- the pairing runs, so the layer above it does
  obtain ⟨f₂, ha₂⟩ :=
    ((DStrategy.id sigU).pair (Node.denD (impSemD P) c.imports.length c.coreNode)).div_run
      ⟨ha, .inr haN⟩
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨g₄, ht₁⟩ := run_of_zip_top hz₂ ha₂ hyb
  obtain ⟨u₄, cs₄, rfl⟩ := exists_rplay ht₁
  -- the import mask
  obtain ⟨ys₁, hys₁⟩ := Strategy.mem_ofHandler.mp hs₁
  obtain ⟨low₃', cs', H₄, H₄', rfl⟩ := hb_zip_run (oneShot_maskH _) hys₁ hz₁
  -- the export handler
  obtain ⟨yt, hyt⟩ := Strategy.mem_ofHandler.mp ht
  obtain ⟨low₃, k₃, H₃, hk₃, hs_eq⟩ :=
    hc_zip_run (oneShot_implsH _ _) (path_rplay _ _ _) hyt hz
  obtain ⟨rfl, -, rfl⟩ := rplay_inj hs_eq
  have e₃ := (exportsH_typed hc hck).symm.trans hk₃
  obtain ⟨he₃, -⟩ := Prog.call.inj e₃
  subst he₃
  -- the complete rounds, down to the pairing
  have G₃ : List.Forall₂ (L3 c) low₃' up :=
    (forall₂_and_right (forall₂_swap
      (hc_forall₂ H₃ fun u hu a => topI_nonpure hc (htop u hu) a)) htop).imp
      fun _ _ ⟨hr, ht⟩ => l3_of hc ht hr
  have G₄ : List.Forall₂ (L4 c) u₄ up :=
    (forall₂_comp (hb_forall₂ H₄) G₃).imp fun _ _ ⟨_, h₁, h₂⟩ => l4_of h₁ h₂
  have hge : ∀ r ∈ u₄, c.imports.length ≤ r.q.1 := fun r hr =>
    let ⟨_, h⟩ := forall₂_mem_left G₄ r hr
    l4_ge h
  -- `splitH` and the pairing
  obtain ⟨low₅, k₅, H₅, hk₅, rfl⟩ := hc_zip_run (oneShot_splitH _) ha₂ hyb hz₂
  rw [hc_splitH_inv H₅ hge] at haN
  simp only [splitH, Nat.not_lt.mpr (Nat.le_add_left _ _), ↓reduceIte] at hk₅
  obtain ⟨hk₅, -⟩ := Prog.call.inj hk₅
  subst hk₅
  rw [halves_rplay_inr] at haN
  -- the core node
  rw [div_coreNode_inst P _ c hI] at haN
  obtain ⟨u, v, hz₆, hu, a₇, b₇, hz₇, ⟨x₈, y₈, hz₈, hx₈, a₉, b₉, hz₉,
    ⟨f, s₉, t₉, hpath, hdiv⟩, hb₉⟩, hb₇⟩ := haN
  have hpos₉ : Path .idle a₉ (.run f) := ipath_pos hpath
  obtain ⟨yb₉, hyb₉⟩ := Strategy.mem_ofHandler.mp hb₉
  obtain ⟨g₈, hy₈⟩ := run_of_zip_top hz₉ hpos₉ hyb₉
  obtain ⟨u₈, cs₈, rfl⟩ := exists_rplay hy₈
  obtain ⟨yx₈, hyx₈⟩ := Strategy.mem_ofHandler.mp hx₈
  obtain ⟨low₇', cs₇', H₈, H₈', rfl⟩ := hb_zip_run (oneShot_importH _) hyx₈ hz₈
  obtain ⟨yb₇, hyb₇⟩ := Strategy.mem_ofHandler.mp hb₇
  obtain ⟨g₆, hv⟩ := run_of_zip_top hz₇ (path_rplay _ _ _) hyb₇
  obtain ⟨u₆, cs₆, rfl⟩ := exists_rplay hv
  obtain ⟨yu, hyu⟩ := Strategy.mem_ofHandler.mp hu
  obtain ⟨low₆, cs₆', H₆, H₆', hx⟩ := hb_zip_run (oneShot_implsN _ _ _) hyu hz₆
  obtain ⟨rfl, rfl, rfl⟩ := rplay_inj hx
  obtain ⟨low₇, k₇, H₇, hk₇, ha₇⟩ := hc_zip_run (oneShot_widenH _) (path_rplay _ _ _) hyb₇ hz₇
  obtain ⟨rfl, -, rfl⟩ := rplay_inj ha₇
  rw [Nat.add_sub_cancel] at hk₇
  have e₇ := (widenH_lt (core_lt hc j) _).symm.trans hk₇
  obtain ⟨he₇, -⟩ := Prog.call.inj e₇
  subst he₇
  obtain ⟨ri, k₉, H₉, hk₉, rfl⟩ := hc_zip_run (oneShot_exportH _) hpos₉ hyb₉ hz₉
  have hl := checkLower_of_check hck
  have e₉ := (exportH_op hI (core_lt hc j)
    (opAtI hI (core_lt hc j) (lowered_types' hc hl (core_lt hc j))) rfl rfl).symm.trans hk₉
  obtain ⟨he₉, -⟩ := Prog.call.inj e₉
  subst he₉
  -- the complete rounds, down to the instance
  have G₆ : List.Forall₂ (L6 c) u₆ up :=
    (forall₂_comp (forall₂_map_right (hb_forall₂ H₆)) G₄).imp
      fun _ _ ⟨_, h₁, h₂⟩ => l6_of h₁ h₂
  have G₇ : List.Forall₂ (L7 c) low₇' up :=
    (forall₂_comp (forall₂_swap (hc_forall₂ H₇ fun x hx a =>
      let ⟨_, h⟩ := forall₂_mem_left G₆ x hx
      l6_nonpure hc h a)) G₆).imp fun _ _ ⟨_, h₁, h₂⟩ => l7_of hc h₁ h₂
  have G₈ : List.Forall₂ (L8 c hI) u₈ up :=
    (forall₂_comp (hb_forall₂ H₈) G₇).imp fun _ _ ⟨_, h₁, h₂⟩ => l8_of hI h₁ h₂
  have G₉ : List.Forall₂ (RdI c I) ri up :=
    (forall₂_comp (forall₂_swap (hc_forall₂ H₉ fun x hx a =>
      let ⟨_, h⟩ := forall₂_mem_left G₈ x hx
      l8_nonpure hc hI h a)) G₈).imp fun _ _ ⟨_, h₁, h₂⟩ => rd_of hc hI h₁ h₂
  -- the pending calls
  obtain ⟨dss, hF, hcs⟩ := imp_calls_inv hc hI cs₈ _ _ _ H₈' H₆' H₄'
  exact ⟨ri, _, cs₈, dss, s₉, t₉, G₉, hpath, hdiv, rfl, rfl, hF, hcs⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
