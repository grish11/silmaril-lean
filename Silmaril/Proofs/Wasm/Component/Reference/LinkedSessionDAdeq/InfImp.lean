module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.InfLayers

/-!
# Infinite plays of a simple component with imports, from its instance

The infinite versions of `imp_div_build`, through the same layers (`core3Sem`'s export and
import handlers, `widenH`, the `canon lower` wiring `implsN`, the pairing and `splitH`, the import
mask, the export handler):

* `imp_inf_pend`: complete rounds through the layers (`LayerI`), then a pending export call whose
  lowered core question makes the core import calls `ω 0, ω 1, …`, each related to one component
  import call (`ImpRel`), forever: an infinite play of the instance's read-back session gives an
  infinite play of `c.toComp.denUD (impSemD P)`, pending on the export call with the component
  import calls forever (the importer's side of chatter).
* `imp_inf_cpl`: infinitely many rounds through the layers: an infinite play of the instance's
  read-back session gives one of the IR (the exporter serving forever).

The rounds of each layer are those of `LayerI` (`hc_exportH`, …, `hc_exportsH`, one round each).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.Abstract.InstSession (spullD instSession)
open Silmaril.Wasm.SingleThreaded (ofFlat toFlat? Thread)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## The strategies, unfolded -/

/-- `impSemD P` at the instance of the module: the read-back instance session between
`core3Sem`'s import and export handlers. -/
theorem impSemD_sem_inst (P : Profile) {m : ImpModule} {I : SInst} (hI : m.IsInst I) :
    (impSemD P).sem m = (DStrategy.ofHandler (importH (instNumI hI))).comp
      ((spullD (instSession I P I.store)).comp (DStrategy.ofHandler (exportH (instNumI hI)))) := by
  have hex : ∃ J, m.IsInst J := ⟨I, hI⟩
  rw [impSemD_sem_of P hex]
  have key : ∀ J (hJ : m.IsInst J), (Silmaril.Wasm.Abstract.InstSession.core3SemD P).sem
      (instNumI hJ) = (DStrategy.ofHandler (importH (instNumI hI))).comp
      ((spullD (instSession I P I.store)).comp (DStrategy.ofHandler (exportH (instNumI hI)))) := by
    intro J hJ
    obtain rfl := ImpModule.IsInst.unique hJ hI
    rfl
  exact key _ hex.choose_spec

/-- The core node of a simple component with imports, unfolded. -/
theorem node_coreNode (C : DCoreSem ImpModule) (e : Nat) (c : SimpleI) :
    Node.denD C e c.coreNode =
      (DStrategy.ofHandler (implsN e (SimpleI.lowerArgs c.imports)
        (CoreModule.imports c.mod).length)).comp
        ((C.sem c.mod).comp (DStrategy.ofHandler (widenH (CoreModule.exports c.mod).length))) := by
  rw [SimpleI.coreNode, Node.denD]
  rfl

/-- The divergence-aware strategy of a simple component with imports, unfolded. -/
theorem denUD_simpleI (C : DCoreSem ImpModule) (c : SimpleI) :
    (Comp.mk c.imports [c.coreNode] c.compExports).denUD C =
      (DStrategy.ext c.imports.length (DStrategy.ofHandler (maskH c.imports.length))
        (Node.denD C c.imports.length c.coreNode)).comp
        (DStrategy.ofHandler (exportsH (c.imports.length + c.mod.exports.length)
          c.toComp.exports)) := by
  rw [Comp.denUD, denNodesD_cons, denNodesD_nil]
  rfl

theorem oneCall_of_allCall {E F : Sig.{0}} {h : Handler E F} (hh : AllCall h) : OneCall h :=
  fun q => .inr (hh q)

/-! ## The rounds of the layers -/

section Layers

variable {c : SimpleI} {I : SInst} (hI : c.mod.IsInst I) (d : LayerI c I)

theorem hc_exportH (hd : d.Ok hI) : HC (exportH (instNumI hI)) [d.l₁] [d.r] :=
  .call (exportH_op hI d.hk d.r.q hd.core hd.args) rfl .nil

theorem hb_importH (hd : d.Ok hI) : HB (importH (instNumI hI)) [d.l₁] [d.l₂] :=
  .cons hd.imp .nil

theorem hc_widenH : HC (widenH (CoreModule.exports c.mod).length) [d.l₃] [d.l₂] :=
  .call (h := widenH _) (dite_eq_left d.hk) rfl .nil

theorem hb_implsN (hd : d.Ok hI) :
    HB (implsN c.imports.length (SimpleI.lowerArgs c.imports) (CoreModule.imports c.mod).length)
      [d.l₃] [d.l₄] :=
  .cons hd.impls .nil

theorem hc_splitH : HC (splitH c.imports.length) [d.l₅] [d.l₄.inr (F₁ := sigU)] :=
  .call (h := splitH _) (splitH_shift _ _ _) rfl .nil

theorem hb_maskH : HB (maskH c.imports.length) [d.l₅] [d.l₅] :=
  .cons (hrounds_maskH _ _) .nil

theorem hc_exportsH (hd : d.Ok hI) :
    HC (exportsH (c.imports.length + c.mod.exports.length) c.toComp.exports) [d.l₆] [d.l₅] := by
  have hl' : checkLower c.exports[d.j.val].ty.params d.vs = some d.xs := hd.lower
  refine .call (h := exportsH _ _)
    (q' := (c.exports[d.j].core + c.imports.length, .flat d.xs))
    (k := fun n => .pure (n.bind (Adapter.up (.lift c.exports[d.j].ty)))) ?_ rfl .nil
  rw [exportsH_toCompI c d.j.isLt d.vs d.hk, hl']
  rfl

end Layers

/-! ## The importer, chattering -/

/-- **The importer's IR on an infinite pending round** (the infinite version of
`imp_div_build`): complete rounds through the layers, then a pending export call `(j, .vals vs)`
whose lowered core question `f` makes the core import calls `ω k`, each related to the one
component import call `Y k`, forever (an infinite play of the instance's read-back session), are
an infinite play of `c.toComp.denUD (impSemD P)`. -/
theorem imp_inf_pend {P : Profile} {c : SimpleI} (hc : c.Good) {I : SInst}
    (hI : c.mod.IsInst I) {L : List (LayerI c I)} (hL : ∀ d ∈ L, d.Ok hI)
    {j : Fin c.exports.length} {vs : List IVal} {xs : List Flat}
    (hl : checkLower c.exports[j].ty.params vs = some xs) {f : I.F.Op}
    (hf₁ : f.1.val = c.exports[j].core) (hf₂ : f.2.1 = xs.map ofFlat)
    {ω : ℕ → Round I.E} {Y : ℕ → Round (sigN c.imports.length)}
    (hrel : ∀ k, Silmaril.Wasm.Component.Reference.ImpRel c I (ω k) [Y k])
    (hinf : (rch (L.map LayerI.r) f ω).lim ∈ (spullD (instSession I P I.store)).inf) :
    (rch (L.map LayerI.l₆) (j.val, .vals vs) fun k => (Y k).forget).lim ∈
      ((Comp.mk c.imports [c.coreNode] c.compExports).denUD (impSemD P)).inf := by
  have hk : c.exports[j].core < c.mod.exports.length := core_lt hc j
  choose x₂ Hi Hn using fun k => imp_call hI (hrel k)
  -- `core3Sem`'s export handler
  have h₉ := inf_top_pend (HC.of_map _ _ L fun d hd => hc_exportH hI d (hL d hd))
    (exportH_op hI hk f hf₁ hf₂) ω hinf
  -- `core3Sem`'s import handler
  have h₈ := inf_below_pend (oneCall_of_allCall (Silmaril.Wasm.Abstract.NodeDiv.allCall_importH _))
    (HB.of_map _ _ L fun d hd => hb_importH hI d (hL d hd)) (⟨c.exports[j].core, hk⟩, .flat xs)
    (Y := x₂) Hi h₉
  rw [← impSemD_sem_inst P hI] at h₈
  -- `widenH`
  have h₇ := inf_top_pend (HC.of_map _ _ L fun d _ => hc_widenH d)
    (g := (c.exports[j].core, .flat xs)) (f := (⟨c.exports[j].core, hk⟩, .flat xs))
    (dite_eq_left hk) x₂ h₈
  -- the `canon lower` wiring
  have h₆ := inf_below_pend (oneCall_implsN _ _ _)
    (HB.of_map _ _ L fun d hd => hb_implsN hI d (hL d hd)) (c.exports[j].core, .flat xs)
    (Y := fun k => (Y k).forget) Hn h₇
  rw [← node_coreNode] at h₆
  -- the pairing and `splitH`
  have h₅ := inf_pair_pend (DStrategy.id sigU) h₆
  have H₅ : HC (splitH c.imports.length) (L.map LayerI.l₅)
      ((L.map LayerI.l₄).map (CRound.inr (F₁ := sigU))) := by
    rw [List.map_map]
    exact HC.of_map _ _ L fun d _ => hc_splitH d
  have h₄ := inf_top_pend H₅ (splitH_shift c.imports.length c.exports[j].core (.flat xs)) _ h₅
  -- the import mask
  have h₃ := inf_below_pend (oneCall_maskH _) (HB.of_map _ _ L fun d _ => hb_maskH d)
    (c.exports[j].core + c.imports.length, .flat xs) (X := fun k => (Y k).forget)
    (Y := fun k => (Y k).forget) (fun k => hrounds_maskH _ [Y k]) h₄
  -- the export handler
  have hg₃ : exportsH (c.imports.length + c.mod.exports.length) c.toComp.exports
      (j.val, .vals vs) = .call (c.exports[j].core + c.imports.length, .flat xs)
        fun n => .pure (n.bind (Adapter.up (.lift c.exports[j].ty))) := by
    have hl' : checkLower c.exports[j.val].ty.params vs = some xs := hl
    rw [exportsH_toCompI c j.isLt vs hk, hl']
    rfl
  have h₂ := inf_top_pend (HC.of_map _ _ L fun d hd => hc_exportsH hI d (hL d hd)) hg₃ _ h₃
  rw [denUD_simpleI]
  exact h₂

/-! ## A component serving forever -/

/-- **The IR on infinitely many rounds** (the infinite version of `cplay_comp_ofHandler` through
the layers): rounds `D k` through the layers, the instance playing them forever (an infinite
play of its read-back session), are an infinite play of `c.toComp.denUD (impSemD P)`. -/
theorem imp_inf_cpl {P : Profile} {c : SimpleI} {I : SInst} (hI : c.mod.IsInst I)
    {D : ℕ → LayerI c I} (hD : ∀ k, (D k).Ok hI)
    (hinf : (cch fun k => (D k).r).lim ∈ (spullD (instSession I P I.store)).inf) :
    (cch fun k => (D k).l₆).lim ∈
      ((Comp.mk c.imports [c.coreNode] c.compExports).denUD (impSemD P)).inf := by
  have h₉ := inf_top_cpl (fun k => hc_exportH hI (D k) (hD k)) hinf
  have h₈ := inf_below_cpl (oneCall_of_allCall (Silmaril.Wasm.Abstract.NodeDiv.allCall_importH _))
    (fun k => hb_importH hI (D k) (hD k)) h₉
  rw [← impSemD_sem_inst P hI] at h₈
  have h₇ := inf_top_cpl (fun k => hc_widenH (D k)) h₈
  have h₆ := inf_below_cpl (oneCall_implsN _ _ _) (fun k => hb_implsN hI (D k) (hD k)) h₇
  rw [← node_coreNode] at h₆
  have h₅ := inf_pair_cpl (DStrategy.id sigU) h₆
  have h₄ := inf_top_cpl (fun k => hc_splitH (D k)) h₅
  have h₃ := inf_below_cpl (oneCall_maskH _) (fun k => hb_maskH (D k)) h₄
  have h₂ := inf_top_cpl (fun k => hc_exportsH hI (D k) (hD k)) h₃
  rw [denUD_simpleI]
  exact h₂

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
