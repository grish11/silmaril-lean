module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef.Call
public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.RefRun

/-!
# Forward runs of a linked call: the core level

The backward simulation of a linked call (`LinkSeg`, `LinkExp`) reads a run of the shared core
store back into runs of the importer's part and of the exporter's part. Here the converse:

* `internalP_unmapH`: a host-free step of a store renamed by `g` is the renaming of a host-free
  step, when `gi` inverts `g` on the host code of the store; `reach_link_fwd`: host-free runs of
  a part (`LinkSt`, `internal_link`) are core runs of the shared store of the machine, with host
  type `CanonHost`;
* `gLInv`: the inverse of `gL` on the trampolines of a linked call (`hostsSat_lstat`);
* `LInv.reach_fwd`: a run of the importer's part is a core run of the shared thread, keeping
  `LInv` at the same exporter store;
* `exp_fwd`: a run of the exporter's specification from its store `π` is a core run of the
  exporter's activation in the shared store, `Rel4` re-established at the exporter's end store
  (not one read back from the shared store, which `PartRel` determines only up to renaming);
* `status_of_values`, `status_of_trap`: the machine status of the image of a finished part;
* `reach_doomed_callout`: a thread filled with a trap never reaches a callout.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)
open Silmaril.Proofs.Wasm.Game.Linking.Split (Own Ren PartRel Rel4 Grow Touch)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread

/-! ## Unmapping host code -/

section Unmap

variable {H : Type} {P : Profile}

/-- Renaming along `g`, then along `gi`, is the identity on the functions of a store whose host
code `gi` inverts. -/
theorem funcs_unmap (g : H → Nat) (gi : Nat → H) {s : Store H}
    (hs : HostsSat (fun h => gi (g h) = h) s) :
    (s.funcs.map (FuncInst.mapH g)).map (FuncInst.mapH gi) = s.funcs := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id s.funcs]
  refine List.map_congr_left fun fi hfi => ?_
  obtain ⟨a, ha⟩ := List.getElem?_of_mem hfi
  obtain ⟨ty, mo, code⟩ := fi
  cases code with
  | wasm f => rfl
  | host h =>
    have e : gi (g h) = h := hs a _ h ha rfl
    simp only [Function.comp_apply, FuncInst.mapH, FuncCode.mapH, e, id]

theorem mapH_unmap (g : H → Nat) (gi : Nat → H) {s : Store H}
    (hs : HostsSat (fun h => gi (g h) = h) s) : Store.mapH gi (Store.mapH g s) = s := by
  have e := funcs_unmap g gi hs
  cases s
  simp only [Store.mapH] at e ⊢
  rw [e]

theorem config_mapH₂ {H' : Type} (g : H → H') (s : Store H) (t : STh) :
    t.config (Store.mapH g s) = Config.mapH g (t.config s) := by
  cases t with
  | pending a args => exact (invoke_mapH g s a args).symm
  | active f code => rfl

/-- **Host-free steps of a renamed store are renamed host-free steps**, when `gi` inverts the
renaming on the store's host code. -/
theorem internalP_unmapH (g : H → Nat) (gi : Nat → H) {s : Store H} {t : STh}
    (hs : HostsSat (fun h => gi (g h) = h) s) {s₁ : Store Nat} {t' : STh}
    (h : Silmaril.Wasm.Game.InternalP P (Store.mapH g s, t) (s₁, t')) :
    ∃ s', s₁ = Store.mapH g s' ∧ s'.funcs = s.funcs ∧
      Silmaril.Wasm.Game.InternalP P (s, t) (s', t') := by
  have hf₁ : s₁.funcs = (Store.mapH g s).funcs :=
    Silmaril.Proofs.Wasm.Game.InternalP.funcs_prefix h
  obtain ⟨f', code', ht, hstep⟩ := h
  have hm := Step.mapH gi hstep
  have hc : Config.mapH gi (t.config (Store.mapH g s)) = t.config s := by
    rw [← config_mapH₂ gi, mapH_unmap g gi hs]
  rw [hc] at hm
  have hs' : (Store.mapH gi s₁).funcs = s.funcs := by
    show s₁.funcs.map _ = _
    rw [hf₁]
    exact funcs_unmap g gi hs
  have hb : Store.mapH g (Store.mapH gi s₁) = s₁ := by
    have e : (s₁.funcs.map (FuncInst.mapH gi)).map (FuncInst.mapH g) = s₁.funcs := by
      rw [hf₁]
      show ((s.funcs.map (FuncInst.mapH g)).map (FuncInst.mapH gi)).map (FuncInst.mapH g) =
        s.funcs.map (FuncInst.mapH g)
      rw [funcs_unmap g gi hs]
    cases s₁
    simp only [Store.mapH] at e ⊢
    rw [e]
  exact ⟨Store.mapH gi s₁, hb.symm, hs', f', code', ht, hm⟩

end Unmap

/-! ## Forward runs of a part -/

section Fwd

variable {P : Profile}

/-- A host-free step of the machine's core store is a core step. -/
theorem coreStep_of_internalP {x y : CoreSt (E3 P)} (h : Silmaril.Wasm.Game.InternalP P x y) :
    CoreStep (E3 P) x y := by
  refine ⟨.inl ?_, h⟩
  show flatStatus (Silmaril.Wasm.Game.statusP P x.1 x.2) = .running
  rw [Adequacy.statusP_running_of (s := x.1) (t := x.2) h]
  rfl

/-- **Runs of a part are core runs of its image in the shared store** of host type `CanonHost`,
the renaming and ownership growing, the shared store touched only at what the part owns. -/
theorem reach_link_fwd (g : CanonHost (E3 P) → Nat) (gi : Nat → CanonHost (E3 P))
    {s₀ : Store Nat} {x x' : Store Nat × STh} (run : Silmaril.Wasm.Game.Reach P x x') :
    ∀ {y : CoreSt (E3 P)} {ρ : Ren} {O : Own}, HostsSat (fun h => gi (g h) = h) y.1 →
      LinkSt s₀ ρ O x (Store.mapH g y.1, y.2) →
      ∃ (y' : CoreSt (E3 P)) (ρ' : Ren) (O' : Own),
        Relation.ReflTransGen (CoreStep (E3 P)) y y' ∧
        LinkSt s₀ ρ' O' x' (Store.mapH g y'.1, y'.2) ∧ Grow ρ O ρ' O' (Store.mapH g y.1) ∧
        Touch ρ O (Store.mapH g y.1) (Store.mapH g y'.1) ∧ y'.1.funcs = y.1.funcs := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro y ρ O _ hL
    exact ⟨y, ρ, O, .refl, hL, Grow.refl ρ O _, Touch.refl ρ O _, rfl⟩
  | @head x x₁ hx _ ih =>
    intro y ρ O hs hL
    obtain ⟨⟨σ₁, t₁⟩, ρ₁, O₁, hy₁, hL₁, hg₁, ht₁⟩ := internal_link hL hx
    obtain ⟨s', rfl, hfs, hi⟩ := internalP_unmapH g gi hs hy₁
    have hs' : HostsSat (fun h => gi (g h) = h) s' := fun a fi h ha hc => hs a fi h (hfs ▸ ha) hc
    obtain ⟨y', ρ', O', hrun, hL', hg', ht', hf'⟩ := ih (y := (s', t₁)) hs' hL₁
    exact ⟨y', ρ', O', .head (coreStep_of_internalP hi) hrun, hL',
      hg₁.trans hg' ht₁.structs_len ht₁.arrays_len, ht₁.trans hg₁ ht', hf'.trans hfs⟩

end Fwd

/-! ## The inverse of `gL` on trampolines -/

section Inv

variable {P : Profile}

/-- The trampoline of import `k`: the inverse of `gL` on trampolines. -/
def gLInv (P : Profile) (l : Linked2) (k : Nat) : CanonHost (E3 P) :=
  match l.imp.imports[k]? with
  | some (_, p) => .lowered (l.wireFid k) (witFt p) {} ⟨2⟩
  | none => Adequacy.someHost P k

theorem hostsSat_gL {l : Linked2} (hn : l.WireNodup) (hw : l.WireTy)
    {s : Store (CanonHost (E3 P))}
    (ht : ∀ (A : Nat) (fi : FuncInst (CanonHost (E3 P))) (h : CanonHost (E3 P)),
      s.funcs[A]? = some fi → fi.code = .host h →
      ∃ k nm p, h = .lowered (l.wireFid k) (witFt p) {} ⟨2⟩ ∧ l.imp.imports[k]? = some (nm, p)) :
    HostsSat (fun h => gLInv P l (gL P l h) = h) s := by
  intro A fi h hA hc
  obtain ⟨k, nm, p, rfl, hk⟩ := ht A fi h hA hc
  have hk' : k < l.imp.imports.length := (List.getElem?_eq_some_iff.mp hk).1
  have hkl : k < l.wire.length := hw.length ▸ hk'
  show gLInv P l (l.trampIdxL (E := E3 P) (.lowered (l.wireFid k) (witFt p) {} ⟨2⟩)) = _
  rw [trampIdxL_wireFid hn hkl]
  simp only [gLInv, hk]

variable {σ : Type} {l : Linked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance}
  {u₀ s₀ : Store Nat} {F₀ : List (FuncInst (CanonHost (E3 P)))} {B : Machine.Config (E3 P) σ}
  {Op₀ Oc₀ : Own} {f : Ii.F.Op}

/-- The shared store of a linked call has only trampolines as host code. -/
theorem hostsSat_lstat (S : LStat P l Ie Ii u₀ F₀ B Op₀) {s : Store (CanonHost (E3 P))}
    (hs : s.funcs = F₀) : HostsSat (fun h => gLInv P l (gL P l h) = h) s :=
  hostsSat_gL S.nodup S.wireTy fun A fi h hA hc => S.tramp A fi h (hs ▸ hA) hc

/-- **A run of the importer's part is a core run of the shared thread**, `LInv` holding at its
end with the same exporter store. -/
theorem LInv.reach_fwd (S : LStat P l Ie Ii u₀ F₀ B Op₀) {y : CoreSt (E3 P)}
    {x : Store Nat × STh} {π : Store Nat} (hI : LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y x π)
    {x' : Store Nat × STh} (hx : Silmaril.Wasm.Game.Reach P x x') :
    ∃ y', Relation.ReflTransGen (CoreStep (E3 P)) y y' ∧
      LInv P l Ie Ii s₀ u₀ F₀ Op₀ Oc₀ f y' x' π := by
  obtain ⟨ρp, Op, ρc, Oc, hL, hR⟩ := hI.rel
  obtain ⟨y', ρc', Oc', hrun, hL', hgr, htc, hfy⟩ :=
    reach_link_fwd (gL P l) (gLInv P l) hx (hostsSat_lstat S hI.funcs) hL
  have hrc : PartRel ρc' Oc' (reloc s₀ x'.1) (Store.mapH (gL P l) y'.1) := by
    have h := hL'.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store] at h
  exact ⟨y', hrun, ⟨⟨ρp, Op, ρc', Oc', hL', Rel4.after_c hR hrc hgr htc⟩,
    hI.fnE.congr (mapH_funcs_eq _ hfy) rfl, hI.wf, hfy.trans hI.funcs,
    hI.run.trans (reach_ssteps hx)⟩⟩

end Inv

/-! ## The exporter's runs -/

section Exp

variable {P : Profile}

/-- **A run of the exporter from its store `π` is a core run of its activation in the shared
store**, the exporter's relation re-established at its end store `π'`. -/
theorem exp_fwd {π κ : Store Nat} {Op₀ Oc₀ : Own} {ρp ρc : Ren} {Op Oc : Own}
    (g : CanonHost (E3 P) → Nat) (gi : Nat → CanonHost (E3 P)) {σ : Store (CanonHost (E3 P))}
    (hs : HostsSat (fun h => gi (g h) = h) σ)
    (hR : Rel4 Op₀ Oc₀ ρp Op ρc Oc (Store.mapH g σ) π κ)
    (hF : FnPre ({} : Store Nat) (Store.mapH g σ) π) {a : Nat} (hO : Op₀.fn a) (xs : List Flat)
    {π' : Store Nat} {t' : STh}
    (run : Silmaril.Wasm.Game.Reach P (π, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs)
      (π', t')) :
    ∃ (e : CoreSt (E3 P)) (ρp' : Ren) (Op' : Own),
      Relation.ReflTransGen (CoreStep (E3 P))
        (σ, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs) e ∧
      LinkSt ({} : Store Nat) ρp' Op' (π', t') (Store.mapH g e.1, e.2) ∧
      Rel4 Op₀ Oc₀ ρp' Op' ρc Oc (Store.mapH g e.1) π' κ ∧
      FnPre ({} : Store Nat) (Store.mapH g e.1) π' ∧ e.1.funcs = σ.funcs := by
  have hL₀ := exp_invoke hR.rp hF (hR.fnp ▸ hO) xs
  obtain ⟨e, ρp', Op', hrun, hL, hgr, htc, hfe⟩ :=
    reach_link_fwd g gi run (y := (σ, Silmaril.Wasm.SingleThreaded.Thread.invokeFlat a xs)) hs hL₀
  have hrel : PartRel ρp' Op' π' (Store.mapH g e.1) := by
    have h := hL.rel.rel
    rwa [Silmaril.Wasm.SingleThreaded.Thread.config_store, reloc_empty] at h
  exact ⟨e, ρp', Op', hrun, hL, Rel4.after_p hR hrel hgr htc, hL.fn, hfe⟩

/-- Flat values are their own image under a code map. -/
theorem map_val_of_flat (M : CMap) : ∀ {vs : List Silmaril.Wasm.Execution.Core.Val} {zs : List Flat},
    vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs → vs.map M.val = vs
  | [], _, _ => rfl
  | v :: vs, zs, h => by
    rw [List.mapM_cons] at h
    cases hv : Silmaril.Wasm.SingleThreaded.toFlat? v with
    | none => simp [hv] at h
    | some z =>
      cases hm : vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
      | none => simp [hv, hm] at h
      | some zs' =>
        have hvv : M.val v = v := by
          cases v with
          | ref r => cases hv
          | num n => rfl
          | vec b => rfl
        rw [List.map_cons, hvv, map_val_of_flat M hm]

/-- **The image of a part finished with flat values returns them.** -/
theorem status_of_values (g : CanonHost (E3 P) → Nat) {s₀ : Store Nat} {ρ : Ren} {O : Own}
    {x : Store Nat × STh} {e : CoreSt (E3 P)} (hL : LinkSt s₀ ρ O x (Store.mapH g e.1, e.2))
    {cvs : List Silmaril.Wasm.Execution.Core.Val}
    (hr : Silmaril.Wasm.Game.ResultAt x.1 x.2 (.values cvs)) {zs : List Flat}
    (hm : cvs.mapM Silmaril.Wasm.SingleThreaded.toFlat? = some zs) :
    (E3 P).status e.1 e.2 = .returned (.values zs) := by
  have hc : (e.2.config e.1).code = Silmaril.Wasm.Execution.Core.vals cvs := by
    rw [← config_code_mapH g e.1 e.2, link_values hL hr, map_val_of_flat _ hm]
  show flatStatus (Silmaril.Wasm.Game.statusP P e.1 e.2) = _
  rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_values hc]
  simp only [flatStatus, hm]

/-- **The image of a trapped part traps.** -/
theorem status_of_trap (g : CanonHost (E3 P) → Nat) {s₀ : Store Nat} {ρ : Ren} {O : Own}
    {x : Store Nat × STh} {e : CoreSt (E3 P)} (hL : LinkSt s₀ ρ O x (Store.mapH g e.1, e.2))
    (hr : Silmaril.Wasm.Game.ResultAt x.1 x.2 .trap) :
    (E3 P).status e.1 e.2 = .returned .trap := by
  have hc : (e.2.config e.1).code = [.trap] := by
    rw [← config_code_mapH g e.1 e.2]
    exact link_trap hL hr
  show flatStatus (Silmaril.Wasm.Game.statusP P e.1 e.2) = _
  rw [Silmaril.Proofs.Wasm.Component.Core3G.statusP_of_trap hc]
  rfl

/-- A related part never ends in an uncaught exception. -/
theorem not_result_throw {H : Type} {s₀ : Store H} {ρ : Ren} {O : Own} {x y : Store H × STh}
    (hL : LinkSt s₀ ρ O x y) {a : Nat}
    (hr : ((x.2).config x.1).code = (Silmaril.Wasm.Execution.Core.Result.throw a).toAdmin) :
    False := by
  obtain ⟨ρ₀, O₀, σ₀, -, -, hc₀⟩ := hL.rel.good
  exact Silmaril.Proofs.Wasm.Game.Linking.Split.Own.not_codeGood_throwing (a := a) hc₀
    (by rw [hr]; simp [Silmaril.Wasm.Execution.Core.Result.toAdmin])

end Exp

/-! ## Doomed threads -/

section Doomed

variable {P : Profile}

/-- **Runs from a thread filled with a trap stay filled with a trap, in the same store.** -/
theorem reach_doomed_cfg {x y : Store Nat × STh} (run : Silmaril.Wasm.Game.Reach P x y) :
    ∀ {E : Silmaril.Wasm.SingleThreaded.Ctx} {f : Silmaril.Wasm.Execution.Core.Frame},
      x.2.config x.1 = ⟨x.1, f, E.fill [.trap]⟩ →
      ∃ E' : Silmaril.Wasm.SingleThreaded.Ctx, y.2.config y.1 = ⟨x.1, f, E'.fill [.trap]⟩ ∧
        y.1 = x.1 := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => intro E f ht; exact ⟨E, ht, rfl⟩
  | @head a b hab _ ih =>
    intro E f ht
    obtain ⟨f', c', hb, hst⟩ := hab
    have hst' : Silmaril.Wasm.Execution.Core.Step P (fun _ _ _ _ => False)
        ⟨a.1, f, E.fill [.trap]⟩ ⟨b.1, f', c'⟩ := ht ▸ hst
    obtain ⟨hs, hf, E', hE'⟩ := Silmaril.Proofs.Wasm.Game.Choice.step_doomed hst'
    have hbc : b.2.config b.1 = ⟨b.1, f, E'.fill [.trap]⟩ := by
      rw [hb]
      simp only at hf hE'
      rw [hf, hE']
      rfl
    obtain ⟨E'', h1, h2⟩ := ih hbc
    simp only at hs
    exact ⟨E'', by rw [h1, hs], h2.trans hs⟩

/-- **A thread filled with a trap never reaches a callout.** -/
theorem reach_doomed_callout {x y : Store Nat × STh} (run : Silmaril.Wasm.Game.Reach P x y)
    {E : Silmaril.Wasm.SingleThreaded.Ctx} {f : Silmaril.Wasm.Execution.Core.Frame}
    (ht : x.2.config x.1 = ⟨x.1, f, E.fill [.trap]⟩) {h : Nat}
    {args : List Silmaril.Wasm.Execution.Core.Val} (hc : Silmaril.Wasm.Game.CalloutAt y.1 y.2 h args) :
    False := by
  obtain ⟨E', hy, -⟩ := reach_doomed_cfg run ht
  obtain ⟨E₁, a, hd⟩ := hc
  rw [hy] at hd
  rw [Silmaril.Wasm.SingleThreaded.Ctx.decompose?_fill_trap] at hd
  cases hd

end Doomed

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
