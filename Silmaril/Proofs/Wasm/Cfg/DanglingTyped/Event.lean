module

public import Silmaril.Proofs.Wasm.Cfg.DanglingTyped.Pres
public import Silmaril.Wasm.Abstract.HostCall.Thms
public import Silmaril.Wasm.SingleThreaded.Locality

@[expose] public section

/-!
# The relaxed invariant across host answers (proofs)

A host answer that keeps the store and whose values have the callee's result types keeps
`ConfigOkD`, whatever exception address it throws, dangling ones included (`ConfigOkD.event`).
The witness is first given enough pads to name the thrown address (`ghost_extend`); then the same
answer, typed on the witness, is one of the typed host `ghostHost`, and Core preservation with a
typed host (`ContextTyped.steps_typed`) types the answered configuration on the witness.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Games.Abstract (Call)
open Silmaril.Wasm.Cfg.DanglingTyped
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Execution.Core.Sim (ContextTyped)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (Ctx decompose?)

variable {H : Type} {P : Profile}

/-! ## Evaluation contexts of host calls -/

theorem fill_approx {N : Nat} (E : Ctx) {xs ys : List Admin} (h : CodeApprox N xs ys) :
    CodeApprox N (E.fill xs) (E.fill ys) := by
  induction E with
  | top pre rest => exact ((CodeApprox.refl _).append h).append (.refl _)
  | label _ _ _ _ _ ih => exact ((CodeApprox.refl _).append (.cons (.label _ _ ih) .nil)).append (.refl _)
  | handler _ _ _ _ _ ih =>
    exact ((CodeApprox.refl _).append (.cons (.handler _ _ ih) .nil)).append (.refl _)
  | frame _ _ _ _ _ ih =>
    exact ((CodeApprox.refl _).append (.cons (.frame _ _ ih) .nil)).append (.refl _)

theorem fill_supp {k : Nat} (E : Ctx) {xs ys : List Admin} (hx : ∀ a ∈ E.fill xs, ASupp k a)
    (hy : ∀ a ∈ ys, ASupp k a) : ∀ a ∈ E.fill ys, ASupp k a := by
  induction E with
  | top pre rest =>
    simp only [Ctx.fill, List.forall_mem_append] at hx ⊢
    exact ⟨⟨hx.1.1, hy⟩, hx.2⟩
  | label _ _ _ _ _ ih =>
    simp only [Ctx.fill, List.forall_mem_append, List.forall_mem_singleton] at hx ⊢
    obtain ⟨hc, hb⟩ := asupp_label_inv hx.1.2
    exact ⟨⟨hx.1.1, .label _ hc (ih hb)⟩, hx.2⟩
  | handler _ _ _ _ _ ih =>
    simp only [Ctx.fill, List.forall_mem_append, List.forall_mem_singleton] at hx ⊢
    exact ⟨⟨hx.1.1, .handler _ _ (ih (asupp_handler_inv hx.1.2))⟩, hx.2⟩
  | frame _ _ _ _ _ ih =>
    simp only [Ctx.fill, List.forall_mem_append, List.forall_mem_singleton] at hx ⊢
    obtain ⟨hf, hb⟩ := asupp_frame_inv hx.1.2
    exact ⟨⟨hx.1.1, .frame _ hf (ih hb)⟩, hx.2⟩

/-! ## More pads -/

theorem reach_extend {s : Store H} {T : List TagInst} {X Y : List ExnInst}
    (hY : ∀ y ∈ Y, y.fields = []) {u w : FieldVal}
    (h : ImmutReachable (gst s T (X ++ Y)) u w) : ImmutReachable (gst s T X) u w := by
  induction h with
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | refStruct hs he hi hfv => exact .refStruct hs he hi hfv
  | refArray hs he hfv => exact .refArray hs he hfv
  | @refExn a i x v hs hv =>
    have hs' : (X ++ Y)[a]? = some x := hs
    rcases Nat.lt_or_ge a X.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hs'
      exact .refExn (s := gst s T X) hs' hv
    · rw [List.getElem?_append_right hge] at hs'
      rw [hY x (List.mem_of_getElem? hs')] at hv
      simp at hv
  | refExtern r => exact .refExtern r

theorem not_reach_beyond {s : Store H} {T : List TagInst} {X : List ExnInst} {a : Nat}
    (ha : X.length ≤ a) {u w : FieldVal} (h : ImmutReachable (gst s T X) u w) :
    u ≠ .val (.ref (.exn a)) := by
  induction h with
  | trans _ _ ih₁ _ => exact ih₁
  | refExn hs _ =>
    intro he
    cases he
    have := (List.getElem?_eq_some_iff.1 hs).1
    exact absurd ha (by simp at this ⊢; omega)
  | _ => intro he; cases he

/-- **A witness with as many pads as needed.** -/
theorem ghost_extend {s : Store H} {T : List TagInst} {X : List ExnInst} {f : Frame}
    {code : List Admin} (hg : GhostOk s T X) (hct : ContextTyped ⟨gst s T X, f, code⟩) (M : Nat) :
    ∃ X', M ≤ X'.length ∧ GhostOk s T X' ∧ ContextTyped ⟨gst s T X', f, code⟩ := by
  obtain ⟨p, hp⟩ : ∃ p, X[s.exns.length]? = some p := ⟨_, List.getElem?_eq_getElem hg.lt⟩
  have hpad := hg.pad _ p (Nat.le_refl _) hp
  have hS := storeOk_of_contextTyped hct
  have hpY : ∀ y ∈ List.replicate M p, y.fields = [] := by
    intro y hy; rw [List.eq_of_mem_replicate hy]; exact hpad.2
  have hw : Widen (gst s T X) (gst s T (X ++ List.replicate M p)) :=
    ⟨rfl, List.prefix_refl _, fun a y hy =>
      ⟨y, by show (X ++ _)[a]? = _; rw [List.getElem?_append_left
        (List.getElem?_eq_some_iff.1 hy).1]; exact hy⟩⟩
  have hS' : StoreOk (gst s T (X ++ List.replicate M p)) := by
    refine ⟨hS.tags, fun gi h => hw.globalInstOk (hS.globals gi h), hS.mems,
      fun ti h => hw.tableInstOk (hS.tables ti h), fun fi h => hw.funcInstOk (hS.funcs fi h),
      fun ei h => hw.elemInstOk (hS.elems ei h), fun si h => hw.structInstOk (hS.structs si h),
      fun ai h => hw.arrayInstOk (hS.arrays ai h), ?_,
      fun a ha hr => hS.acyclicStructs a ha (reach_extend hpY hr),
      fun a ha hr => hS.acyclicArrays a ha (reach_extend hpY hr), ?_, hS.structsClosed,
      hS.arraysClosed⟩
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · obtain ⟨ti, ts, h1, h2, h3⟩ := hS.exns x hx
        exact ⟨ti, ts, h1, h2, h3.imp fun _ _ h => hw.valOk h⟩
      · rw [List.eq_of_mem_replicate hx]
        obtain ⟨ti, ts, h1, h2, h3⟩ := hS.exns p (List.mem_of_getElem? hp)
        exact ⟨ti, ts, h1, h2, h3.imp fun _ _ h => hw.valOk h⟩
    · intro a ha hr
      have hr' := reach_extend hpY hr
      rcases Nat.lt_or_ge a X.length with hlt | hge
      · exact hS.acyclicExns a hlt hr'
      · exact not_reach_beyond hge hr' rfl
  refine ⟨X ++ List.replicate M p, by simp, ⟨hg.tags, by simp; have := hg.lt; omega, ?_, ?_⟩,
    contextTyped_widen hw hS' hct⟩
  · intro a e he
    obtain ⟨e', h1, h2, h3⟩ := hg.real a e he
    refine ⟨e', ?_, h2, h3.imp fun _ _ h => ValApprox.mono (by simp) h⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h1).1]; exact h1
  · intro a e' ha he'
    rcases Nat.lt_or_ge a X.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at he'
      exact hg.pad a e' ha he'
    · rw [List.getElem?_append_right hge] at he'
      rw [List.eq_of_mem_replicate (List.mem_of_getElem? he')]
      exact hpad

/-! ## The typed witness host -/

/-- **The typed witness host**: it keeps the store and answers results of the callee's types. -/
def ghostHost : HostSemantics H := fun h s _ out =>
  out = .diverged ∨ ∃ r, out = .returned s r ∧ ∀ fi ∈ s.funcs, fi.code = .host h →
    ∀ ps rs, Expand fi.type (.func ps rs) → ResultTyped s r rs.toList

theorem hostTyped_ghostHost : Abstract.HostTyped (ghostHost (H := H)) := by
  intro s fi h vs ps rs hs hfi hc he _ out hout
  rcases hout with rfl | ⟨r, rfl, hr⟩
  · trivial
  · exact ⟨hs, Extend.refl hs, hr fi hfi hc ps rs he⟩

/-- **A store-keeping host answer whose values are typed keeps the relaxed invariant**, every
exception address included. -/
theorem ConfigOkD.event {host : HostSemantics H} {c c' : Config H} {e : Call (Abstract.wasmHostSig H)}
    (hc : ConfigOkD c) (h : Abstract.HEvStep P host c (some e) c') (hsp : e.2.1 = e.1.2.1)
    (hres : ∀ fi ∈ c.store.funcs, fi.code = .host e.1.1 → ∀ ps rs,
      Expand fi.type (.func ps rs) → ResultTypedD c.store e.2.2 rs.toList) :
    ConfigOkD c' := by
  obtain ⟨hF, hf, hs, hheap, T, X₀, hg₀, hct₀⟩ := hc
  obtain ⟨E, a, hdec, hst, -, rfl⟩ := h
  rw [hsp, hst]
  obtain ⟨⟨hh, s₀, us⟩, ⟨s₁, r⟩⟩ := e
  dsimp only at hdec hst hres ⊢
  obtain ⟨fi, yy, ps, rs, hfi, hcode, hyy, hexp, hlen, hcodeE⟩ :=
    SingleThreaded.decompose?_sound hdec
  have hsuppE : ∀ x ∈ E.fill r.toAdmin, ASupp c.store.tags.length x :=
    fill_supp E (hcodeE ▸ hs) (asupp_result r)
  refine ⟨hF, hf, hsuppE, hheap, ?_⟩
  -- enough pads for a thrown address
  obtain ⟨X, hM, hg, hct⟩ := ghost_extend hg₀ hct₀
    (match r with | .throw t => t + 1 | _ => 0)
  refine ⟨T, X, hg, ?_⟩
  have hw := GhostOk.widen hg
  have hghost : ghostHost hh (gst c.store T X) us (.returned (gst c.store T X) r) := by
    refine .inr ⟨r, rfl, fun fi' hfi' hc' ps' rs' he' => ?_⟩
    have := hres fi' hfi' hc' ps' rs' he'
    cases r with
    | values vs => exact this.imp fun _ _ h => hw.valOk h
    | throw t =>
      simp only at hM
      exact ⟨_, List.getElem?_eq_getElem (l := X) (by omega)⟩
    | trap => trivial
  have hev : Abstract.HEvStep P ghostHost ⟨gst c.store T X, c.frame, c.code⟩
      (some ⟨(hh, gst c.store T X, us), (gst c.store T X, r)⟩)
      ⟨gst c.store T X, c.frame, E.fill r.toAdmin⟩ := by
    refine ⟨E, a, ?_, rfl, hghost, rfl⟩
    show decompose? (gst c.store T X) c.code = some (E, a, hh, us)
    rw [SingleThreaded.decompose?_congr (s := c.store) (s' := gst c.store T X) rfl]
    exact hdec
  exact Abstract.ContextTyped.steps_typed hostTyped_ghostHost hct
    (Relation.ReflTransGen.single (Abstract.hEvStep_step hev))

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
