module

public import Silmaril.Proofs.Wasm.Cfg.RegionTail
public import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.SingleThreaded.Locality
import Silmaril.Wasm.SingleThreaded.Determinism.Head

@[expose] public section

/-!
# Host-free calls do not depend on the caller's frame or the `call_ref` annotation

With no host (`fun _ _ _ _ => False`) and only Wasm functions in the store, a Core run of a call
`vals us ++ [ref.func a, c]` (or of a `FRAME`) to a result ends in the caller's frame, and the same
run exists from any caller frame `g` and any `call_ref` annotation `c'`. Tail calls out of the
frame (`return_call_ref-frame-addr`) are calls again, by the same argument.
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type} {P : Profile}

/-- Every function of the store has Wasm code. -/
def WasmFuncs (s : Store H) : Prop := ∀ fi ∈ s.funcs, ∃ fn, fi.code = .wasm fn

theorem frameExit_step {s : Store H} {fi : Frame} {n : Nat} {is out : List Admin}
    {host : HostSemantics H} (h : FrameExit s fi n is out) (g : Frame) :
    Step P host ⟨s, g, [.frame n fi is]⟩ ⟨s, g, out⟩ := by
  cases h with
  | vals hn => exact Step.frameVals hn
  | ret hn => exact Step.returnFrame hn
  | trap => exact Step.trapFrame
  | throw a => exact Step.throwRefFrame
  | returnCallNull hc => exact Step.returnCallRefFrameNull hc
  | returnCallAddr hc hf he hn => exact Step.returnCallRefFrameAddr hc hf he hn

theorem result_not_frame {r : Result} {n : Nat} {fi : Frame} {X : List Admin} :
    r.toAdmin ≠ [.frame n fi X] := by
  intro h
  have hm : Admin.frame n fi X ∈ r.toAdmin := by rw [h]; simp
  cases r with
  | values vs =>
    simp only [Result.toAdmin, vals, List.mem_map] at hm
    obtain ⟨v, -, hv⟩ := hm
    have := Admin.val?_toAdmin v
    rw [hv] at this; simp [Admin.val?] at this
  | trap => simp [Result.toAdmin] at hm
  | throw t => simp [Result.toAdmin] at hm

theorem result_not_call {r : Result} {us : List Val} {a : Nat} {c : Admin} (hc : c.IsCallRef) :
    r.toAdmin ≠ vals us ++ [.ref (.func a), c] := by
  intro h
  have hm : c ∈ r.toAdmin := by rw [h]; simp
  cases r with
  | values vs =>
    simp only [Result.toAdmin, vals, List.mem_map] at hm
    obtain ⟨v, -, hv⟩ := hm
    have := Admin.val?_toAdmin v
    rw [hv, SingleThreaded.Det.IsCallRef.val_none hc] at this; cases this
  | trap => simp [Result.toAdmin] at hm; subst hm; exact hc
  | throw t =>
    simp [Result.toAdmin] at hm
    rcases hm with rfl | rfl <;> exact hc

theorem wasmFuncs_step {c c' : Config H} (h : Step P (fun _ _ _ _ => False) c c')
    (hw : WasmFuncs c.store) : WasmFuncs c'.store := by
  intro fi hfi
  rw [(SingleThreaded.Step.framesLocal h).1] at hfi
  exact hw fi hfi

/-- **Transport of host-free call runs.** For a run from `c` to a result: if `c` is a `FRAME`,
it ends in `c`'s frame and runs from any outer frame; if `c` is a call, it ends in `c`'s frame
and runs from any caller frame and any `call_ref` annotation. -/
theorem call_transport {c : Config H} {s' : Store H} {f' : Frame} {R : List Admin}
    (h : Steps P (fun _ _ _ _ => False) c ⟨s', f', R⟩) (hR : ∃ r : Result, R = r.toAdmin)
    (hw : WasmFuncs c.store) :
    (∀ m F X, c.code = [.frame m F X] → f' = c.frame ∧
        ∀ g, Steps P (fun _ _ _ _ => False) ⟨c.store, g, [.frame m F X]⟩ ⟨s', g, R⟩) ∧
    (∀ us a cr (fi : FuncInst H) ps rs, c.code = vals us ++ [.ref (.func a), cr] → cr.IsCallRef →
        c.store.funcs[a]? = some fi → Expand fi.type (.func ps rs) → us.length = ps.length →
        f' = c.frame ∧ ∀ g cr', cr'.IsCallRef →
          Steps P (fun _ _ _ _ => False) ⟨c.store, g, vals us ++ [.ref (.func a), cr']⟩
            ⟨s', g, R⟩) := by
  obtain ⟨r, rfl⟩ := hR
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    refine ⟨fun m F X hc => ?_, fun us a cr fi ps rs hc hcr => ?_⟩
    · exact absurd hc result_not_frame
    · exact absurd hc (result_not_call hcr)
  | @head c c₁ hstep hrest ih =>
    obtain ⟨s, f, code⟩ := c
    have ih' := ih (wasmFuncs_step hstep hw)
    refine ⟨fun m F X hc => ?_, fun us a cr fi ps rs hc hcr hfi he hn => ?_⟩
    · simp only at hc; subst hc
      rcases Step.frame_inv hstep with ⟨s₁, F', X', hin, rfl⟩ | ⟨out, hx, rfl⟩
      · obtain ⟨hf, hg⟩ := ih'.1 m F' X' rfl
        exact ⟨hf, fun g => .head (Step.ctxtFrame hin) (hg g)⟩
      · cases hx with
        | returnCallAddr hc' hf' he' hn' =>
          obtain ⟨hf, hg⟩ := ih'.2 _ _ _ _ _ _ rfl (isCallRef_retToCallIn hc' F.module) hf' he' hn'
          exact ⟨hf, fun g => .head (frameExit_step (.returnCallAddr hc' hf' he' hn') g)
            (hg g _ (isCallRef_retToCallIn hc' F.module))⟩
        | vals hn' =>
          obtain ⟨rfl, rfl, hR⟩ := steps_result (r := .values _) hrest
          exact ⟨rfl, fun g => by rw [hR]; exact .single (frameExit_step (.vals hn') g)⟩
        | ret hn' =>
          obtain ⟨rfl, rfl, hR⟩ := steps_result (r := .values _) hrest
          exact ⟨rfl, fun g => by rw [hR]; exact .single (frameExit_step (.ret hn') g)⟩
        | trap =>
          obtain ⟨rfl, rfl, hR⟩ := steps_result (r := .trap) hrest
          exact ⟨rfl, fun g => by rw [hR]; exact .single (frameExit_step .trap g)⟩
        | throw a =>
          obtain ⟨rfl, rfl, hR⟩ := steps_result (r := .throw a) hrest
          exact ⟨rfl, fun g => by rw [hR]; exact .single (frameExit_step (.throw a) g)⟩
        | returnCallNull hc' =>
          obtain ⟨rfl, rfl, hR⟩ := steps_result (r := .trap) hrest
          exact ⟨rfl, fun g => by rw [hR]; exact .single (frameExit_step (.returnCallNull hc') g)⟩
    · simp only at hc hfi; subst hc
      obtain ⟨fn, hcode⟩ := hw fi (List.mem_of_getElem? hfi)
      have hc₁ := Step.callRef_wasm_inv_exact hcr hfi hcode he hn hstep
      subst hc₁
      obtain ⟨hf, hg⟩ := ih'.1 _ _ _ rfl
      exact ⟨hf, fun g cr' hcr' => .head (Step.callRefFunc hcr' hfi he hn hcode) (hg g)⟩

/-- **A complete oracle turns a Core call into a region call**: with `CallCompleteG`, a Core run
of the callee (`vals us ++ [ref.func a, call_ref]`, from a guarded store and arguments) to a result
ends in the caller's frame, and `call x` runs as `RunC.call` (continuing on the results),
`RunC.callTrap` or `RunC.callThrow` says. -/
theorem call_of_core {host : HostSemantics H} {G : Store H → Nat → List Val → Prop}
    {C : Abstract.CallRel H} (hC : CallCompleteG P host G C) {s s₁ : Store H} {f f₁ : Frame}
    {ws us : List Val} {x : FuncIdx} {a : Nat} {fi : FuncInst H} {ps rs : List CValType}
    {code : List Admin} {r : Result} (hfi : s.func? f x = some (a, fi))
    (hty : DefType.funcType? fi.type = some (ps, rs)) (hn : us.length = ps.length)
    (hG : G s a us)
    (hs : Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
      ⟨s₁, f₁, r.toAdmin⟩) :
    f₁ = f ∧
      (∀ vs, r = .values vs → ∀ {s' : Store H} {f' : Frame} {o : Out},
        RunC P host C s₁ f (ws ++ vs) code s' f' o →
          RunC P host C s f (ws ++ us) (.plain (.call x) :: code) s' f' o) ∧
      (r = .trap → RunC P host C s f (ws ++ us) (.plain (.call x) :: code) s₁ f .trap) ∧
      (∀ t, r = .throw t →
        RunC P host C s f (ws ++ us) (.plain (.call x) :: code) s₁ f (.throw t)) := by
  obtain ⟨hf, fl, hcall, hres⟩ := hC s s₁ f f₁ a fi ps rs us (.callRefType fi.type) r hG trivial (func?_inv hfi).2 hty hn hs
  refine ⟨hf, fun vs hv s' f' o hk => ?_, fun ht => ?_, fun t ht => ?_⟩
  · subst hv
    obtain ⟨ws', hw, rfl⟩ := hres
    exact .call hfi hty hn hcall hw hk
  · subst ht
    simp only [FlowRes] at hres; subst hres
    exact .callTrap hfi hty hn hcall
  · subst ht
    simp only [FlowRes] at hres; subst hres
    exact .callThrow hfi hty hn hcall

/-- The configurations of a diverging host-free call, up to the caller's frame and the
`call_ref` annotation: a `FRAME` that diverges from some outer frame, or a call that diverges
from some caller frame with some annotation. -/
def DivCall (c : Config H) : Prop :=
  WasmFuncs c.store ∧
    ((∃ (m : Nat) (F : Frame) (X : List Admin) (f : Frame), c.code = [.frame m F X] ∧
        Diverges P (fun _ _ _ _ => False) ⟨c.store, f, [.frame m F X]⟩) ∨
      ∃ (us : List Val) (a : Nat) (cr : Admin) (fi : FuncInst H) (ps rs : Ty (.list .val))
        (f : Frame) (cr' : Admin), c.code = vals us ++ [.ref (.func a), cr] ∧
        cr.IsCallRef ∧ c.store.funcs[a]? = some fi ∧ Expand fi.type (.func ps rs) ∧
        us.length = ps.length ∧ cr'.IsCallRef ∧
        Diverges P (fun _ _ _ _ => False) ⟨c.store, f, vals us ++ [.ref (.func a), cr']⟩)

theorem divCall_step {c : Config H} (h : DivCall (P := P) c) :
    ∃ d, Step P (fun _ _ _ _ => False) c d ∧ DivCall (P := P) d := by
  obtain ⟨s, g, code⟩ := c
  obtain ⟨hw, ⟨m, F, X, f, hc, hd⟩ | ⟨us, a, cr, fi, ps, rs, f, cr', hc, hcr, hfi, he, hn, hcr',
    hd⟩⟩ := h
  · simp only at hc hd hw; subst hc
    obtain ⟨c₁, hs, hd₁⟩ := hd.unfold
    rcases Step.frame_inv hs with ⟨s₁, F', X', hin, rfl⟩ | ⟨out, hx, rfl⟩
    · exact ⟨⟨s₁, g, [.frame m F' X']⟩, Step.ctxtFrame hin,
        wasmFuncs_step (c := ⟨s, F, X⟩) (c' := ⟨s₁, F', X'⟩) hin hw, .inl ⟨m, F', X', f, rfl, hd₁⟩⟩
    · cases hx with
      | returnCallAddr hc' hf' he' hn' =>
        exact ⟨_, frameExit_step (.returnCallAddr hc' hf' he' hn') g, hw,
          .inr ⟨_, _, _, _, _, _, f, _, rfl, isCallRef_retToCallIn hc' F.module, hf', he', hn',
            isCallRef_retToCallIn hc' F.module, hd₁⟩⟩
      | vals hn' =>
        obtain ⟨_, h₂, -⟩ := hd₁.unfold
        exact absurd h₂ (Step.result_stuck (.values _))
      | ret hn' =>
        obtain ⟨_, h₂, -⟩ := hd₁.unfold
        exact absurd h₂ (Step.result_stuck (.values _))
      | trap =>
        obtain ⟨_, h₂, -⟩ := hd₁.unfold
        exact absurd h₂ (Step.result_stuck .trap)
      | throw a =>
        obtain ⟨_, h₂, -⟩ := hd₁.unfold
        exact absurd h₂ (Step.result_stuck (.throw a))
      | returnCallNull hc' =>
        obtain ⟨_, h₂, -⟩ := hd₁.unfold
        exact absurd h₂ (Step.result_stuck .trap)
  · simp only at hc hd hw hfi; subst hc
    obtain ⟨fn, hcode⟩ := hw fi (List.mem_of_getElem? hfi)
    obtain ⟨c₁, hs, hd₁⟩ := hd.unfold
    have hc₁ := Step.callRef_wasm_inv_exact hcr' hfi hcode he hn hs
    subst hc₁
    exact ⟨_, Step.callRefFunc hcr hfi he hn hcode, hw, .inl ⟨_, _, _, f, rfl, hd₁⟩⟩

/-- **Transport of diverging host-free calls**: on a store of Wasm functions, a call of a typed
function that diverges from one caller frame with one `call_ref` annotation diverges from every
caller frame with every annotation. Tail calls out of the callee's frame are calls again. -/
theorem div_call_transport {s : Store H} {f : Frame} {us : List Val} {a : Nat} {cr : Admin}
    {fi : FuncInst H} {ps rs : Ty (.list .val)} (hw : WasmFuncs s) (hcr : cr.IsCallRef)
    (hfi : s.funcs[a]? = some fi) (he : Expand fi.type (.func ps rs)) (hn : us.length = ps.length)
    (h : Diverges P (fun _ _ _ _ => False) ⟨s, f, vals us ++ [.ref (.func a), cr]⟩)
    (g : Frame) {cr' : Admin} (hcr' : cr'.IsCallRef) :
    Diverges P (fun _ _ _ _ => False) ⟨s, g, vals us ++ [.ref (.func a), cr']⟩ :=
  InfiniteTrace.coinduct (DivCall (P := P)) (fun _ hc => divCall_step hc)
    ⟨hw, .inr ⟨us, a, cr', fi, ps, rs, f, cr, rfl, hcr', hfi, he, hn, hcr, h⟩⟩

end Silmaril.Wasm.Cfg.Proofs.Region
