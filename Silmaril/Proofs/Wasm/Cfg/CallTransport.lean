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

end Silmaril.Wasm.Cfg.Proofs.Region
