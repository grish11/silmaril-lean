module

public import Silmaril.Wasm.Abstract.ExposePTyped.Defs
public import Silmaril.Wasm.Execution.Core.Soundness.Instantiation
public import Silmaril.Wasm.Execution.Core.Soundness.TableMemoryTyping

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePTyped.Thms`: at every run state a typed interface
describes (`Realizes`), typed code is a typed problem (`Interp.TypedP`). The Core configuration
is typed in context by closing the code's labels with `label_n{} … unreachable` and its frame
with `frame_n{f}` under the empty frame: `unreachable` takes the code's result stack to each
label's (and the return) type.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePTyped

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Interp Silmaril.Wasm.Abstract.ExposePStruct Silmaril.Wasm.Abstract.ExposePTyped
open Silmaril.Wasm.Abstract.CallXT (TyTypes)

variable {H : Type}

/-- What a frame typing fixes of its context. -/
theorem frame_ctx {s : Store H} {f : Frame} {C₀ : Context} (hF : FrameOk s f C₀) :
    C₀.labels = [] ∧ C₀.return_ = none ∧ C₀.locals.length = f.locals.length ∧
      TyTypes f.module := by
  obtain ⟨C', lts, hm, hl, rfl⟩ := hF
  cases hm with
  | mk htypes =>
    exact ⟨rfl, rfl, by simp [hl.length_eq],
      fun y d h => htypes d (List.mem_of_getElem? h)⟩

theorem resultOk_of_empty {Δ : TypeCtx} {ts : List CValType} (h : ResultOk {} ts) :
    ResultOk Δ ts := fun t ht => TyOk.of_empty Δ (h t ht)

/-- `code ++ [unreachable]` ends at any valid type. -/
theorem append_unreachable {s : Store H} {C : Context} {code : List Admin}
    {ts ts' : List CValType} (h : AdminsOk s C code (.plain [] ts))
    (hts : ResultOk C.toTypeCtx ts) (hts' : ResultOk C.toTypeCtx ts') :
    AdminsOk s C (code ++ [.plain .unreachable]) (.plain [] ts') := by
  have hu : AdminsOk s (C.initLocals []) [.plain .unreachable] (.plain ts ts') :=
    .single (.plain (.parametric (.unreachable ⟨hts, hts', by simp⟩)))
  simpa using AdminsOk.append (xs₁ := []) h (by simp) hu

/-- The empty frame is typed. -/
theorem frameOk_empty {s : Store H} : ∃ C : Context, FrameOk s ({} : Frame) C := by
  have hmi : ModuleInstOk s ({} : ModuleInst)
      { types := [], recs := [], tags := [], globals := [], mems := [], tables := [],
        funcs := [], datas := ([] : List Nat).map (fun _ => ()), elems := [],
        refs := List.range 0 } :=
    ModuleInstOk.mk (k := 0) (by simp) .nil .nil .nil .nil .nil (by simp) .nil (by simp)
      (by simp) (by simp) (by simp)
  exact ⟨_, _, [], hmi, .nil, rfl⟩

/-- **Code typed under labels and a return type is typed in context**, in a typed frame. -/
theorem ctxTyped_of_labels {s : Store H} {f : Frame} {C₀ : Context} {R : List CValType}
    (hs : StoreOk s) (hF : FrameOk s f C₀) (hR : ResultOk {} R) :
    ∀ (L : List (List CValType)), (∀ l ∈ L, ResultOk {} l) →
      ∀ (code : List Admin) (ts : List CValType), ResultOk C₀.toTypeCtx ts →
        AdminsOk s { C₀ with labels := L, return_ := some R } code (.plain [] ts) →
          Sim.ContextTyped ⟨s, f, code⟩
  | [], _, code, ts, hts, h => by
    obtain ⟨hl0, -, -, -⟩ := frame_ctx hF
    have hu := append_unreachable h hts (resultOk_of_empty hR)
    have e : ({ C₀ with labels := [], return_ := some R } : Context) =
        { C₀ with return_ := some R } := by
      rw [hl0]
    rw [e] at hu
    obtain ⟨Ce, hCe⟩ := frameOk_empty (s := s)
    have hfr := AdminsOk.single' (AdminOk.frame (C := Ce) hF rfl hu hR) (resultOk_of_empty hR)
    have hc : Sim.ContextTyped ⟨s, f, code ++ [.plain .unreachable]⟩ :=
      ⟨.frame R.length {} [] [] .hole, R, Ce, ⟨hs, hCe⟩, by
        simpa [Sim.ActiveCtx.plug, vals] using hfr⟩
    exact Sim.ContextTyped.suffix hc
  | L₀ :: L', hL, code, ts, hts, h => by
    have hL₀ : ResultOk C₀.toTypeCtx L₀ := resultOk_of_empty (hL L₀ (by simp))
    have hu := append_unreachable h hts hL₀
    have hcont : AdminsOk s ({ C₀ with labels := L', return_ := some R } : Context)
        (expression []) ⟨L₀, [], L₀⟩ := by
      simpa [expression] using AdminsOk.frame (ts := L₀)
        (AdminsOk.nil (s := s) (C := ({ C₀ with labels := L', return_ := some R } : Context))) hL₀
    have hlab := AdminsOk.single' (AdminOk.label (n := L₀.length) rfl hcont hu) hL₀
    have ih := ctxTyped_of_labels hs hF hR L' (fun l hl => hL l (by simp [hl])) _ L₀ hL₀ hlab
    have ih' : Sim.ContextTyped ⟨s, f, vals [] ++ [.label L₀.length [] (code ++
        [.plain .unreachable])] ++ []⟩ := by simpa [vals] using ih
    exact Sim.ContextTyped.suffix (Sim.ContextTyped.label ih')

variable {Γ : Ctx H}

/-- **Typed code is a typed problem** at every run state its interface describes. -/
theorem tmor_typedP {I J : TIface} {ft : Bool} {es : List BExpr} {s : Store H} {f : Frame}
    {stk : List Val} (h : TMor Γ I J ft es) (hr : Realizes Γ I s f stk) (hI : I.Ok)
    (hJ : J.Ok) : TypedP Γ.tags s f stk es := by
  obtain ⟨-, xs, -, hC, ht, hc⟩ := h
  obtain ⟨hg, hs, hfm, ⟨C₀, hF, hIC⟩, ⟨R, hR, hRok⟩, hL, hstk⟩ := hr
  obtain ⟨-, -, hn0, hTT⟩ := frame_ctx hF
  have hJ' : ResultOk I.C.toTypeCtx J.ts := by
    have := hJ; unfold TIface.Ok at this; rwa [hC, Context.initLocals_toTypeCtx] at this
  have h1 : AdminsOk s I.C (vals stk.reverse) (.plain [] I.ts) := AdminsOk.of_vals hstk hI
  have h2 : AdminsOk s I.C (expression (BExpr.lowerList es)) ⟨I.ts, xs, J.ts⟩ :=
    AdminsOk.of_instrsOk ht
  have h3 : AdminsOk s I.C (vals stk.reverse ++ expression (BExpr.lowerList es)) ⟨[], xs, J.ts⟩ := by
    simpa using AdminsOk.append (xs₁ := []) h1 (by simp) h2
  have h4 : AdminsOk s I.C (vals stk.reverse ++ expression (BExpr.lowerList es))
      (.plain [] J.ts) :=
    AdminsOk.sub h3 ⟨ResultSub.refl _ _, ResultSub.refl _ _, by simp⟩ ⟨by simp, hJ', by simp⟩
  have hnl : f.locals.length = I.C.locals.length := by
    rw [hIC]; exact hn0.symm
  generalize hLs : I.C.labels = Ls at hIC hL
  rw [hR] at hIC
  have hct := ctxTyped_of_labels hs hF hRok Ls hL _ J.ts
    (by have := hJ'; rw [hIC] at this; exact this) (by rw [hIC] at h4; exact h4)
  refine ⟨[], (I.C.labels.map List.length), (I.C.return_.getD []).length, ftOut ft J.ts.length,
    hg.1 ▸ Γ.storeChk, ?_, by simpa using hct, hTT, hg.2⟩
  have hsl : stk.length = I.ts.length := by
    simpa using hstk.length_eq
  rw [hg.1, hfm, hnl, hsl]
  exact hc

end Silmaril.Proofs.Wasm.Abstract.ExposePTyped
