module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.Conv

/-!
# Divergence with the empty log (proofs)

* `descends_tail`: a body ending, in the closed canonical semantics, in a pending tail call is a
  descent of the canonical module to the tail callee with no import call (`closed_conv`: the body
  run is a logged run resolving to the empty log; the tail call is the open call at the frame);
* `div_of_funDivXP`: a typed call diverging at the frame (`FunDivXP`) has the behaviour
  `([], div)` in `wasmEvFunDXP`: its chain of frame-level tail calls reaches a body diverging
  host-free (`LDLwXP` by `LogDivXP.div`, at the end of a descent path), or goes on forever (an
  infinite descent chain with no import call, `Shape.closeD`), by choice;
* `evRun_nil_div`: a Core run of a typed invocation with no host event, then host-free divergence,
  is `([], div)` in `wasmEvFunDXP` (`funDivXP_of_invoke_diverges`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP Silmaril.Wasm.Abstract.XDivergeP
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Wasm.Binaryen (BExpr liftInstrs Flow)

variable {H : Type}

/-- **A body ending in a pending tail call is a descent to the tail callee**, with no import
call. -/
theorem descends_tail {s s₁ : Store H} {a a' n : Nat} {vs args : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} {f₂ : Frame} (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn) (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : EvalOXP closedCallXP s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body)
      (s₁, f₂, .tail a' args n)) :
    Shape.Descends wasmHOpenXP Cl ⟨a, (vs, s)⟩ [] ⟨a', (args, s₁)⟩ := by
  obtain ⟨l, d, hl⟩ := closed_conv hbody (by rintro ⟨⟩)
  exact ⟨((l ++ [OCall.mk a' args s₁ (.inl []) s₁]).map OCall.lift,
    Abstract.tailAns rs.length n (.inl []) s₁),
    .inr (.inl ⟨fi, fn, ps, rs, s₁, s₁, f₂, a', n, args, .inl [], l, hf, hcode, hty, d, rfl⟩),
    l.map OCall.lift, (.inl [], s₁), [], by rw [List.map_append]; rfl, hl⟩

theorem descPath_snoc {x y z : (wasmHShape H).self.Op} {q : List (Call (wasmHostSig H))}
    (hp : Shape.DescPath wasmHOpenXP Cl x q y) (hd : Shape.Descends wasmHOpenXP Cl y [] z) :
    Shape.DescPath wasmHOpenXP Cl x q z := by
  induction hp with
  | refl x => simpa using Shape.DescPath.step hd (.refl z)
  | step h _ ih => exact .step h (ih hd)

/-- A call whose function has a function type. -/
def Typed (z : (wasmHShape H).self.Op) : Prop :=
  ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), z.2.2.funcs[z.1]? = some fi ∧
    Validation.DefType.funcType? fi.type = some (ps, rs)

/-- **A typed call diverging at the frame has the behaviour `([], div)`.** -/
theorem div_of_funDivXP {x : (wasmHShape H).self.Op} (hx : Typed x)
    (hd : FunDivXP x.2.2 x.1 x.2.1) : ([], .div) ∈ wasmEvFunDXP x.2.2 (x.1, x.2.1) := by
  classical
  let G : (wasmHShape H).self.Op → Prop := fun z =>
    Shape.DescPath wasmHOpenXP Cl x [] z ∧ FunDivXP z.2.2 z.1 z.2.1 ∧ Typed z
  by_cases hb : ∃ (z : (wasmHShape H).self.Op) (fi : FuncInst H) (fn : Func), G z ∧ z.2.2.funcs[z.1]? = some fi ∧
      fi.code = .wasm fn ∧
      EvalDivXP z.2.2 (Frame.forCall fi.module z.2.1 fn.locals) [] (liftInstrs fn.body)
  · obtain ⟨z, fi, fn, ⟨hp, -, -⟩, hf, hcode, hdiv⟩ := hb
    exact .inr ⟨rfl, z, [], [], [], hp, ⟨fi, fn, [], hf, hcode, .div hdiv, rfl⟩, .nil, rfl⟩
  · have step : ∀ z, G z → ∃ y, Shape.Descends wasmHOpenXP Cl z [] y ∧ G y := by
      rintro z ⟨hp, hz, fi₀, ps, rs, hf₀, hty⟩
      rcases funDivXP_iff_step.1 hz with ⟨hf, hcode, hbd⟩ | ⟨hf, hcode, hbody, hy⟩
      · exact (hb ⟨z, _, _, ⟨hp, hz, fi₀, ps, rs, hf₀, hty⟩, hf, hcode, hbd⟩).elim
      · rw [hf₀] at hf; cases hf
        have hD := descends_tail hf₀ hcode hty hbody
        obtain ⟨fi', ps', rs', hf', hty', -⟩ := tail_wf hbody _ _ _ rfl
        exact ⟨_, hD, descPath_snoc hp hD, hy, fi', ps', rs', hf', hty'⟩
    let next : {z // G z} → {z // G z} := fun z =>
      ⟨Classical.choose (step z.1 z.2), (Classical.choose_spec (step z.1 z.2)).2⟩
    let g : Nat → (wasmHShape H).self.Op := fun n => (next^[n] ⟨x, .refl x, hd, hx⟩).1
    refine .inl (.inr ⟨rfl, g, fun _ => [], 0, rfl, fun n => ?_, fun _ _ => rfl, rfl⟩)
    have := (Classical.choose_spec (step (next^[n] ⟨x, .refl x, hd, hx⟩).1
      (next^[n] ⟨x, .refl x, hd, hx⟩).2)).1
    simpa only [g, Function.iterate_succ_apply'] using this

/-- A labelled run with no event, then host-free divergence, is host-free divergence. -/
theorem evRun_nil_diverges {P : Numerics.Profile} {host : HostSemantics H} {c c' : Config H}
    (h : EvRun P host c [] c') (hd : Diverges P (fun _ _ _ _ => False) c') :
    Diverges P (fun _ _ _ _ => False) c := by
  generalize hcs : ([] : List (Call (wasmHostSig H))) = cs at h
  induction h with
  | refl => exact hd
  | silent hs _ ih =>
    rcases hs with hs | ⟨rfl, -⟩
    · exact Silmaril.InfiniteTrace.fold hs (ih hd hcs)
    · exact ih hd hcs
  | event => cases hcs

/-- **A Core run with no host event, then host-free divergence, is `([], div)`** (deterministic
profile, typed invocations, stores that may hold host functions). -/
theorem evRun_nil_div {o : GrowOracle} {host : HostSemantics H} {tags : List TagInst}
    {s : Store H} {a : Nat} {vs : List Val} {c' : Config H} (hs : StoreOk s)
    (hok : InvokeOk s a vs) (hS : Interp.StoreChkE (Interp.ehExt tags) s.funcs)
    (hts : Interp.TagsOk tags s) (hrun : EvRun (profile o) host (invoke s a vs) [] c')
    (hd : Diverges (profile o) (fun _ _ _ _ => False) c') :
    ([], .div) ∈ wasmEvFunDXP s (a, vs) := by
  have hf := funDivXP_of_invoke_diverges hs hok hS hts (evRun_nil_diverges hrun hd)
  obtain ⟨fi, ps, rs, hfi, he, -⟩ := id hok
  have hty : Validation.DefType.funcType? fi.type = some (ps.toList, rs.toList) := by
    unfold Validation.DefType.funcType?; rw [Validation.Expand.iff.mp he]
  exact div_of_funDivXP (x := ⟨a, (vs, s)⟩) ⟨fi, _, _, hfi, hty⟩ hf

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
