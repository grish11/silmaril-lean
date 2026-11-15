module

public import Silmaril.Proofs.Wasm.Abstract.HostEval.CallWasm
public import Silmaril.Wasm.Abstract.HostCall.Thms

/-!
# The whole-run backward simulation with host calls (proofs)

`back_whole`: in the deterministic profile `SingleThreaded.profile o`, for a host
with typed answers (`HostTyped`) in the native host slice
(`Interp.NativeHostSlice`), every Core run of lowered, arity-checked, typed trees
to a stuck end is the end of an `EvalH` run (`EndsAs`) or is blocked at a host call
with no outcome (`Pending`).

The proof is a well-founded induction on the run length, then the tree size
(`BackGoal`). The constructor cases (`back_nil`, `back_op_flat`, `back_op_call`
with `back_call_host`/`back_call_wasm`, `back_block_tree`, `back_loop_tree`,
`back_if_tree`) are applied with their hypotheses discharged:

* the induction hypotheses, at a run no longer than the whole on a smaller tree,
  or strictly shorter (callee bodies, loop re-entry);
* the forward simulation (`Interp.evalH_good`): every `EvalH` result satisfies the
  arity check's `FlowOk` and keeps the store check (`EvalInv`), and is a Core run,
  which carries typing to the intermediate configurations
  (`HostCall.ContextTyped.steps_typed`);
* typed native progress (`Interp.evalFlat_progressH`, `Interp.truthy_progressH`);
* the host slice (result arity, no exceptions).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostEval

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core (Outcome)
open Silmaril.Wasm.SingleThreaded

variable {H : Type} {host : HostSemantics H}

/-- The statement of the backward simulation for `n` steps of the trees `es`. -/
def BackGoal (o : GrowOracle) (host : HostSemantics H) (n : Nat) (es : List Binaryen.BExpr) : Prop :=
  ∀ (s : Store H) (f : Frame) (stk : List Val) (labels : List Nat) (ret : Nat) (out : Option Nat)
    (c : Config H), Interp.StoreChk s.funcs →
    Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) es = some out →
    Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ →
    StepsN (profile o) host n ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ c →
    (∀ c', ¬ Step (profile o) host c c') → BackOut host s f stk es c

variable {o : GrowOracle}

/-- A normal native run of checked trees is a Core run to its values. -/
theorem run_of_evalH (hH : Interp.NativeHostSlice host) {s s₁ : Store H} {f f₁ : Frame}
    {stk stk₁ : List Val} {xs : List Binaryen.BExpr} {labels : List Nat} {ret : Nat}
    {out : Option Nat} (hev : EvalH host s f stk xs (s₁, f₁, .normal stk₁))
    (hS : Interp.StoreChk s.funcs)
    (hc : Interp.chk s.funcs f.module f.locals.length ret labels (some stk.length) xs = some out) :
    Steps (profile o) host ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList xs)⟩
      ⟨s₁, f₁, vals stk₁.reverse⟩ := by
  obtain ⟨c', o', hrun, he, hm⟩ :=
    Interp.run_of_wp ((Interp.evalH_good (P := profile o) hH hev).2 hS hc)
  rw [← Interp.ends_normal hm he]
  exact hrun

/-- **The operator case** other than a call. -/
theorem case_op_flat (hT : HostTyped host) (hH : Interp.NativeHostSlice host) {n : Nat}
    {i : Instr} {args es : List Binaryen.BExpr} (hi : ∀ x, i ≠ .call x)
    (ihle : ∀ m ≤ n, ∀ es', sizeOf es' < sizeOf (Binaryen.BExpr.op i args :: es) →
      BackGoal o host m es') :
    BackGoal o host n (.op i args :: es) := by
  intro s f stk labels ret out c hS hc ht hrun hend
  obtain ⟨o₁, h1, h2⟩ := Interp.chk_consE.mp hc
  obtain ⟨oa, ha, -⟩ := Interp.chk1_opE h1
  have hcode := Interp.code_op stk i args es
  have hta : Sim.ContextTyped ⟨s, f, vals stk.reverse ++ expression (Binaryen.BExpr.lowerList args)⟩ :=
    Sim.ContextTyped.suffix (hcode ▸ ht)
  -- typing after the arguments
  have htyped : ∀ s₁ f₁ stk₁, EvalH host s f stk args (s₁, f₁, .normal stk₁) →
      Sim.ContextTyped ⟨s₁, f₁, vals stk₁.reverse ++ .plain i ::
        expression (Binaryen.BExpr.lowerList es)⟩ := by
    intro s₁ f₁ stk₁ hev
    have hr := Silmaril.Wasm.Logic.Core.Steps.append (.plain i :: expression (Binaryen.BExpr.lowerList es))
      (run_of_evalH (o := o) hH hev hS ha)
    exact ContextTyped.steps_typed hT (hcode ▸ ht) hr
  refine back_op_flat hi hrun hend ?_ ?_ ?_
  · intro m hm c₁ h₁ hs₁
    exact ihle m hm args Interp.size_args s f stk labels ret oa c₁ hS ha hta h₁ hs₁
  · intro s₁ f₁ stk₁ hev
    obtain ⟨hf, -⟩ := Interp.arity_args hS (Interp.evalH_good (P := profile o) hH hev).1 h1
    exact ⟨Interp.evalFlat_progressH hf hi (htyped s₁ f₁ stk₁ hev),
      _, _, _, _, _, _, hf⟩
  · intro s₁ f₁ stk₁ s₂ f₂ stk₂ m hm hev hfl hrun₂
    obtain ⟨hf, inv1⟩ := Interp.arity_args hS (Interp.evalH_good (P := profile o) hH hev).1 h1
    obtain ⟨ho, inv2⟩ := Interp.flat_normal (ext := Interp.noExt) hfl hf
    have inv12 : Interp.EvalInv s f (s₂, f₂, .normal stk₂) := inv1.trans inv2
    have h2' : Interp.chk s₂.funcs f₂.module f₂.locals.length ret labels (some stk₂.length) es =
        some out := by
      rw [← ho]; exact Interp.chk_inv inv12 h2
    have hst := Interp.steps_flat_normal (P := profile o) (host := host) hi hf hfl
      (expression (Binaryen.BExpr.lowerList es))
    have ht₂ : Sim.ContextTyped ⟨s₂, f₂, vals stk₂.reverse ++ expression (Binaryen.BExpr.lowerList es)⟩ :=
      ContextTyped.steps_typed hT (htyped s₁ f₁ stk₁ hev) hst
    exact ihle m hm es Interp.size_tail s₂ f₂ stk₂ labels ret out c (Interp.storeChk_inv inv12 hS) h2'
      ht₂ hrun₂ hend

end Silmaril.Proofs.Wasm.Abstract.HostEval
