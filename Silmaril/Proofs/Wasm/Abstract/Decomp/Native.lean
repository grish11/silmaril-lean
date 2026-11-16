module

public import Silmaril.Wasm.Abstract.Decomp.Defs
public import Silmaril.Wasm.Interp.Diverge.Thms
public import Silmaril.Wasm.Abstract.Recursion.Thms

/-!
# Decomposing native divergence (proofs)

* `reach_evalDiv`: reaching a diverging call diverges.
* `evalDiv_decomp`: a diverging problem either diverges within its function,
  or reaches a diverging call. The proof is coinduction on "diverges and
  reaches no diverging call".
* `funDiv_decomp`: the same for calls.
* `funDiv_path_or_chain`: iterating it, by choice. A diverging call either
  reaches a locally diverging call by finitely many descents, or starts an
  infinite chain of descents.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.Decomp

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Interp (EvalDiv LocalDiv FunDiv DivStep Problem)

variable {H : Type}

/-- The call `y` diverges. -/
def CallDiv (y : (wasmOShape H).self.Op) : Prop := FunDiv y.2.2 y.1 y.2.1

theorem reach_evalDiv {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : Reach s f stk es y) (hy : CallDiv y) : EvalDiv s f stk es := by
  induction h with
  | here hargs hfi hty =>
    obtain ⟨fi', fn, hfi', hcode, hd⟩ := hy
    obtain rfl : _ = fi' := Option.some.inj ((funcs_of_func? hfi).symm.trans hfi')
    exact Interp.evalDiv_iff_step.mpr (.callee hargs hfi hcode hty hd)
  | args _ ih => exact Interp.evalDiv_iff_step.mpr (.args (ih hy))
  | callK hargs hfi hcode hty hbody hvs _ ih =>
    exact Interp.evalDiv_iff_step.mpr (.callRet hargs hfi hcode hty hbody hvs (ih hy))
  | opK hi hargs hflat _ ih => exact Interp.evalDiv_iff_step.mpr (.opK hi hargs hflat (ih hy))
  | block har _ ih => exact Interp.evalDiv_iff_step.mpr (.block har (ih hy))
  | blockK har hbody hvs _ ih => exact Interp.evalDiv_iff_step.mpr (.blockK har hbody hvs (ih hy))
  | loop har _ ih => exact Interp.evalDiv_iff_step.mpr (.loop har (ih hy))
  | loopK har hbody _ ih => exact Interp.evalDiv_iff_step.mpr (.loopK har hbody (ih hy))
  | loopBack har hbody _ ih => exact Interp.evalDiv_iff_step.mpr (.loopBack har hbody (ih hy))
  | cond _ ih => exact Interp.evalDiv_iff_step.mpr (.cond (ih hy))
  | arm hc hb har _ ih => exact Interp.evalDiv_iff_step.mpr (.arm hc hb har (ih hy))
  | ifK hc hb har harm hvs _ ih => exact Interp.evalDiv_iff_step.mpr (.ifK hc hb har harm hvs (ih hy))

/-- **A diverging problem diverges within its function or reaches a diverging
call.** -/
theorem evalDiv_decomp {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (h : EvalDiv s f stk es) :
    LocalDiv s f stk es ∨ ∃ y, Reach s f stk es y ∧ CallDiv y := by
  by_cases hr : ∃ y, Reach s f stk es y ∧ CallDiv y
  · exact .inr hr
  refine .inl (Interp.localDiv_of_coind (X := fun s f stk es =>
    EvalDiv s f stk es ∧ ¬ ∃ y, Reach s f stk es y ∧ CallDiv y) ?_ _ _ _ _ ⟨h, hr⟩)
  rintro s f stk es ⟨hd, hn⟩
  have lift : ∀ {s' f' stk' es'}, (∀ y, Reach s' f' stk' es' y → Reach s f stk es y) →
      EvalDiv s' f' stk' es' → (EvalDiv s' f' stk' es' ∧ ¬ ∃ y, Reach s' f' stk' es' y ∧ CallDiv y) :=
    fun hl hd' => ⟨hd', fun ⟨y, hy, hc⟩ => hn ⟨y, hl y hy, hc⟩⟩
  cases Interp.evalDiv_iff_step.mp hd with
  | args h => exact .args (lift (fun _ => .args) h)
  | callee hargs hfi hcode hty h =>
    exact absurd ⟨_, .here hargs hfi hty, _, _, funcs_of_func? hfi, hcode, h⟩ hn
  | callRet hargs hfi hcode hty hbody hvs h =>
    exact .callRet hargs hfi hcode hty hbody hvs (lift (fun _ => .callK hargs hfi hcode hty hbody hvs) h)
  | opK hi hargs hflat h => exact .opK hi hargs hflat (lift (fun _ => .opK hi hargs hflat) h)
  | block har h => exact .block har (lift (fun _ => .block har) h)
  | blockK har hbody hvs h => exact .blockK har hbody hvs (lift (fun _ => .blockK har hbody hvs) h)
  | loop har h => exact .loop har (lift (fun _ => .loop har) h)
  | loopK har hbody h => exact .loopK har hbody (lift (fun _ => .loopK har hbody) h)
  | loopBack har hbody h => exact .loopBack har hbody (lift (fun _ => .loopBack har hbody) h)
  | cond h => exact .cond (lift (fun _ => .cond) h)
  | arm hc hb har h => exact .arm hc hb har (lift (fun _ => .arm hc hb har) h)
  | ifK hc hb har harm hvs h => exact .ifK hc hb har harm hvs (lift (fun _ => .ifK hc hb har harm hvs) h)

/-- A call reached from code has a typed callee. -/
theorem reach_typed {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : Reach s f stk es y) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), y.2.2.funcs[y.1]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) := by
  induction h with
  | here _ hfi hty => exact ⟨_, _, _, funcs_of_func? hfi, hty⟩
  | args _ ih | callK _ _ _ _ _ _ _ ih | opK _ _ _ _ ih | block _ _ ih | blockK _ _ _ _ ih
  | loop _ _ ih | loopK _ _ _ ih | loopBack _ _ _ ih | cond _ ih | arm _ _ _ _ ih
  | ifK _ _ _ _ _ _ ih => exact ih

/-- **A diverging call diverges locally or reaches a diverging call.** -/
theorem callDiv_decomp {x : (wasmOShape H).self.Op} (h : CallDiv x) :
    wasmLocalDiv x ∨ ∃ y, BodyReach x y ∧ CallDiv y := by
  obtain ⟨fi, fn, hfi, hcode, hd⟩ := h
  rcases evalDiv_decomp hd with hl | ⟨y, hy, hc⟩
  · exact .inl ⟨fi, fn, hfi, hcode, hl⟩
  · exact .inr ⟨y, ⟨fi, fn, hfi, hcode, hy⟩, hc⟩

/-- Local divergence of a call is divergence. -/
theorem callDiv_of_local {x : (wasmOShape H).self.Op} (h : wasmLocalDiv x) : CallDiv x := by
  obtain ⟨fi, fn, hfi, hcode, hl⟩ := h
  exact ⟨fi, fn, hfi, hcode, Interp.localDiv_evalDiv _ _ _ _ hl⟩

/-- Descending into a diverging call diverges. -/
theorem callDiv_of_bodyReach {x y : (wasmOShape H).self.Op} (h : BodyReach x y) (hy : CallDiv y) :
    CallDiv x := by
  obtain ⟨fi, fn, hfi, hcode, hr⟩ := h
  exact ⟨fi, fn, hfi, hcode, reach_evalDiv hr hy⟩

theorem callDiv_of_path {x z : (wasmOShape H).self.Op} (h : BodyPath x z) (hz : wasmLocalDiv z) :
    CallDiv x := by
  induction h with
  | refl => exact callDiv_of_local hz
  | step hxy _ ih => exact callDiv_of_bodyReach hxy (ih hz)

/-- **A diverging call reaches a locally diverging call by finitely many
descents, or starts an infinite chain of descents into diverging calls.** -/
theorem callDiv_path_or_chain {x : (wasmOShape H).self.Op} (h : CallDiv x) :
    (∃ z, BodyPath x z ∧ wasmLocalDiv z) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = x ∧ ∀ n, BodyReach (g n) (g (n + 1)) := by
  by_cases hp : ∃ z, BodyPath x z ∧ wasmLocalDiv z
  · exact .inl hp
  refine .inr ?_
  -- calls that diverge and reach no local divergence
  let S := {y : (wasmOShape H).self.Op // CallDiv y ∧ ¬ ∃ z, BodyPath y z ∧ wasmLocalDiv z}
  have next : ∀ y : S, ∃ y' : S, BodyReach y.1 y'.1 := by
    rintro ⟨y, hy, hny⟩
    rcases callDiv_decomp hy with hl | ⟨y', hr, hy'⟩
    · exact absurd ⟨y, .refl y, hl⟩ hny
    · exact ⟨⟨y', hy', fun ⟨z, hz, hl⟩ => hny ⟨z, .step hr hz, hl⟩⟩, hr⟩
  choose nx hnx using next
  let G : Nat → S := fun n => Nat.rec ⟨x, h, hp⟩ (fun _ y => nx y) n
  exact ⟨fun n => (G n).1, rfl, fun n => hnx (G n)⟩

end Silmaril.Proofs.Wasm.Abstract.Decomp
