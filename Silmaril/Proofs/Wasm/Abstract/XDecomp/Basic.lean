module

public import Silmaril.Wasm.Abstract.XDecomp.Defs
public import Silmaril.Proofs.Wasm.Abstract.XDiverge.Basic

/-!
Proofs for `Silmaril.Wasm.Abstract.XDecomp.Thms`, following
`Silmaril.Proofs.Wasm.Abstract.Decomp.Native` with every call form a descent:

* `reach_evalDivX`: reaching a diverging call diverges;
* `evalDivX_decomp`: a diverging problem diverges within its function, or
  reaches a diverging call (coinduction on "diverges and reaches no diverging
  call");
* `callDivX_path_or_chain`: iterating it, by choice;
* `callDivX_of_path`, `callDivX_of_chain`: the converses (the second by
  coinduction on "reaches a call of the chain").
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.XDecomp

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (wasmOShape funcs_of_func?)
open Silmaril.Wasm.Abstract.CallX Silmaril.Wasm.Abstract.XRecursion Silmaril.Wasm.Abstract.XDiverge
  Silmaril.Wasm.Abstract.XDecomp
open Silmaril.Proofs.Wasm.Abstract.XDiverge

variable {H : Type}

theorem reach_evalDivX {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {y : (wasmOShape H).self.Op} (h : ReachX s f stk es y) (hy : CallDivX y) : EvalDivX s f stk es := by
  induction h with
  | here hargs hfi hty =>
    obtain ⟨fi', fn, hfi', hcode, hd⟩ := hy
    obtain rfl : _ = fi' := Option.some.inj ((funcs_of_func? hfi).symm.trans hfi')
    exact evalDivX_unfold.mpr (.callee hargs hfi hcode hty hd)
  | args _ ih => exact evalDivX_unfold.mpr (.args (ih hy))
  | callK hargs hfi hcode hty hbody hvs _ ih =>
    exact evalDivX_unfold.mpr (.callRet hargs hfi hcode hty hbody hvs (ih hy))
  | opK hi hargs hflat _ ih => exact evalDivX_unfold.mpr (.opK hi hargs hflat (ih hy))
  | block har _ ih => exact evalDivX_unfold.mpr (.block har (ih hy))
  | blockK har hbody hvs _ ih => exact evalDivX_unfold.mpr (.blockK har hbody hvs (ih hy))
  | loop har _ ih => exact evalDivX_unfold.mpr (.loop har (ih hy))
  | loopK har hbody _ ih => exact evalDivX_unfold.mpr (.loopK har hbody (ih hy))
  | loopBack har hbody _ ih => exact evalDivX_unfold.mpr (.loopBack har hbody (ih hy))
  | cond _ ih => exact evalDivX_unfold.mpr (.cond (ih hy))
  | arm hc hb har _ ih => exact evalDivX_unfold.mpr (.arm hc hb har (ih hy))
  | ifK hc hb har harm hvs _ ih => exact evalDivX_unfold.mpr (.ifK hc hb har harm hvs (ih hy))
  | hereInd hargs hres hfi hty =>
    obtain ⟨fi', fn, hfi', hcode, hd⟩ := hy
    obtain rfl : _ = fi' := Option.some.inj (hfi.symm.trans hfi')
    exact evalDivX_unfold.mpr (.callIndCallee hargs hres hfi hcode hty hd)
  | callIndK hargs hres hfi hcode hty hbody hvs _ ih =>
    exact evalDivX_unfold.mpr (.callIndRet hargs hres hfi hcode hty hbody hvs (ih hy))
  | hereRef hargs hfi hty =>
    obtain ⟨fi', fn, hfi', hcode, hd⟩ := hy
    obtain rfl : _ = fi' := Option.some.inj (hfi.symm.trans hfi')
    exact evalDivX_unfold.mpr (.callRefCallee hargs hfi hcode hty hd)
  | callRefK hargs hfi hcode hty hbody hvs _ ih =>
    exact evalDivX_unfold.mpr (.callRefRet hargs hfi hcode hty hbody hvs (ih hy))
  | hereTail hargs hres hfi hty =>
    obtain ⟨fi', fn, hfi', hcode, hd⟩ := hy
    obtain rfl : _ = fi' := Option.some.inj (hfi.symm.trans hfi')
    exact evalDivX_unfold.mpr (.tailCallee hargs hres hfi hcode hty hd)

/-- **A diverging problem diverges within its function or reaches a diverging
call.** -/
theorem evalDivX_decomp {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    (h : EvalDivX s f stk es) :
    LocalDivX s f stk es ∨ ∃ y, ReachX s f stk es y ∧ CallDivX y := by
  by_cases hr : ∃ y, ReachX s f stk es y ∧ CallDivX y
  · exact .inr hr
  refine .inl (localDivX_coind (X := fun s f stk es =>
    EvalDivX s f stk es ∧ ¬ ∃ y, ReachX s f stk es y ∧ CallDivX y) ?_ _ _ _ _ ⟨h, hr⟩)
  rintro s f stk es ⟨hd, hn⟩
  have lift : ∀ {s' f' stk' es'}, (∀ y, ReachX s' f' stk' es' y → ReachX s f stk es y) →
      EvalDivX s' f' stk' es' → (EvalDivX s' f' stk' es' ∧ ¬ ∃ y, ReachX s' f' stk' es' y ∧ CallDivX y) :=
    fun hl hd' => ⟨hd', fun ⟨y, hy, hc⟩ => hn ⟨y, hl y hy, hc⟩⟩
  cases evalDivX_unfold.mp hd with
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
  | callIndCallee hargs hres hfi hcode hty h =>
    exact absurd ⟨_, .hereInd hargs hres hfi hty, _, _, hfi, hcode, h⟩ hn
  | callIndRet hargs hres hfi hcode hty hbody hvs h =>
    exact .callIndRet hargs hres hfi hcode hty hbody hvs
      (lift (fun _ => .callIndK hargs hres hfi hcode hty hbody hvs) h)
  | callRefCallee hargs hfi hcode hty h =>
    exact absurd ⟨_, .hereRef hargs hfi hty, _, _, hfi, hcode, h⟩ hn
  | callRefRet hargs hfi hcode hty hbody hvs h =>
    exact .callRefRet hargs hfi hcode hty hbody hvs
      (lift (fun _ => .callRefK hargs hfi hcode hty hbody hvs) h)
  | tailCallee hargs hres hfi hcode hty h =>
    exact absurd ⟨_, .hereTail hargs hres hfi hty, _, _, hfi, hcode, h⟩ hn

/-- **A diverging call diverges locally or reaches a diverging call.** -/
theorem callDivX_decomp {x : (wasmOShape H).self.Op} (h : CallDivX x) :
    wasmLocalDivX x ∨ ∃ y, BodyReachX x y ∧ CallDivX y := by
  obtain ⟨fi, fn, hfi, hcode, hd⟩ := h
  rcases evalDivX_decomp hd with hl | ⟨y, hy, hc⟩
  · exact .inl ⟨fi, fn, hfi, hcode, hl⟩
  · exact .inr ⟨y, ⟨fi, fn, hfi, hcode, hy⟩, hc⟩

/-- Local divergence of a call is divergence. -/
theorem callDivX_of_local {x : (wasmOShape H).self.Op} (h : wasmLocalDivX x) : CallDivX x := by
  obtain ⟨fi, fn, hfi, hcode, hl⟩ := h
  exact ⟨fi, fn, hfi, hcode, localDivX_le_evalDivX _ _ _ _ hl⟩

/-- Descending into a diverging call diverges. -/
theorem callDivX_of_bodyReach {x y : (wasmOShape H).self.Op} (h : BodyReachX x y) (hy : CallDivX y) :
    CallDivX x := by
  obtain ⟨fi, fn, hfi, hcode, hr⟩ := h
  exact ⟨fi, fn, hfi, hcode, reach_evalDivX hr hy⟩

theorem callDivX_of_path {x z : (wasmOShape H).self.Op} (h : BodyPathX x z) (hz : wasmLocalDivX z) :
    CallDivX x := by
  induction h with
  | refl => exact callDivX_of_local hz
  | step hxy _ ih => exact callDivX_of_bodyReach hxy (ih hz)

/-- **A diverging call reaches a locally diverging call by finitely many
descents, or starts an infinite chain of descents into diverging calls.** -/
theorem callDivX_path_or_chain {x : (wasmOShape H).self.Op} (h : CallDivX x) :
    (∃ z, BodyPathX x z ∧ wasmLocalDivX z) ∨
      ∃ g : Nat → (wasmOShape H).self.Op, g 0 = x ∧ ∀ n, BodyReachX (g n) (g (n + 1)) := by
  by_cases hp : ∃ z, BodyPathX x z ∧ wasmLocalDivX z
  · exact .inl hp
  refine .inr ?_
  -- calls that diverge and reach no local divergence
  let S := {y : (wasmOShape H).self.Op // CallDivX y ∧ ¬ ∃ z, BodyPathX y z ∧ wasmLocalDivX z}
  have next : ∀ y : S, ∃ y' : S, BodyReachX y.1 y'.1 := by
    rintro ⟨y, hy, hny⟩
    rcases callDivX_decomp hy with hl | ⟨y', hr, hy'⟩
    · exact absurd ⟨y, .refl y, hl⟩ hny
    · exact ⟨⟨y', hy', fun ⟨z, hz, hl⟩ => hny ⟨z, .step hr hz, hl⟩⟩, hr⟩
  choose nx hnx using next
  let G : Nat → S := fun n => Nat.rec ⟨x, h, hp⟩ (fun _ y => nx y) n
  exact ⟨fun n => (G n).1, rfl, fun n => hnx (G n)⟩


/-- **An infinite chain of descents makes the first call diverge.** -/
theorem callDivX_of_chain {g : Nat → (wasmOShape H).self.Op} (hg : ∀ n, BodyReachX (g n) (g (n + 1))) :
    CallDivX (g 0) := by
  let X : Interp.Problem H := fun s f stk es => ∃ n, ReachX s f stk es (g n)
  have hX : X ≤ EvalDivX := by
    refine evalDivX_coind ?_
    rintro s f stk es ⟨n, hr⟩
    generalize hy : g n = y at hr
    have next : ∀ {fa : Nat} {args : List Val} {s₁ : Store H} {fi : FuncInst H},
        g n = ⟨fa, (args, s₁)⟩ → s₁.funcs[fa]? = some fi →
        ∃ fn, fi.code = .wasm fn ∧
          X s₁ (Frame.forCall fi.module args fn.locals) [] (liftInstrs fn.body) := by
      intro fa args s₁ fi he hfi
      obtain ⟨fi', fn, hfi', hcode, hreach⟩ := hg n
      rw [he] at hfi' hreach
      simp only at hfi'
      rw [hfi] at hfi'
      obtain rfl := Option.some.inj hfi'
      exact ⟨fn, hcode, n + 1, hreach⟩
    cases hr with
    | here hargs hfi hty =>
      obtain ⟨fn, hcode, hx⟩ := next hy (funcs_of_func? hfi)
      exact .callee hargs hfi hcode hty hx
    | args h' => exact .args ⟨n, hy ▸ h'⟩
    | callK hargs hfi hcode hty hbody hvs h' =>
      exact .callRet hargs hfi hcode hty hbody hvs ⟨n, hy ▸ h'⟩
    | opK hi hargs hflat h' => exact .opK hi hargs hflat ⟨n, hy ▸ h'⟩
    | block har h' => exact .block har ⟨n, hy ▸ h'⟩
    | blockK har hbody hvs h' => exact .blockK har hbody hvs ⟨n, hy ▸ h'⟩
    | loop har h' => exact .loop har ⟨n, hy ▸ h'⟩
    | loopK har hbody h' => exact .loopK har hbody ⟨n, hy ▸ h'⟩
    | loopBack har hbody h' => exact .loopBack har hbody ⟨n, hy ▸ h'⟩
    | cond h' => exact .cond ⟨n, hy ▸ h'⟩
    | arm hc hb har h' => exact .arm hc hb har ⟨n, hy ▸ h'⟩
    | ifK hc hb har harm hvs h' => exact .ifK hc hb har harm hvs ⟨n, hy ▸ h'⟩
    | hereInd hargs hres hfi hty =>
      obtain ⟨fn, hcode, hx⟩ := next hy hfi
      exact .callIndCallee hargs hres hfi hcode hty hx
    | callIndK hargs hres hfi hcode hty hbody hvs h' =>
      exact .callIndRet hargs hres hfi hcode hty hbody hvs ⟨n, hy ▸ h'⟩
    | hereRef hargs hfi hty =>
      obtain ⟨fn, hcode, hx⟩ := next hy hfi
      exact .callRefCallee hargs hfi hcode hty hx
    | callRefK hargs hfi hcode hty hbody hvs h' =>
      exact .callRefRet hargs hfi hcode hty hbody hvs ⟨n, hy ▸ h'⟩
    | hereTail hargs hres hfi hty =>
      obtain ⟨fn, hcode, hx⟩ := next hy hfi
      exact .tailCallee hargs hres hfi hcode hty hx
  obtain ⟨fi, fn, hfi, hcode, hreach⟩ := hg 0
  exact ⟨fi, fn, hfi, hcode, hX _ _ _ _ ⟨1, hreach⟩⟩

end Silmaril.Proofs.Wasm.Abstract.XDecomp
