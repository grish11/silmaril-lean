module

public import Silmaril.Wasm.Execution.Core.Inversion.Thms
public import Silmaril.Wasm.SingleThreaded.NoRedex

/-!
# Deterministic Core runs to values (proofs)

Inversion of concrete Core steps, for any profile and host, through the context lemmas of
`Silmaril.Wasm.Execution.Core.Inversion`:

* `Next P host c c'`: `c` steps, and only to `c'`;
* a `FRAME` or `LABEL` around code whose first non-value is a call, a `call_ref`, a `LABEL` or a
  `FRAME` (`Inert`) only steps inside, since no exit rule applies (`labelExit_inert`,
  `frameExit_inert`); around values it only leaves with them;
* `DetRun P host s c e`: a chain of `Next` steps from `c` to the values `e`, through
  configurations in the store `s` that are neither values nor a trap. Every configuration
  reachable from `c` is on it (`DetRun.of_steps`), and `c` does not diverge
  (`DetRun.not_diverges`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.PubViewExample

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {f F : Frame}
  {n : Nat} {k : List Instr} {is : List Admin} {out : List Admin}

/-! ## Heads that no exit rule removes -/

/-- A call, a `call_ref`, a `LABEL` or a `FRAME`. -/
def Inert : Admin → Prop
  | .plain (.call _) | .callRefType _ | .label .. | .frame .. => True
  | _ => False

theorem split_of {l : List Admin} (us : List Val) (d : Admin) (r : List Admin)
    (h : l = vals us ++ d :: r) (hd : d.val? = none) : splitVals l = (us, d :: r) := by
  subst h; exact splitVals_vals_cons hd r

theorem not_inert_returnCallRef {c : Admin} (hc : c.IsReturnCallRef) : ¬ Inert c := by
  unfold Admin.IsReturnCallRef at hc
  split at hc <;> simp_all [Inert]

/-- The code an exit rule removes is values, or has a head that is not `Inert`. -/
theorem labelExit_shape (h : LabelExit n k is out) :
    (∃ ws, is = vals ws ∧ out = vals ws) ∨
      ∃ us d r, splitVals is = (us, d :: r) ∧ ¬ Inert d := by
  cases h with
  | vals ws => exact .inl ⟨ws, rfl, rfl⟩
  | @brZero vs' vs l rest _ _ =>
    exact .inr ⟨vs' ++ vs, _, rest, split_of _ (.plain (.br l)) _ (by simp) rfl, id⟩
  | @brSucc vs l rest _ =>
    exact .inr ⟨vs, _, rest, split_of _ (.plain (.br l)) _ (by simp) rfl, id⟩
  | @ret vs rest => exact .inr ⟨vs, _, rest, split_of _ (.plain .return_) _ (by simp) rfl, id⟩
  | @returnCall vs c rest hc =>
    exact .inr ⟨vs, c, rest, split_of _ _ _ (by simp) (val?_returnCallRef hc),
      not_inert_returnCallRef hc⟩
  | throw a => exact .inr ⟨[.ref (.exn a)], _, [], split_of _ _ _ rfl rfl, id⟩
  | trap => exact .inr ⟨[], _, [], split_of _ _ _ rfl rfl, id⟩

theorem frameExit_shape (h : FrameExit s F n is out) :
    (∃ ws, is = vals ws ∧ out = vals ws) ∨
      ∃ us d r, splitVals is = (us, d :: r) ∧ ¬ Inert d := by
  cases h with
  | @vals ws _ => exact .inl ⟨ws, rfl, rfl⟩
  | @ret vs' vs rest _ =>
    exact .inr ⟨vs' ++ vs, _, rest, split_of _ (.plain .return_) _ (by simp) rfl, id⟩
  | trap => exact .inr ⟨[], _, [], split_of _ _ _ rfl rfl, id⟩
  | throw a => exact .inr ⟨[.ref (.exn a)], _, [], split_of _ _ _ rfl rfl, id⟩
  | @returnCallNull vs c rest hc =>
    exact .inr ⟨vs ++ [.ref .null], c, rest, split_of _ _ _ (by simp [vals, Val.toAdmin])
      (val?_returnCallRef hc), not_inert_returnCallRef hc⟩
  | @returnCallAddr vs' vs a c rest _ _ _ hc _ _ _ =>
    exact .inr ⟨vs' ++ vs ++ [.ref (.func a)], c, rest,
      split_of _ _ _ (by simp [vals, Val.toAdmin]) (val?_returnCallRef hc),
      not_inert_returnCallRef hc⟩

theorem vals_ne_split {ws us : List Val} {d : Admin} {r : List Admin}
    (h : splitVals (vals ws) = (us, d :: r)) : False := by
  rw [splitVals_vals] at h; cases h

theorem labelExit_inert {us : List Val} {d : Admin} {r : List Admin}
    (hs : splitVals is = (us, d :: r)) (hd : Inert d) (h : LabelExit n k is out) : False := by
  rcases labelExit_shape h with ⟨ws, rfl, -⟩ | ⟨us', d', r', hs', hd'⟩
  · exact vals_ne_split hs
  · rw [hs] at hs'; cases hs'; exact hd' hd

theorem frameExit_inert {us : List Val} {d : Admin} {r : List Admin}
    (hs : splitVals is = (us, d :: r)) (hd : Inert d) (h : FrameExit s F n is out) : False := by
  rcases frameExit_shape h with ⟨ws, rfl, -⟩ | ⟨us', d', r', hs', hd'⟩
  · exact vals_ne_split hs
  · rw [hs] at hs'; cases hs'; exact hd' hd

theorem frameExit_vals {ws : List Val} (h : FrameExit s F n (vals ws) out) : out = vals ws := by
  rcases frameExit_shape h with ⟨ws', hw, rfl⟩ | ⟨us, d, r, hs, -⟩
  · rw [vals_injective hw]
  · exact (vals_ne_split hs).elim

/-! ## Unique steps -/

/-- `c` steps, and only to `c'`. -/
def Next (P : Profile) (host : HostSemantics H) (c c' : Config H) : Prop :=
  Step P host c c' ∧ ∀ d, Step P host c d → d = c'

theorem Next.frame {s' : Store H} {F' : Frame} {is' : List Admin} {us : List Val} {d : Admin}
    {r : List Admin} (hs : splitVals is = (us, d :: r)) (hd : Inert d)
    (h : Next P host ⟨s, F, is⟩ ⟨s', F', is'⟩) :
    Next P host ⟨s, f, [.frame n F is]⟩ ⟨s', f, [.frame n F' is']⟩ := by
  refine ⟨.ctxtFrame h.1, fun c hc => ?_⟩
  rcases Step.frame_inv hc with ⟨s₁, F₁, is₁, h₁, rfl⟩ | ⟨out, hx, -⟩
  · cases h.2 _ h₁; rfl
  · exact (frameExit_inert hs hd hx).elim

theorem Next.label {s' : Store H} {f' : Frame} {is' : List Admin} {us : List Val} {d : Admin}
    {r : List Admin} (hs : splitVals is = (us, d :: r)) (hd : Inert d)
    (h : Next P host ⟨s, f, is⟩ ⟨s', f', is'⟩) :
    Next P host ⟨s, f, [.label n k is]⟩ ⟨s', f', [.label n k is']⟩ := by
  refine ⟨.ctxtLabel h.1, fun c hc => ?_⟩
  rcases Step.label_inv hc with ⟨s₁, f₁, is₁, h₁, rfl⟩ | ⟨out, hx, -⟩
  · cases h.2 _ h₁; rfl
  · exact (labelExit_inert hs hd hx).elim

theorem next_frameVals {ws : List Val} (hn : ws.length = n) :
    Next P host ⟨s, f, [.frame n F (vals ws)]⟩ ⟨s, f, vals ws⟩ := by
  refine ⟨.frameVals hn, fun c hc => ?_⟩
  rcases Step.frame_inv hc with ⟨s₁, F₁, is₁, h₁, -⟩ | ⟨out, hx, rfl⟩
  · exact (Step.not_vals h₁).elim
  · rw [frameExit_vals hx]

theorem next_labelVals {ws : List Val} :
    Next P host ⟨s, f, [.label n k (vals ws)]⟩ ⟨s, f, vals ws⟩ := by
  refine ⟨.labelVals, fun c hc => ?_⟩
  rcases Step.label_inv hc with ⟨s₁, f₁, is₁, h₁, -⟩ | ⟨out, hx, rfl⟩
  · exact (Step.not_vals h₁).elim
  · rw [labelExit_of_vals hx]

theorem next_call {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi) :
    Next P host ⟨s, f, [.plain (.call x)]⟩ ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ :=
  ⟨.call hx hf, fun _ hc => Step.call_inv_of hx hf hc⟩

/-- `call_ref` of a Wasm function without parameters enters its frame. -/
theorem next_callRef {a : Nat} {fi : FuncInst H} {code : Func} {ps rs : Validation.Ty (.list .val)}
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code)
    (he : Validation.Expand fi.type (.func ps rs)) (hps : ps.toList = []) :
    Next P host ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩
      ⟨s, f, [.frame rs.length (Frame.forCall fi.module [] code.locals)
        [.label rs.length [] (expression code.body)]]⟩ := by
  have hn : ([] : List Val).length = ps.length := by simp [Validation.Ty.length, hps]
  exact ⟨Step.callRefFunc (vs := []) (c := .callRefType fi.type) trivial hf he hn hcode,
    fun _ hc => Step.callRef_wasm_inv_exact (vs := []) (r := .callRefType fi.type) trivial hf hcode
      he hn hc⟩

/-! ## Deterministic runs to values -/

/-- A chain of `Next` steps from `c` to the values `e`, through configurations in the store `s`
that are neither values nor a trap. -/
inductive DetRun (P : Profile) (host : HostSemantics H) (s : Store H) :
    Config H → Config H → Prop where
  | done (f : Frame) (ws : List Val) : DetRun P host s ⟨s, f, vals ws⟩ ⟨s, f, vals ws⟩
  | step {c c' e : Config H} (hs : c.store = s) (hv : ∀ ws, c.code ≠ vals ws)
      (ht : c.code ≠ [.trap]) (h : Next P host c c') (hr : DetRun P host s c' e) :
      DetRun P host s c e

/-- The side conditions of `DetRun.step` from the first non-value of the code. -/
theorem mid_of_split {l : List Admin} {us : List Val} {d : Admin} {r : List Admin}
    (hs : splitVals l = (us, d :: r)) (hd : Inert d) : (∀ ws, l ≠ vals ws) ∧ l ≠ [.trap] := by
  refine ⟨fun ws h => ?_, fun h => ?_⟩
  · subst h; exact vals_ne_split hs
  · subst h; cases hs; exact hd

theorem DetRun.steps {c e : Config H} (h : DetRun P host s c e) : Steps P host c e := by
  induction h with
  | done => exact .refl
  | step _ _ _ hn _ ih => exact .head hn.1 ih

theorem DetRun.end {c e : Config H} (h : DetRun P host s c e) :
    ∃ f ws, e = ⟨s, f, vals ws⟩ := by
  induction h with
  | done f ws => exact ⟨f, ws, rfl⟩
  | step _ _ _ _ _ ih => exact ih

theorem DetRun.of_steps {c d e : Config H} (h : DetRun P host s c e) (hd : Steps P host c d) :
    DetRun P host s d e := by
  induction hd using Relation.ReflTransGen.head_induction_on generalizing e with
  | refl => exact h
  | head hst _ ih =>
    cases h with
    | done => exact (Step.not_vals hst).elim
    | step _ _ _ hn hr => cases hn.2 _ hst; exact ih hr

/-- A configuration on a `DetRun` is its end, or in the store `s` and neither values nor a
trap. -/
theorem DetRun.cases {c e : Config H} (h : DetRun P host s c e) :
    c = e ∨ (c.store = s ∧ (∀ ws, c.code ≠ vals ws) ∧ c.code ≠ [.trap]) := by
  cases h with
  | done => exact .inl rfl
  | step hs hv ht _ _ => exact .inr ⟨hs, hv, ht⟩

theorem DetRun.not_diverges {c e : Config H} (h : DetRun P host s c e) :
    ¬ Diverges P host c := by
  induction h with
  | done => rintro ⟨t, h0, ht⟩; exact Step.not_vals (h0 ▸ ht 0)
  | step _ _ _ hn _ ih =>
    rintro ⟨t, h0, ht⟩
    have h1 : t 1 = _ := hn.2 _ (h0 ▸ ht 0)
    exact ih ⟨fun i => t (i + 1), h1, fun i => ht (i + 1)⟩

end Silmaril.Proofs.Wasm.Abstract.PubViewExample
