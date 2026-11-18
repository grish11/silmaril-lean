module

public import Silmaril.Wasm.Abstract.HostClosingS.Defs
public import Silmaril.Wasm.Abstract.HostClosingXP.Thms
public import Silmaril.Wasm.Abstract.Recursion.Thms

/-!
# Session runs and canonical runs (proofs)

The logged relations `EvalLXPS` (trap answers) and `EvalLXPh` (cut calls) have the same runs up to
the answers of the calls:

* `oToS`, `hToS`: a call of `wasmHShape H` as a call of `wasmHShapeS H`, its answer as `inl`;
* `evalLXPS_toH`: a session run is a canonical run of the same result, with the same calls and
  answers, except that a trap answer, which is the last call and ends the run in a trap, becomes
  a cut call, with any answer longer than the callee's result arity;
* `evalLXPh_toS`: a canonical run is a session run of the same result and calls, unless it ends
  in a cut call (an answer of more values than the callee's result arity), then in a trap; then
  the call answered by a trap is a session run of the same result;
* `reachLXP_trapS`: a reached call answered by a trap, leaving any store, ends a session run.

In the trap cases the correspondence is exact: a trap answer becomes a cut call with **every**
answer longer than the callee's result arity (`ToH`), and a cut call becomes the trap answer
leaving its store (`ToS`); `evalLXPS_canonical_cut`, `evalLXPh_session_cut` state both through
`OCall.toS`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingS

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.CallXP (POut)

variable {H : Type}

/-- A call of the canonical open semantics as a session call, its answer as `inl`. -/
def oToS : OCall H → SCall H
  | ⟨.inr y, (b, s')⟩ => ⟨.inr y, (.inl b, s')⟩

/-- A call of `wasmHShape H` as a call of `wasmHShapeS H`, its answer as `inl`. -/
def hToS : HCall H → SCall H
  | ⟨.inl m, n⟩ => ⟨.inl m, n⟩
  | ⟨.inr y, (b, s')⟩ => ⟨.inr y, (.inl b, s')⟩

@[simp] theorem oToS_mk {a : Nat} {args : List Val} {s s' : Store H} {b : List Val ⊕ Nat} :
    oToS (OCall.mk a args s b s') = SCall.mk a args s (.inl b) s' := rfl

@[simp] theorem hToS_lift (z : OCall H) : hToS (OCall.lift z) = oToS z := by
  rcases z with ⟨⟨⟨⟩⟩ | y, b, s'⟩
  rfl

theorem ne_trap_of_blockVals {fl : Flow} {vs : List Val} (hvs : fl.blockVals = some vs) :
    POut.flow fl ≠ .flow .trap := by
  rintro ⟨⟩
  simp [Flow.blockVals] at hvs

/-! ## Session runs as canonical runs -/

/-- A session log `l` of a run ending in `r`, read back: the image of a canonical log, or a
canonical log `u` then a trap answer of a call to `g` leaving `s₂`, the run ending in a trap in
`s₂`. In the second case the callee has a type, and the canonical log `u` then the call answered
by **any** list of more values than the callee's result arity (a cut call) satisfies `P`. -/
def ToH (l : List (SCall H)) (r : Store H × Frame × POut) (P : List (OCall H) → Prop) : Prop :=
  (∃ l', l = l'.map oToS ∧ P l') ∨
  (r.2.2 = .flow .trap ∧ ∃ (u : List (OCall H)) (g : Nat) (args : List Val) (s₁ s₂ : Store H),
    r.1 = s₂ ∧ l = u.map oToS ++ [SCall.mk g args s₁ (.inr ()) s₂] ∧
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s₁.funcs[g]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧
      ∀ ws : List Val, rs.length < ws.length → P (u ++ [OCall.mk g args s₁ (.inl ws) s₂]))

theorem ToH.mono {l : List (SCall H)} {r r' : Store H × Frame × POut}
    {P Q : List (OCall H) → Prop} (h : ToH l r P) (hP : ∀ l', P l' → Q l')
    (ho : r.2.2 = .flow .trap → r'.2.2 = .flow .trap ∧ r'.1 = r.1) : ToH l r' Q := by
  rcases h with ⟨l', rfl, hp⟩ | ⟨ht, u, g, args, s₁, s₂, hs, rfl, fi, ps, rs, hf, hty, hp⟩
  · exact .inl ⟨l', rfl, hP _ hp⟩
  · exact .inr ⟨(ho ht).1, u, g, args, s₁, s₂, (ho ht).2.trans hs, rfl, fi, ps, rs, hf, hty,
      fun ws hws => hP _ (hp ws hws)⟩

theorem ToH.app {l : List (SCall H)} {r : Store H × Frame × POut} {P Q : List (OCall H) → Prop}
    (pre : List (OCall H)) (h : ToH l r P) (hP : ∀ l', P l' → Q (pre ++ l')) :
    ToH (pre.map oToS ++ l) r Q := by
  rcases h with ⟨l', rfl, hp⟩ | ⟨ht, u, g, args, s₁, s₂, hs, rfl, fi, ps, rs, hf, hty, hp⟩
  · exact .inl ⟨pre ++ l', by simp, hP _ hp⟩
  · exact .inr ⟨ht, pre ++ u, g, args, s₁, s₂, hs, by simp, fi, ps, rs, hf, hty,
      fun ws hws => by simpa using hP _ (hp ws hws)⟩

theorem ToH.ok {l : List (SCall H)} {r : Store H × Frame × POut} {P : List (OCall H) → Prop}
    (h : ToH l r P) (ho : r.2.2 ≠ .flow .trap) : ∃ l', l = l'.map oToS ∧ P l' := by
  rcases h with h | ⟨ht, -⟩
  · exact h
  · exact absurd ht ho

/-- **A session run is a canonical run**, a trap answer becoming a cut call. -/
theorem evalLXPS_toH {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f stk es l r) :
    ToH l r (fun l' => EvalLXPh s f stk es l' r) := by
  induction h with
  | nil => exact .inl ⟨[], rfl, .nil⟩
  | argsAbort _ ho ih => exact ih.mono (fun _ h => .argsAbort h ho) fun h => ⟨h, rfl⟩
  | @callRet s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ l₂ r _ hfi hty _ ih₁ ih₂ =>
    obtain ⟨l₁', rfl, h₁⟩ := ih₁.ok (by simp)
    have := ih₂.app (l₁' ++ [OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂])
      (Q := fun l' => EvalLXPh s f stk (.op (.call x) args :: es) l' r)
      (fun l₂' h₂ => by simpa using EvalLXPh.callRet h₁ hfi hty h₂)
    simpa using this
  | callThrow _ hfi hty ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨_, by simp, .callThrow h₁ hfi hty⟩
  | @callTrap s s₁ s₂ f f₁ stk stk₁ x args es a fi ps rs l₁ _ hfi hty ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inr ⟨rfl, l₁', _, _, s₁, s₂, rfl, rfl, fi, ps, rs, funcs_of_func? hfi, hty,
      fun _ hws => .callCut h₁ hfi hty hws⟩
  | opOk hi _ hflat _ ih₁ ih₂ =>
    obtain ⟨l₁', rfl, h₁⟩ := ih₁.ok (by simp)
    exact ih₂.app l₁' (fun _ h₂ => .opOk hi h₁ hflat h₂)
  | opStop hi _ hflat hfl ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨l₁', rfl, .opStop hi h₁ hflat hfl⟩
  | blockOk har _ hvs _ ih₁ ih₂ =>
    obtain ⟨l₁', rfl, h₁⟩ := ih₁.ok (ne_trap_of_blockVals hvs)
    exact ih₂.app l₁' (fun _ h₂ => .blockOk har h₁ hvs h₂)
  | blockBrk har _ ih => exact ih.mono (fun _ h => .blockBrk har h) (fun h => absurd h (by simp))
  | blockEsc har _ ho ih => exact ih.mono (fun _ h => .blockEsc har h ho) fun h => ⟨h, rfl⟩
  | loopOk har _ _ ih₁ ih₂ =>
    obtain ⟨l₁', rfl, h₁⟩ := ih₁.ok (by simp)
    exact ih₂.app l₁' (fun _ h₂ => .loopOk har h₁ h₂)
  | loopBack har _ _ ih₁ ih₂ =>
    obtain ⟨l₁', rfl, h₁⟩ := ih₁.ok (by simp)
    exact ih₂.app l₁' (fun _ h₂ => .loopBack har h₁ h₂)
  | loopBrk har _ ih => exact ih.mono (fun _ h => .loopBrk har h) (fun h => absurd h (by simp))
  | loopEsc har _ ho ih => exact ih.mono (fun _ h => .loopEsc har h ho) fun h => ⟨h, rfl⟩
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    obtain ⟨l₁', rfl, h₁⟩ := ih₁.ok (by simp)
    obtain ⟨l₂', rfl, h₂⟩ := ih₂.ok (ne_trap_of_blockVals hvs)
    rw [show l₁'.map oToS ++ l₂'.map oToS = (l₁' ++ l₂').map oToS by simp]
    exact ih₃.app _ (fun _ h₃ => by simpa using EvalLXPh.ifOk h₁ hb har h₂ hvs h₃)
  | ifBrk _ hb har _ ih₁ ih₂ =>
    obtain ⟨l₁', rfl, h₁⟩ := ih₁.ok (by simp)
    obtain ⟨l₂', rfl, h₂⟩ := ih₂.ok (by simp)
    exact .inl ⟨l₁' ++ l₂', by simp, .ifBrk h₁ hb har h₂⟩
  | ifEsc _ hb har _ ho ih₁ ih₂ =>
    obtain ⟨l₁', rfl, h₁⟩ := ih₁.ok (by simp)
    exact ih₂.app l₁' (fun _ h₂ => .ifEsc h₁ hb har h₂ ho)
  | ifAbort _ ho ih => exact ih.mono (fun _ h => .ifAbort h ho) fun h => ⟨h, rfl⟩
  | @indRet s s₁ s₂ f f₁ stk stk₁ ws x y args es ad i fa fi ps rs l₁ l₂ r _ hres hfi hty hy _
      ih₁ ih₂ =>
    obtain ⟨l₁', rfl, h₁⟩ := ih₁.ok (by simp)
    have := ih₂.app (l₁' ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂])
      (Q := fun l' => EvalLXPh s f stk (.op (.callIndirect x y) args :: es) l' r)
      (fun l₂' h₂ => by simpa using EvalLXPh.indRet h₁ hres hfi hty hy h₂)
    simpa using this
  | indThrow _ hres hfi hty hy ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨_, by simp, .indThrow h₁ hres hfi hty hy⟩
  | @indTrap s s₁ s₂ f f₁ stk stk₁ x y args es ad i fa fi ps rs l₁ _ hres hfi hty hy ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inr ⟨rfl, l₁', _, _, s₁, s₂, rfl, rfl, fi, ps, rs, hfi, hty,
      fun _ hws => .indCut h₁ hres hfi hty hy hws⟩
  | indRes _ hres ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨l₁', rfl, .indRes h₁ hres⟩
  | @refRet s s₁ s₂ f f₁ stk stk₁ ws y args es fa fi ps rs l₁ l₂ r _ hfi hty hy _ ih₁ ih₂ =>
    obtain ⟨l₁', rfl, h₁⟩ := ih₁.ok (by simp)
    have := ih₂.app (l₁' ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂])
      (Q := fun l' => EvalLXPh s f stk (.op (.callRef y) args :: es) l' r)
      (fun l₂' h₂ => by simpa using EvalLXPh.refRet h₁ hfi hty hy h₂)
    simpa using this
  | refThrow _ hfi hty hy ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨_, by simp, .refThrow h₁ hfi hty hy⟩
  | @refTrap s s₁ s₂ f f₁ stk stk₁ y args es fa fi ps rs l₁ _ hfi hty hy ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inr ⟨rfl, l₁', _, _, s₁, s₂, rfl, rfl, fi, ps, rs, hfi, hty,
      fun _ hws => .refCut h₁ hfi hty hy hws⟩
  | refNull _ ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨l₁', rfl, .refNull h₁⟩
  | tail _ hres hfi hty hy ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨l₁', rfl, .tail h₁ hres hfi hty hy⟩
  | tailRes _ hres ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨l₁', rfl, .tailRes h₁ hres⟩
  | throw _ ht he hn ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨l₁', rfl, .throw h₁ ht he hn⟩
  | throwRefNull _ ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨l₁', rfl, .throwRefNull h₁⟩
  | throwRefExn _ ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨l₁', rfl, .throwRefExn h₁⟩
  | tryOk har _ hvs _ ih₁ ih₂ =>
    obtain ⟨l₁', rfl, h₁⟩ := ih₁.ok (ne_trap_of_blockVals hvs)
    exact ih₂.app l₁' (fun _ h₂ => .tryOk har h₁ hvs h₂)
  | tryBrk har _ ih => exact ih.mono (fun _ h => .tryBrk har h) (fun h => absurd h (by simp))
  | tryEsc har _ ho hnt ih => exact ih.mono (fun _ h => .tryEsc har h ho hnt) fun h => ⟨h, rfl⟩
  | tryCatch har _ hc ih =>
    obtain ⟨l₁', rfl, h₁⟩ := ih.ok (by simp)
    exact .inl ⟨l₁', rfl, .tryCatch har h₁ hc⟩
  | tryRethrow har _ hc ih => exact ih.mono (fun _ h => .tryRethrow har h hc) fun h => ⟨h, rfl⟩

/-! ## Canonical runs as session runs -/

/-- A canonical log `l` of a run ending in `o`: its image is a session log satisfying `P`, or it
ends in a cut call (an answer of more values than the callee's result arity) and the run in a
trap, and the image of the log before the cut call, then the call answered by a trap leaving the
cut call's store, satisfies `P`. -/
def ToS (l : List (OCall H)) (o : POut) (P : List (SCall H) → Prop) : Prop :=
  P (l.map oToS) ∨
  (o = .flow .trap ∧ ∃ (u : List (OCall H)) (g : Nat) (args : List Val) (s₁ s₂ : Store H)
    (ws : List Val) (fi : FuncInst H) (ps rs : List Validation.CValType),
    l = u ++ [OCall.mk g args s₁ (.inl ws) s₂] ∧ s₁.funcs[g]? = some fi ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧ rs.length < ws.length ∧
    P (u.map oToS ++ [SCall.mk g args s₁ (.inr ()) s₂]))

theorem ToS.mono {l : List (OCall H)} {o o' : POut} {P Q : List (SCall H) → Prop}
    (h : ToS l o P) (hP : ∀ l', P l' → Q l')
    (ho : o = .flow .trap → o' = .flow .trap) : ToS l o' Q := by
  rcases h with hp | ⟨ht, u, g, args, s₁, s₂, ws, fi, ps, rs, hl, hf, hty, hws, hp⟩
  · exact .inl (hP _ hp)
  · exact .inr ⟨ho ht, u, g, args, s₁, s₂, ws, fi, ps, rs, hl, hf, hty, hws, hP _ hp⟩

theorem ToS.app {l : List (OCall H)} {o : POut} {P Q : List (SCall H) → Prop}
    (pre : List (OCall H)) (h : ToS l o P) (hP : ∀ l', P l' → Q (pre.map oToS ++ l')) :
    ToS (pre ++ l) o Q := by
  rcases h with hp | ⟨ht, u, g, args, s₁, s₂, ws, fi, ps, rs, rfl, hf, hty, hws, hp⟩
  · exact .inl (by simpa using hP _ hp)
  · exact .inr ⟨ht, pre ++ u, g, args, s₁, s₂, ws, fi, ps, rs, by simp, hf, hty, hws,
      by simpa using hP _ hp⟩

theorem ToS.ok {l : List (OCall H)} {o : POut} {P : List (SCall H) → Prop} (h : ToS l o P)
    (ho : o ≠ .flow .trap) : P (l.map oToS) := by
  rcases h with h | ⟨ht, -⟩
  · exact h
  · exact absurd ht ho

/-- **A canonical run is a session run**, unless it ends in a cut call. -/
theorem evalLXPh_toS {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × POut} (h : EvalLXPh s f stk es l r) :
    ToS l r.2.2 (fun l' => EvalLXPS s f stk es l' r) := by
  induction h with
  | nil => exact .inl .nil
  | argsAbort _ ho ih => exact ih.mono (fun _ h => .argsAbort h ho) id
  | @callRet s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ l₂ r _ hfi hty _ ih₁ ih₂ =>
    have h₁ := ih₁.ok (by simp)
    have := ih₂.app (l₁ ++ [OCall.mk a (stk₁.take ps.length).reverse s₁ (.inl ws) s₂])
      (Q := fun l' => EvalLXPS s f stk (.op (.call x) args :: es) l' r)
      (fun _ h₂ => by simpa using EvalLXPS.callRet h₁ hfi hty h₂)
    simpa using this
  | callThrow _ hfi hty ih =>
    exact .inl (by simpa using EvalLXPS.callThrow (ih.ok (by simp)) hfi hty)
  | @callCut s s₁ s₂ f f₁ stk stk₁ ws x args es a fi ps rs l₁ _ hfi hty hws ih =>
    exact .inr ⟨rfl, l₁, a, _, s₁, s₂, ws, fi, ps, rs, rfl, funcs_of_func? hfi, hty, hws,
      .callTrap (ih.ok (by simp)) hfi hty⟩
  | opOk hi _ hflat _ ih₁ ih₂ =>
    exact ih₂.app _ (fun _ h₂ => .opOk hi (ih₁.ok (by simp)) hflat h₂)
  | opStop hi _ hflat hfl ih => exact .inl (.opStop hi (ih.ok (by simp)) hflat hfl)
  | blockOk har _ hvs _ ih₁ ih₂ =>
    exact ih₂.app _ (fun _ h₂ => .blockOk har (ih₁.ok (ne_trap_of_blockVals hvs)) hvs h₂)
  | blockBrk har _ ih => exact ih.mono (fun _ h => .blockBrk har h) (fun h => absurd h (by simp))
  | blockEsc har _ ho ih => exact ih.mono (fun _ h => .blockEsc har h ho) id
  | loopOk har _ _ ih₁ ih₂ => exact ih₂.app _ (fun _ h₂ => .loopOk har (ih₁.ok (by simp)) h₂)
  | loopBack har _ _ ih₁ ih₂ => exact ih₂.app _ (fun _ h₂ => .loopBack har (ih₁.ok (by simp)) h₂)
  | loopBrk har _ ih => exact ih.mono (fun _ h => .loopBrk har h) (fun h => absurd h (by simp))
  | loopEsc har _ ho ih => exact ih.mono (fun _ h => .loopEsc har h ho) id
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    have h₁ := ih₁.ok (by simp)
    have h₂ := ih₂.ok (ne_trap_of_blockVals hvs)
    exact ih₃.app (_ ++ _) (fun _ h₃ => by simpa using EvalLXPS.ifOk h₁ hb har h₂ hvs h₃)
  | ifBrk _ hb har _ ih₁ ih₂ =>
    exact .inl (by simpa using EvalLXPS.ifBrk (ih₁.ok (by simp)) hb har (ih₂.ok (by simp)))
  | ifEsc _ hb har _ ho ih₁ ih₂ =>
    exact ih₂.app _ (fun _ h₂ => .ifEsc (ih₁.ok (by simp)) hb har h₂ ho)
  | ifAbort _ ho ih => exact ih.mono (fun _ h => .ifAbort h ho) id
  | @indRet s s₁ s₂ f f₁ stk stk₁ ws x y args es ad i fa fi ps rs l₁ l₂ r _ hres hfi hty hy _
      ih₁ ih₂ =>
    have h₁ := ih₁.ok (by simp)
    have := ih₂.app (l₁ ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂])
      (Q := fun l' => EvalLXPS s f stk (.op (.callIndirect x y) args :: es) l' r)
      (fun _ h₂ => by simpa using EvalLXPS.indRet h₁ hres hfi hty hy h₂)
    simpa using this
  | indThrow _ hres hfi hty hy ih =>
    exact .inl (by simpa using EvalLXPS.indThrow (ih.ok (by simp)) hres hfi hty hy)
  | @indCut s s₁ s₂ f f₁ stk stk₁ ws x y args es ad i fa fi ps rs l₁ _ hres hfi hty hy hws ih =>
    exact .inr ⟨rfl, l₁, fa, _, s₁, s₂, ws, fi, ps, rs, rfl, hfi, hty, hws,
      .indTrap (ih.ok (by simp)) hres hfi hty hy⟩
  | indRes _ hres ih => exact .inl (.indRes (ih.ok (by simp)) hres)
  | @refRet s s₁ s₂ f f₁ stk stk₁ ws y args es fa fi ps rs l₁ l₂ r _ hfi hty hy _ ih₁ ih₂ =>
    have h₁ := ih₁.ok (by simp)
    have := ih₂.app (l₁ ++ [OCall.mk fa (stk₁.take ps.length).reverse s₁ (.inl ws) s₂])
      (Q := fun l' => EvalLXPS s f stk (.op (.callRef y) args :: es) l' r)
      (fun _ h₂ => by simpa using EvalLXPS.refRet h₁ hfi hty hy h₂)
    simpa using this
  | refThrow _ hfi hty hy ih =>
    exact .inl (by simpa using EvalLXPS.refThrow (ih.ok (by simp)) hfi hty hy)
  | @refCut s s₁ s₂ f f₁ stk stk₁ ws y args es fa fi ps rs l₁ _ hfi hty hy hws ih =>
    exact .inr ⟨rfl, l₁, fa, _, s₁, s₂, ws, fi, ps, rs, rfl, hfi, hty, hws,
      .refTrap (ih.ok (by simp)) hfi hty hy⟩
  | refNull _ ih => exact .inl (.refNull (ih.ok (by simp)))
  | tail _ hres hfi hty hy ih => exact .inl (.tail (ih.ok (by simp)) hres hfi hty hy)
  | tailRes _ hres ih => exact .inl (.tailRes (ih.ok (by simp)) hres)
  | throw _ ht he hn ih => exact .inl (.throw (ih.ok (by simp)) ht he hn)
  | throwRefNull _ ih => exact .inl (.throwRefNull (ih.ok (by simp)))
  | throwRefExn _ ih => exact .inl (.throwRefExn (ih.ok (by simp)))
  | tryOk har _ hvs _ ih₁ ih₂ =>
    exact ih₂.app _ (fun _ h₂ => .tryOk har (ih₁.ok (ne_trap_of_blockVals hvs)) hvs h₂)
  | tryBrk har _ ih => exact ih.mono (fun _ h => .tryBrk har h) (fun h => absurd h (by simp))
  | tryEsc har _ ho hnt ih => exact ih.mono (fun _ h => .tryEsc har h ho hnt) id
  | tryCatch har _ hc ih => exact .inl (.tryCatch har (ih.ok (by simp)) hc)
  | tryRethrow har _ hc ih => exact ih.mono (fun _ h => .tryRethrow har h hc) id

/-- A canonical run ending in a normal flow (or anything but a trap) is a session run. -/
theorem evalLXPh_toS_ok {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × POut} (h : EvalLXPh s f stk es l r)
    (ho : r.2.2 ≠ .flow .trap) : EvalLXPS s f stk es (l.map oToS) r :=
  (evalLXPh_toS h).ok ho

/-! ## The exact correspondence, through `OCall.toS` -/

theorem oToS_eq : (oToS : OCall H → SCall H) = OCall.toS := by
  funext z; rcases z with ⟨⟨⟨⟩⟩ | y, b, s'⟩; rfl

/-- **A session run is a canonical run, or ends in a trap answer read as every cut call.** -/
theorem evalLXPS_canonical_cut {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (SCall H)} {r : Store H × Frame × POut} (h : EvalLXPS s f stk es l r) :
    (∃ l', l = l'.map OCall.toS ∧ EvalLXPh s f stk es l' r) ∨
    (r.2.2 = .flow .trap ∧ ∃ (u : List (OCall H)) (g : Nat) (args : List Val) (s₁ s₂ : Store H),
      r.1 = s₂ ∧ l = u.map OCall.toS ++ [SCall.mk g args s₁ (.inr ()) s₂] ∧
      ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s₁.funcs[g]? = some fi ∧
        Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        ∀ ws : List Val, rs.length < ws.length →
          EvalLXPh s f stk es (u ++ [OCall.mk g args s₁ (.inl ws) s₂]) r) := by
  rw [← oToS_eq]; exact evalLXPS_toH h

/-- **A canonical run is a session run, or ends in a cut call read as a trap answer.** -/
theorem evalLXPh_session_cut {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × POut} (h : EvalLXPh s f stk es l r) :
    EvalLXPS s f stk es (l.map OCall.toS) r ∨
    (r.2.2 = .flow .trap ∧ ∃ (u : List (OCall H)) (g : Nat) (args : List Val) (s₁ s₂ : Store H)
      (ws : List Val) (fi : FuncInst H) (ps rs : List Validation.CValType),
      l = u ++ [OCall.mk g args s₁ (.inl ws) s₂] ∧ s₁.funcs[g]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ rs.length < ws.length ∧
      EvalLXPS s f stk es (u.map OCall.toS ++ [SCall.mk g args s₁ (.inr ()) s₂]) r) := by
  rw [← oToS_eq]; exact evalLXPh_toS h

/-! ## Reached calls answered by a trap -/

/-- **A reached call answered by a trap ends a session run**: the logged prefix, then the call
answered by a trap leaving the store `s''`, is a session run ending in a trap in `s''`. -/
theorem reachLXP_trapS {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {z : (wasmOShape H).self.Op} (h : ReachLXP s f stk es l z)
    (s'' : Store H) :
    ∃ f', EvalLXPS s f stk es (l.map oToS ++ [SCall.mk z.1 z.2.1 z.2.2 (.inr ()) s''])
      (s'', f', .flow .trap) := by
  induction h with
  | call hargs hfi hty => exact ⟨_, .callTrap (evalLXPh_toS_ok hargs (by simp)) hfi hty⟩
  | ind hargs hres hfi hty hy =>
    exact ⟨_, .indTrap (evalLXPh_toS_ok hargs (by simp)) hres hfi hty hy⟩
  | ref hargs hfi hty hy => exact ⟨_, .refTrap (evalLXPh_toS_ok hargs (by simp)) hfi hty hy⟩
  | args _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', .argsAbort h (by simp [POut.IsNormal, Flow.IsNormal])⟩
  | callK hargs hfi hty _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.callRet (evalLXPh_toS_ok hargs (by simp)) hfi hty h⟩
  | indK hargs hres hfi hty hy _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by
      simpa using EvalLXPS.indRet (evalLXPh_toS_ok hargs (by simp)) hres hfi hty hy h⟩
  | refK hargs hfi hty hy _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.refRet (evalLXPh_toS_ok hargs (by simp)) hfi hty hy h⟩
  | opK hi hargs hflat _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.opOk hi (evalLXPh_toS_ok hargs (by simp)) hflat h⟩
  | block har _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', .blockEsc har h (by simp [POut.Escapes, Flow.Escapes])⟩
  | blockK har hbody hvs _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by
      simpa using EvalLXPS.blockOk har (evalLXPh_toS_ok hbody (ne_trap_of_blockVals hvs)) hvs h⟩
  | loop har _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', .loopEsc har h (by simp [POut.Escapes, Flow.Escapes])⟩
  | loopK har hbody _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.loopOk har (evalLXPh_toS_ok hbody (by simp)) h⟩
  | loopBack har hbody _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by simpa using EvalLXPS.loopBack har (evalLXPh_toS_ok hbody (by simp)) h⟩
  | cond _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', .ifAbort h (by simp [POut.IsNormal, Flow.IsNormal])⟩
  | arm hc hb har _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by
      simpa using EvalLXPS.ifEsc (evalLXPh_toS_ok hc (by simp)) hb har h
        (by simp [POut.Escapes, Flow.Escapes])⟩
  | ifK hc hb har harm hvs _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by
      simpa using EvalLXPS.ifOk (evalLXPh_toS_ok hc (by simp)) hb har
        (evalLXPh_toS_ok harm (ne_trap_of_blockVals hvs)) hvs h⟩
  | handler har _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', .tryEsc har h (by simp [POut.Escapes, Flow.Escapes]) (by simp [POut.NotThrow])⟩
  | tryK har hbody hvs _ ih =>
    obtain ⟨f', h⟩ := ih
    exact ⟨f', by
      simpa using EvalLXPS.tryOk har (evalLXPh_toS_ok hbody (ne_trap_of_blockVals hvs)) hvs h⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingS
