module

public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Games.Abstract.Module.Thms

/-!
# The canonical relation with host calls as an open module: basic facts (proofs)

* `evalLXPh_of_evalL`: every `EvalL` run is an `EvalLXPh` run, ending in the same flow;
  so `wasmHOpen ≤ wasmHOpenXP` (`wasmHOpen_le`), and the closures are ordered alike.
* `close_ret`, `subst_ret`: a returning behaviour of a closure ends as an open behaviour does.
* `wasmHOpenXP_ret_len`, `close_ret_len`: a function returns at most its result arity, open and
  closed; so a cut call is never resolved by a return.
* `subst_last`: an internal call no behaviour of the closure answers can be replaced, at the end of
  a log, by any other answer and the open behaviour's end, keeping the resolved behaviour.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

universe u

variable {H : Type}

/-- Every native logged run is a canonical logged run, ending in the same flow. -/
theorem evalLXPh_of_evalL {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × Flow} (h : EvalL s f stk es l r) :
    EvalLXPh s f stk es l (r.1, r.2.1, .flow r.2.2) := by
  induction h with
  | nil => exact .nil
  | argsAbort _ hfl ih => exact .argsAbort ih hfl
  | callRet _ hfi hty _ ih₁ ih₂ => exact .callRet ih₁ hfi hty ih₂
  | callThrow _ hfi hty ih => exact .callThrow ih hfi hty
  | opOk hi _ hflat _ ih₁ ih₂ => exact .opOk hi ih₁ hflat ih₂
  | opStop hi _ hflat hfl ih => exact .opStop hi ih hflat hfl
  | blockOk har _ hvs _ ih₁ ih₂ => exact .blockOk har ih₁ hvs ih₂
  | blockBrk har _ ih => exact .blockBrk har ih
  | blockEsc har _ hfl ih => exact .blockEsc har ih hfl
  | loopOk har _ _ ih₁ ih₂ => exact .loopOk har ih₁ ih₂
  | loopBack har _ _ ih₁ ih₂ => exact .loopBack har ih₁ ih₂
  | loopBrk har _ ih => exact .loopBrk har ih
  | loopEsc har _ hfl ih => exact .loopEsc har ih hfl
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ => exact .ifOk ih₁ hb har ih₂ hvs ih₃
  | ifBrk _ hb har _ ih₁ ih₂ => exact .ifBrk ih₁ hb har ih₂
  | ifEsc _ hb har _ hfl ih₁ ih₂ => exact .ifEsc ih₁ hb har ih₂ hfl
  | ifAbort _ hfl ih => exact .ifAbort ih hfl

/-- The native open module is included in the canonical one. -/
theorem wasmHOpen_le : wasmHOpen (H := H) ≤ wasmHOpenXP := by
  rintro a s vs x (⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, hE, hxf, rfl⟩ |
    ⟨fi, hh, ps, rs, s', r, fl, hfi, hc, hty, hxf, rfl⟩)
  · exact .inl ⟨fi, fn, ps, rs, s', f₂, bfl, fl, l, hfi, hc, hty, evalLXPh_of_evalL hE, hxf, rfl⟩
  · exact .inr (.inr ⟨fi, hh, ps, rs, s', r, fl, hfi, hc, hty, hxf, rfl⟩)

/-- A resolved behaviour that returns ends as the open behaviour does. -/
theorem subst_ret {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod} {R : Type u}
    {x : List (Call (sh.E ⊕ₛ sh.self))}
    {e : End sh.S R} {y : CallBeh sh.E sh.S R} (h : Shape.Subst c x e y) :
    ∀ b s', y.2 = .ret b s' → e = .ret b s' := by
  induction h with
  | nil => exact fun _ _ h => h
  | ext _ ih => exact ih
  | int _ _ ih => exact ih
  | intTrap _ => exact fun _ _ h => nomatch h
  | intDiv _ => exact fun _ _ h => nomatch h

/-- A returning behaviour of a closure ends as an open behaviour does. -/
theorem close_ret {sh : Silmaril.Games.Abstract.Shape.{u}} {m : sh.OpenMod} {g : sh.F} {s : sh.S}
    {a : sh.A g}
    {c₁ : List (Call sh.E)} {b : sh.B g} {s' : sh.S} (h : (c₁, .ret b s') ∈ Shape.close m g s a) :
    ∃ x ∈ m g s a, x.2 = .ret b s' := by
  rw [← Shape.resolve_close] at h
  obtain ⟨x, hx, hs⟩ := h
  exact ⟨x, hx, subst_ret hs b s' rfl⟩

theorem exitFlow_len {n : Nat} {bfl fl : Flow} {s s' : Store H} {ws : List Val}
    (h : exitFlow n bfl = some fl) (he : endOfFlow fl s = .ret (.inl ws) s') : ws.length ≤ n := by
  rcases bfl with vs | ⟨_ | k, vs⟩ | vs | _ | t <;>
    simp only [exitFlow, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [endOfFlow, End.ret.injEq, Sum.inl.injEq, reduceCtorEq, false_and] at he <;>
    (obtain ⟨rfl, -⟩ := he; simp)

theorem tailAns_ret {m n : Nat} {b b' : List Val ⊕ Nat} {s₂ s' : Store H}
    (h : tailAns m n b s₂ = .ret b' s') :
    s' = s₂ ∧ ∀ ws, b' = .inl ws → ws.length ≤ m := by
  unfold tailAns at h
  split at h
  · rename_i fl hfl
    refine ⟨?_, fun ws hw => exitFlow_len hfl (hw ▸ h)⟩
    rcases fl <;> simp only [endOfFlow, End.ret.injEq, reduceCtorEq] at h <;> exact h.2.symm
  · exact nomatch h

/-- **A function returns at most its result arity** (open module). -/
theorem wasmHOpenXP_ret_len {a : Nat} {s : Store H} {vs : List Val}
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s vs)
    {ws : List Val} {s' : Store H} (he : x.2 = .ret (.inl ws) s') :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ ws.length ≤ rs.length := by
  rcases hx with ⟨fi, fn, ps, rs, s₁, f₂, bfl, fl, l, hfi, -, hty, -, hxf, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, hfi, -, hty, -, rfl⟩ |
    ⟨fi, hh, ps, rs, s₁, r, fl, hfi, -, hty, hxf, rfl⟩
  · exact ⟨fi, ps, rs, hfi, hty, exitFlow_len hxf he⟩
  · exact ⟨fi, ps, rs, hfi, hty, (tailAns_ret he).2 ws rfl⟩
  · exact ⟨fi, ps, rs, hfi, hty, exitFlow_len hxf he⟩

/-- **A function returns at most its result arity** (closure). -/
theorem close_ret_len {a : Nat} {s : Store H} {vs : List Val} {c₁ : List (Call (wasmHostSig H))}
    {ws : List Val} {s' : Store H} (h : (c₁, .ret (.inl ws) s') ∈ Shape.close wasmHOpenXP a s vs) :
    ∃ (fi : FuncInst H) (ps rs : List Validation.CValType), s.funcs[a]? = some fi ∧
      Validation.DefType.funcType? fi.type = some (ps, rs) ∧ ws.length ≤ rs.length := by
  obtain ⟨x, hx, he⟩ := close_ret h
  exact wasmHOpenXP_ret_len hx he

/-- An internal call at the end of a log that no behaviour of the closure answers resolves only by
the callee trapping or diverging, so its answer and the open end can be replaced. -/
theorem subst_last {sh : Silmaril.Games.Abstract.Shape.{u}} {c : sh.ClosedMod} {R : Type u}
    {g : sh.F} {a : sh.A g} {s₀ : sh.S} {b b' : sh.B g} {s₁ s₁' : sh.S}
    (hno : ∀ c₁, (c₁, .ret b s₁) ∉ c g s₀ a) {e e' : End sh.S R} {y : CallBeh sh.E sh.S R} :
    ∀ {L : List (Call (sh.E ⊕ₛ sh.self))},
      Shape.Subst c (L ++ [⟨.inr ⟨g, (a, s₀)⟩, (b, s₁)⟩]) e y →
      Shape.Subst c (L ++ [⟨.inr ⟨g, (a, s₀)⟩, (b', s₁')⟩]) e' y
  | [], h => by
    cases h with
    | int hc _ => exact (hno _ hc).elim
    | intTrap hc => exact .intTrap hc
    | intDiv hc => exact .intDiv hc
  | ⟨.inl _, _⟩ :: L, h => by
    cases h with
    | ext hs => exact .ext (subst_last hno hs)
  | ⟨.inr ⟨_, (_, _)⟩, (_, _)⟩ :: L, h => by
    cases h with
    | int hc hs => exact .int hc (subst_last hno hs)
    | intTrap hc => exact .intTrap hc
    | intDiv hc => exact .intDiv hc

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
