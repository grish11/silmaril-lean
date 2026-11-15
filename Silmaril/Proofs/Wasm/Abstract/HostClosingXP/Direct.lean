module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingXP.Basic
public import Silmaril.Wasm.Interp.HostEvalP.Thms
public import Silmaril.Wasm.Abstract.XRecursion.Thms

/-!
# The canonical open module on direct stores (proofs)

On direct, exception-free code (`CallX.xFreeL`, `CallXE.ehFreeL`) a canonical logged run is a
native one, or a cut call whose throwing variant is a native run (`evalLXPh_direct`). So on a
direct store (`Interp.StoreDirect`) the behaviours of `wasmHOpenXP` are those of `wasmHOpen`, and
cut behaviours (`wasmHOpenXP_direct`).

The closures agree on behaviours whose host answers leave direct stores (`close_direct`):
least-fixpoint induction, keeping the store's functions along the logs (`OChain`, `BChain`: every
call is made in a store with the functions of the previous answer's store, `evalLXPh_chain`), so
every internal call is made in a direct store; a cut call is never resolved by a return
(`close_ret_len`), so the native behaviour answering it by an exception resolves the same way
(`subst_last`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingXP

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Abstract.CallX (xFreeL xFree isXCall)
open Silmaril.Wasm.Abstract.CallXE (ehFreeL ehFree ehInstr)
open Silmaril.Wasm.Interp (StoreDirect storeDirect_of_funcs)

variable {H : Type}

theorem func?_funcs {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (h : s.func? f x = some (a, fi)) : s.funcs[a]? = some fi := by
  unfold Store.func? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨a', -, fi', hfi, rfl, rfl⟩ := h
  exact hfi

/-! ## Direct code -/

theorem tailRes_xcall {s : Store H} {f : Frame} {i : Instr} {stk : List Val}
    {r : Option (Nat × List Val)} (h : CallX.TailRes s f i stk r) : isXCall i = true := by
  cases h <;> rfl

/-- The cut alternative of a run: the log ends in a cut call, and answering it by an exception
instead is a native run. -/
def CutRun (s : Store H) (f : Frame) (stk : List Val) (es : List BExpr) (l : List (OCall H))
    (r : Store H × Frame × CallXP.POut) : Prop :=
  r.2.2 = .flow .trap ∧ ∃ (pre : List (OCall H)) (a' : Nat) (args : List Val) (s₁ : Store H)
    (ws : List Val) (fi : FuncInst H) (ps rs : List Validation.CValType),
    l = pre ++ [OCall.mk a' args s₁ (.inl ws) r.1] ∧ s₁.funcs[a']? = some fi ∧
    Validation.DefType.funcType? fi.type = some (ps, rs) ∧ rs.length < ws.length ∧
    EvalL s f stk es (pre ++ [OCall.mk a' args s₁ (.inr 0) r.1]) (r.1, r.2.1, .throw 0)

/-- A cut run lifted through a context that passes an exception on, after the calls `l₀`. -/
theorem cutRun_lift {s s' : Store H} {f f' : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {o : CallXP.POut} {s₀ : Store H} {f₀ : Frame} {stk₀ : List Val}
    {es₀ : List BExpr} (l₀ : List (OCall H)) (h : CutRun s f stk es l (s', f', o))
    (k : ∀ L, EvalL s f stk es L (s', f', .throw 0) →
      EvalL s₀ f₀ stk₀ es₀ (l₀ ++ L) (s', f', .throw 0)) :
    CutRun s₀ f₀ stk₀ es₀ (l₀ ++ l) (s', f', o) := by
  obtain ⟨ho, pre, a', args, s₁, ws, fi, ps, rs, rfl, hfi, hty, hlt, d⟩ := h
  exact ⟨ho, l₀ ++ pre, a', args, s₁, ws, fi, ps, rs, by simp, hfi, hty, hlt, by simpa using k _ d⟩

theorem iteX {b : Bool} {t el : List BExpr} (ht : xFreeL t = true) (he : xFreeL el = true) :
    xFreeL (if b then t else el) = true := by
  cases b <;> assumption

theorem iteE {b : Bool} {t el : List BExpr} (ht : ehFreeL t = true) (he : ehFreeL el = true) :
    ehFreeL (if b then t else el) = true := by
  cases b <;> assumption

/-- **On direct, exception-free code, a canonical logged run is a native one, or cut.** -/
theorem evalLXPh_direct {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × CallXP.POut} (h : EvalLXPh s f stk es l r) :
    xFreeL es = true → ehFreeL es = true →
      (∃ fl, r.2.2 = .flow fl ∧ EvalL s f stk es l (r.1, r.2.1, fl)) ∨ CutRun s f stk es l r := by
  induction h with
  | nil => exact fun _ _ => .inl ⟨_, rfl, .nil⟩
  | argsAbort _ ho ih =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih hx.1.2 he.1.2 with ⟨fl, rfl, d⟩ | hc
    · exact .inl ⟨fl, rfl, .argsAbort d ho⟩
    · exact .inr (by simpa using cutRun_lift [] hc fun L d => .argsAbort d (fun h => h))
  | callRet _ hfi hty _ ih₁ ih₂ =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih₁ hx.1.2 he.1.2 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl
      rcases ih₂ hx.2 he.2 with ⟨fl, hr, d₂⟩ | hc
      · exact .inl ⟨fl, hr, .callRet d₁ hfi hty d₂⟩
      · have := cutRun_lift (_ ++ [_]) hc fun L d => by simpa using EvalL.callRet d₁ hfi hty d
        exact .inr (by simpa using this)
    · exact nomatch hc.1
  | callThrow _ hfi hty ih =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih hx.1.2 he.1.2 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl; exact .inl ⟨_, rfl, .callThrow d₁ hfi hty⟩
    · exact nomatch hc.1
  | callCut _ hfi hty hws ih =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih hx.1.2 he.1.2 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl
      exact .inr ⟨rfl, _, _, _, _, _, _, _, _, rfl, func?_funcs hfi, hty, hws, .callThrow d₁ hfi hty⟩
    · exact nomatch hc.1
  | opOk hi _ hflat _ ih₁ ih₂ =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih₁ hx.1.2 he.1.2 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl
      rcases ih₂ hx.2 he.2 with ⟨fl, hr, d₂⟩ | hc
      · exact .inl ⟨fl, hr, .opOk hi d₁ hflat d₂⟩
      · exact .inr (cutRun_lift _ hc fun L d => .opOk hi d₁ hflat d)
    · exact nomatch hc.1
  | opStop hi _ hflat hfl ih =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih hx.1.2 he.1.2 with ⟨fl, hfl', d₁⟩ | hc
    · cases hfl'; exact .inl ⟨_, rfl, .opStop hi d₁ hflat hfl⟩
    · exact nomatch hc.1
  | blockOk har _ hvs _ ih₁ ih₂ =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih₁ hx.1 he.1 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl
      rcases ih₂ hx.2 he.2 with ⟨fl, hr, d₂⟩ | hc
      · exact .inl ⟨fl, hr, .blockOk har d₁ hvs d₂⟩
      · exact .inr (cutRun_lift _ hc fun L d => .blockOk har d₁ hvs d)
    · cases hc.1; simp [Flow.blockVals] at hvs
  | blockBrk har _ ih =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih hx.1 he.1 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl; exact .inl ⟨_, rfl, .blockBrk har d₁⟩
    · exact nomatch hc.1
  | blockEsc har _ ho ih =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih hx.1 he.1 with ⟨fl, rfl, d₁⟩ | hc
    · exact .inl ⟨_, rfl, .blockEsc har d₁ ho⟩
    · exact .inr (by simpa using cutRun_lift [] hc fun L d => .blockEsc har d trivial)
  | loopOk har _ _ ih₁ ih₂ =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih₁ hx.1 he.1 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl
      rcases ih₂ hx.2 he.2 with ⟨fl, hr, d₂⟩ | hc
      · exact .inl ⟨fl, hr, .loopOk har d₁ d₂⟩
      · exact .inr (cutRun_lift _ hc fun L d => .loopOk har d₁ d)
    · exact nomatch hc.1
  | loopBack har _ _ ih₁ ih₂ =>
    intro hx he
    have hx' := hx; have he' := he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx' he'
    rcases ih₁ hx'.1 he'.1 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl
      rcases ih₂ hx he with ⟨fl, hr, d₂⟩ | hc
      · exact .inl ⟨fl, hr, .loopBack har d₁ d₂⟩
      · exact .inr (cutRun_lift _ hc fun L d => .loopBack har d₁ d)
    · exact nomatch hc.1
  | loopBrk har _ ih =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih hx.1 he.1 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl; exact .inl ⟨_, rfl, .loopBrk har d₁⟩
    · exact nomatch hc.1
  | loopEsc har _ ho ih =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih hx.1 he.1 with ⟨fl, rfl, d₁⟩ | hc
    · exact .inl ⟨_, rfl, .loopEsc har d₁ ho⟩
    · exact .inr (by simpa using cutRun_lift [] hc fun L d => .loopEsc har d trivial)
  | ifOk _ hb har _ hvs _ ih₁ ih₂ ih₃ =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih₁ hx.1.1.1 he.1.1.1 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl
      rcases ih₂ (iteX hx.1.1.2 hx.1.2) (iteE he.1.1.2 he.1.2) with ⟨fl, hfl, d₂⟩ | hc
      · cases hfl
        rcases ih₃ hx.2 he.2 with ⟨fl, hr, d₃⟩ | hc
        · exact .inl ⟨fl, hr, .ifOk d₁ hb har d₂ hvs d₃⟩
        · exact .inr (cutRun_lift _ hc fun L d => .ifOk d₁ hb har d₂ hvs d)
      · cases hc.1; simp [Flow.blockVals] at hvs
    · exact nomatch hc.1
  | ifBrk _ hb har _ ih₁ ih₂ =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih₁ hx.1.1.1 he.1.1.1 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl
      rcases ih₂ (iteX hx.1.1.2 hx.1.2) (iteE he.1.1.2 he.1.2) with ⟨fl, hfl, d₂⟩ | hc
      · cases hfl; exact .inl ⟨_, rfl, .ifBrk d₁ hb har d₂⟩
      · exact nomatch hc.1
    · exact nomatch hc.1
  | ifEsc _ hb har _ ho ih₁ ih₂ =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih₁ hx.1.1.1 he.1.1.1 with ⟨fl, hfl, d₁⟩ | hc
    · cases hfl
      rcases ih₂ (iteX hx.1.1.2 hx.1.2) (iteE he.1.1.2 he.1.2) with ⟨fl, rfl, d₂⟩ | hc
      · exact .inl ⟨_, rfl, .ifEsc d₁ hb har d₂ ho⟩
      · exact .inr (cutRun_lift _ hc fun L d => .ifEsc d₁ hb har d trivial)
    · exact nomatch hc.1
  | ifAbort _ ho ih =>
    intro hx he
    simp only [xFreeL, xFree, ehFreeL, ehFree, Bool.and_eq_true] at hx he
    rcases ih hx.1.1.1 he.1.1.1 with ⟨fl, rfl, d₁⟩ | hc
    · exact .inl ⟨_, rfl, .ifAbort d₁ ho⟩
    · exact .inr (by simpa using cutRun_lift [] hc fun L d => .ifAbort d (fun h => h))
  | indRet | indThrow | indCut | indRes | refRet | refThrow | refCut | refNull =>
    intro hx _
    simp [xFreeL, xFree, isXCall] at hx
  | tail _ hres _ _ _ _ =>
    intro hx _
    simp only [xFreeL, xFree, Bool.and_eq_true, Bool.not_eq_true', tailRes_xcall hres] at hx
    exact nomatch hx.1.1
  | tailRes _ hres _ =>
    intro hx _
    simp only [xFreeL, xFree, Bool.and_eq_true, Bool.not_eq_true', tailRes_xcall hres] at hx
    exact nomatch hx.1.1
  | throw | throwRefNull | throwRefExn =>
    intro _ he
    simp [ehFreeL, ehFree, ehInstr] at he
  | tryOk | tryBrk | tryEsc | tryCatch | tryRethrow =>
    intro _ he
    simp [ehFreeL, ehFree] at he

/-! ## Functions along logs -/

/-- Every call of a log is made in a store with the functions of the previous answer's store (the
first, of `s`), and the run ends in a store with the functions of the last answer's store. -/
inductive OChain : Store H → List (OCall H) → Store H → Prop where
  | nil {s s' : Store H} (h : s'.funcs = s.funcs) : OChain s [] s'
  | cons {s s₀ s₂ s' : Store H} {a : Nat} {args : List Val} {b : List Val ⊕ Nat}
      {L : List (OCall H)} (h : s₀.funcs = s.funcs) (t : OChain s₂ L s') :
      OChain s (OCall.mk a args s₀ b s₂ :: L) s'

theorem OChain.start {s₁ s s' : Store H} {L : List (OCall H)} (h : OChain s₁ L s')
    (he : s₁.funcs = s.funcs) : OChain s L s' := by
  cases h with
  | nil h' => exact .nil (h'.trans he)
  | cons h' t => exact .cons (h'.trans he) t

theorem OChain.fin {s s₁ s₂ : Store H} {L : List (OCall H)} (h : OChain s L s₁)
    (he : s₂.funcs = s₁.funcs) : OChain s L s₂ := by
  induction h with
  | nil h' => exact .nil (he.trans h')
  | cons h' _ ih => exact .cons h' (ih he)

theorem OChain.append {s s₁ s' : Store H} {L₁ L₂ : List (OCall H)} (h₁ : OChain s L₁ s₁)
    (h₂ : OChain s₁ L₂ s') : OChain s (L₁ ++ L₂) s' := by
  induction h₁ with
  | nil h => exact h₂.start h
  | cons h _ ih => exact .cons h (ih h₂)

theorem oChain_call {s s₁ s₂ s' : Store H} {L₁ L₂ : List (OCall H)} {a : Nat} {args : List Val}
    {b : List Val ⊕ Nat} (h₁ : OChain s L₁ s₁) (h₂ : OChain s₂ L₂ s') :
    OChain s (L₁ ++ OCall.mk a args s₁ b s₂ :: L₂) s' :=
  h₁.append (.cons rfl h₂)

/-- **A canonical logged run keeps the functions along its log.** -/
theorem evalLXPh_chain {s : Store H} {f : Frame} {stk : List Val} {es : List BExpr}
    {l : List (OCall H)} {r : Store H × Frame × CallXP.POut} (h : EvalLXPh s f stk es l r) :
    OChain s l r.1 := by
  induction h with
  | nil => exact .nil rfl
  | argsAbort _ _ ih => exact ih
  | callRet _ _ _ _ ih₁ ih₂ => exact oChain_call ih₁ ih₂
  | callThrow _ _ _ ih => exact oChain_call ih (.nil rfl)
  | callCut _ _ _ _ ih => exact oChain_call ih (.nil rfl)
  | opOk _ _ hflat _ ih₁ ih₂ => exact ih₁.append (ih₂.start (XRecursion.evalFlat_funcs hflat))
  | opStop _ _ hflat _ ih => exact ih.fin (XRecursion.evalFlat_funcs hflat)
  | blockOk _ _ _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | blockBrk _ _ ih => exact ih
  | blockEsc _ _ _ ih => exact ih
  | loopOk _ _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | loopBack _ _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | loopBrk _ _ ih => exact ih
  | loopEsc _ _ _ ih => exact ih
  | ifOk _ _ _ _ _ _ ih₁ ih₂ ih₃ => exact (ih₁.append ih₂).append ih₃
  | ifBrk _ _ _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | ifEsc _ _ _ _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | ifAbort _ _ ih => exact ih
  | indRet _ _ _ _ _ _ ih₁ ih₂ => exact oChain_call ih₁ ih₂
  | indThrow _ _ _ _ _ ih => exact oChain_call ih (.nil rfl)
  | indCut _ _ _ _ _ _ ih => exact oChain_call ih (.nil rfl)
  | indRes _ _ ih => exact ih
  | refRet _ _ _ _ _ ih₁ ih₂ => exact oChain_call ih₁ ih₂
  | refThrow _ _ _ _ ih => exact oChain_call ih (.nil rfl)
  | refCut _ _ _ _ _ ih => exact oChain_call ih (.nil rfl)
  | refNull _ ih => exact ih
  | tail _ _ _ _ _ ih => exact ih
  | tailRes _ _ ih => exact ih
  | throw _ _ _ _ ih => exact ih.fin rfl
  | throwRefNull _ ih => exact ih
  | throwRefExn _ ih => exact ih
  | tryOk _ _ _ _ ih₁ ih₂ => exact ih₁.append ih₂
  | tryBrk _ _ ih => exact ih
  | tryEsc _ _ _ _ ih => exact ih
  | tryCatch _ _ _ ih => exact ih
  | tryRethrow _ _ _ ih => exact ih

/-- `OChain` for the logs of the open module, the end's store included. -/
inductive BChain {R : Type} : Store H → List (HCall H) → End (Store H) R → Prop where
  | nil {s : Store H} {e : End (Store H) R} (h : ∀ b s', e = .ret b s' → s'.funcs = s.funcs) :
      BChain s [] e
  | ext {s : Store H} {m : (wasmHostSig H).Op} {n : (wasmHostSig H).Ar m} {L : List (HCall H)}
      {e : End (Store H) R} (h : m.2.1.funcs = s.funcs) (t : BChain n.1 L e) :
      BChain s (⟨.inl m, n⟩ :: L) e
  | int {s s₀ s₂ : Store H} {g : Nat} {a : List Val} {b : List Val ⊕ Nat} {L : List (HCall H)}
      {e : End (Store H) R} (h : s₀.funcs = s.funcs) (t : BChain s₂ L e) :
      BChain s (⟨.inr ⟨g, (a, s₀)⟩, (b, s₂)⟩ :: L) e

theorem bChain_of {R : Type} {s s' : Store H} {L : List (OCall H)} (h : OChain s L s')
    {e : End (Store H) R} (he : ∀ b s'', e = .ret b s'' → s''.funcs = s'.funcs) :
    BChain s (L.map OCall.lift) e := by
  induction h with
  | nil h => exact .nil fun b s'' hb => (he b s'' hb).trans h
  | cons h _ ih => exact .int h (ih he)

/-- **The open behaviours keep the functions along their logs.** -/
theorem open_chain {a : Nat} {s : Store H} {vs : List Val}
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s vs) : BChain s x.1 x.2 := by
  rcases hx with ⟨fi, fn, ps, rs, s₁, f₂, bfl, fl, l, -, -, -, hE, -, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, -, -, -, hE, rfl⟩ |
    ⟨fi, hh, ps, rs, s₁, r, fl, -, -, -, -, rfl⟩
  · refine bChain_of (evalLXPh_chain hE) fun b s'' hb => ?_
    rcases fl <;> simp only [endOfFlow, End.ret.injEq, reduceCtorEq] at hb <;> rw [hb.2]
  · refine bChain_of ((evalLXPh_chain hE).append (.cons rfl (.nil rfl))) fun b' s'' hb => ?_
    rw [(tailAns_ret hb).1]
  · refine .ext rfl (.nil fun b s'' hb => ?_)
    rcases fl <;> simp only [endOfFlow, End.ret.injEq, reduceCtorEq] at hb <;> rw [hb.2]

/-! ## The open modules on direct stores -/

/-- **On a direct store, a canonical open behaviour is native, or cut.** -/
theorem wasmHOpenXP_direct {a : Nat} {s : Store H} {vs : List Val} (hs : StoreDirect s)
    {x : CallBeh ((wasmHShape H).E ⊕ₛ (wasmHShape H).self) (Store H) (List Val ⊕ Nat)}
    (hx : x ∈ wasmHOpenXP a s vs) :
    x ∈ wasmHOpen a s vs ∨
      (x.2 = .trap ∧ ∃ (pre : List (OCall H)) (a' : Nat) (args : List Val) (s₁ s₂ : Store H)
        (ws : List Val) (fi : FuncInst H) (ps rs : List Validation.CValType),
        x.1 = (pre ++ [OCall.mk a' args s₁ (.inl ws) s₂]).map OCall.lift ∧
        s₁.funcs[a']? = some fi ∧ Validation.DefType.funcType? fi.type = some (ps, rs) ∧
        rs.length < ws.length ∧
        ((pre ++ [OCall.mk a' args s₁ (.inr 0) s₂]).map OCall.lift, .ret (.inr 0) s₂) ∈
          wasmHOpen a s vs) := by
  rcases hx with ⟨fi, fn, ps, rs, s₁, f₂, bfl, fl, l, hfi, hc, hty, hE, hxf, rfl⟩ |
    ⟨fi, fn, ps, rs, s₁, s₂, f₂, a', n, args, b, l, hfi, hc, hty, hE, rfl⟩ |
    ⟨fi, hh, ps, rs, s₁, r, fl, hfi, hc, hty, hxf, rfl⟩
  · obtain ⟨hxb, heb⟩ := hs a fi fn hfi hc
    rcases evalLXPh_direct hE hxb heb with ⟨fl', hfl, d⟩ | ⟨ho, pre, a', args, s₀, ws, fi', ps',
        rs', hl, hfi', hty', hlt, d⟩
    · cases hfl
      exact .inl (.inl ⟨fi, fn, ps, rs, s₁, f₂, bfl, fl, l, hfi, hc, hty, d, hxf, rfl⟩)
    · cases ho
      simp only [exitFlow, Option.some.injEq] at hxf
      subst hxf hl
      exact .inr ⟨rfl, pre, a', args, s₀, s₁, ws, fi', ps', rs', rfl, hfi', hty', hlt,
        .inl ⟨fi, fn, ps, rs, s₁, f₂, .throw 0, .throw 0, _, hfi, hc, hty, d, rfl, rfl⟩⟩
  · obtain ⟨hxb, heb⟩ := hs a fi fn hfi hc
    rcases evalLXPh_direct hE hxb heb with ⟨fl', hfl, -⟩ | hc
    · exact nomatch hfl
    · exact nomatch hc.1
  · exact .inl (.inr ⟨fi, hh, ps, rs, s₁, r, fl, hfi, hc, hty, hxf, rfl⟩)

/-! ## The closures on direct stores -/

/-- What the canonical closure is shown below: from a direct store, a behaviour whose host answers
leave direct stores is native, and returns to a direct store. -/
def GD : (wasmHShape H).ClosedMod := fun a s vs =>
  {y | StoreDirect s → (∀ c ∈ y.1, StoreDirect c.2.1) →
    y ∈ Shape.close wasmHOpen a s vs ∧ ∀ b s', y.2 = .ret b s' → StoreDirect s'}

theorem subst_GD {x : List (HCall H)} {e : End (Store H) (List Val ⊕ Nat)}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} (h : Shape.Subst GD x e y) :
    ∀ {s : Store H}, BChain s x e → StoreDirect s → (∀ c ∈ y.1, StoreDirect c.2.1) →
      Shape.Subst (Shape.close wasmHOpen) x e y ∧ ∀ b s', y.2 = .ret b s' → StoreDirect s' := by
  induction h with
  | nil e =>
    intro s hb hs _
    cases hb with
    | nil h => exact ⟨.nil e, fun b s' he => storeDirect_of_funcs (h b s' he) hs⟩
  | ext _ ih =>
    intro s hb hs hy
    cases hb with
    | ext h t =>
      obtain ⟨d, hr⟩ := ih t (hy _ List.mem_cons_self) fun c hc => hy c (List.mem_cons_of_mem _ hc)
      exact ⟨.ext d, hr⟩
  | int hc _ ih =>
    intro s hb hs hy
    cases hb with
    | int h t =>
      obtain ⟨hc', hd⟩ := hc (storeDirect_of_funcs h hs) fun c h' => hy c (List.mem_append_left _ h')
      obtain ⟨d, hr⟩ := ih t (hd _ _ rfl) fun c h' => hy c (List.mem_append_right _ h')
      exact ⟨.int hc' d, hr⟩
  | intTrap hc =>
    intro s hb hs hy
    cases hb with
    | int h t => exact ⟨.intTrap (hc (storeDirect_of_funcs h hs) hy).1, fun _ _ h => nomatch h⟩
  | intDiv hc =>
    intro s hb hs hy
    cases hb with
    | int h t => exact ⟨.intDiv (hc (storeDirect_of_funcs h hs) hy).1, fun _ _ h => nomatch h⟩

theorem close_le_GD : Shape.close (wasmHOpenXP (H := H)) ≤ GD := by
  refine OrderHom.lfp_le _ ?_
  rintro a s vs y ⟨x, hx, hS⟩ hs hy
  obtain ⟨d, hr⟩ := subst_GD hS (open_chain hx) hs hy
  refine ⟨?_, hr⟩
  rw [← Shape.resolve_close]
  rcases wasmHOpenXP_direct hs hx with hx' | ⟨he, pre, a', args, s₁, s₂, ws, fi, ps, rs, hl, hfi,
      hty, hlt, hx'⟩
  · exact ⟨x, hx', d⟩
  · refine ⟨_, hx', ?_⟩
    rw [hl, he, List.map_append] at d
    rw [List.map_append]
    refine subst_last (fun c₁ hc => ?_) d
    obtain ⟨fi', ps', rs', hfi', hty', hle⟩ :=
      close_ret_len (Shape.close_mono wasmHOpen_le _ _ _ hc)
    rw [hfi] at hfi'
    cases hfi'
    rw [hty] at hty'
    cases hty'
    omega

/-- **On direct stores the closures agree**, on behaviours whose host answers leave direct
stores. -/
theorem close_direct {a : Nat} {s : Store H} {vs : List Val} (hs : StoreDirect s)
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} (hy : ∀ c ∈ y.1, StoreDirect c.2.1) :
    y ∈ Shape.close wasmHOpenXP a s vs ↔ y ∈ Shape.close wasmHOpen a s vs :=
  ⟨fun h => (close_le_GD a s vs h hs hy).1, fun h => Shape.close_mono wasmHOpen_le a s vs h⟩

/-- What a host keeping direct stores allows of the canonical closure: from a direct store, a
behaviour whose log it allows has direct answer stores, and returns to a direct store. -/
def GK (host : HostSemantics H) : (wasmHShape H).ClosedMod := fun _ s _ =>
  {y | StoreDirect s → (coreHostRel host).Consistent y.1 →
    (∀ c ∈ y.1, StoreDirect c.2.1) ∧ ∀ b s', y.2 = .ret b s' → StoreDirect s'}

theorem subst_GK {host : HostSemantics H} (hD : Interp.HostKeepsDirect host)
    {x : List (HCall H)} {e : End (Store H) (List Val ⊕ Nat)}
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)} (h : Shape.Subst (GK host) x e y) :
    ∀ {s : Store H}, BChain s x e → StoreDirect s → (coreHostRel host).Consistent y.1 →
      (∀ c ∈ y.1, StoreDirect c.2.1) ∧ ∀ b s', y.2 = .ret b s' → StoreDirect s' := by
  induction h with
  | nil e =>
    intro s hb hs _
    cases hb with
    | nil h => exact ⟨nofun, fun b s' he => storeDirect_of_funcs (h b s' he) hs⟩
  | ext _ ih =>
    intro s hb hs hy
    cases hb with
    | ext h t =>
      have hn := hD _ _ _ _ _ (hy _ List.mem_cons_self) (storeDirect_of_funcs h hs)
      obtain ⟨d, hr⟩ := ih t hn fun c hc => hy c (List.mem_cons_of_mem _ hc)
      refine ⟨fun c hc => ?_, hr⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hn
      · exact d c hc
  | int hc _ ih =>
    intro s hb hs hy
    cases hb with
    | int h t =>
      obtain ⟨d₁, hd⟩ :=
        hc (storeDirect_of_funcs h hs) fun c h' => hy c (List.mem_append_left _ h')
      obtain ⟨d, hr⟩ := ih t (hd _ _ rfl) fun c h' => hy c (List.mem_append_right _ h')
      exact ⟨fun c hc => (List.mem_append.1 hc).elim (d₁ c) (d c), hr⟩
  | intTrap hc =>
    intro s hb hs hy
    cases hb with
    | int h t => exact ⟨(hc (storeDirect_of_funcs h hs) hy).1, fun _ _ h => nomatch h⟩
  | intDiv hc =>
    intro s hb hs hy
    cases hb with
    | int h t => exact ⟨(hc (storeDirect_of_funcs h hs) hy).1, fun _ _ h => nomatch h⟩

theorem close_le_GK {host : HostSemantics H} (hD : Interp.HostKeepsDirect host) :
    Shape.close (wasmHOpenXP (H := H)) ≤ GK host := by
  refine OrderHom.lfp_le _ ?_
  rintro a s vs y ⟨x, hx, hS⟩ hs hy
  exact subst_GK hD hS (open_chain hx) hs hy

/-- **On direct stores the closures agree on behaviours a host keeping direct stores allows.** -/
theorem close_direct_consistent {host : HostSemantics H} (hD : Interp.HostKeepsDirect host)
    {a : Nat} {s : Store H} {vs : List Val} (hs : StoreDirect s)
    {y : CallBeh (wasmHostSig H) (Store H) (List Val ⊕ Nat)}
    (hc : (coreHostRel host).Consistent y.1) :
    y ∈ Shape.close wasmHOpenXP a s vs ↔ y ∈ Shape.close wasmHOpen a s vs :=
  ⟨fun h => (close_direct hs ((close_le_GK hD a s vs h hs hc).1)).1 h,
    fun h => Shape.close_mono wasmHOpen_le a s vs h⟩

end Silmaril.Proofs.Wasm.Abstract.HostClosingXP
