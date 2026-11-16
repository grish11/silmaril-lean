module

public import Silmaril.Wasm.Abstract.SelfLoop.Defs
public import Silmaril.Wasm.Abstract.Closing.Thms

/-!
# Unbounded recursion: proofs

A self-looping function has no derivation of the recursive big-step relation
(each derivation of its call contains one of the same call). So it has no
closed outcome, and `Shape.close` gives it nothing. Its logged run reaches its
own call at once, and that gives the constant infinite internal-call chain
that `Shape.closeD` turns into `div`.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.SelfLoop

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

theorem func?_eq {s : Store H} {f : Frame} {x : FuncIdx} {a a' : Nat} {fi fi' : FuncInst H}
    (h : s.func? f x = some (a', fi')) (hx : f.module.funcs[x.toNat]? = some a)
    (hfi : s.funcs[a]? = some fi) : a' = a ∧ fi' = fi := by
  unfold Store.func? at h
  simp only [hx, hfi, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
    Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

theorem func?_of {s : Store H} {f : Frame} {x : FuncIdx} {a : Nat} {fi : FuncInst H}
    (hx : f.module.funcs[x.toNat]? = some a) (hfi : s.funcs[a]? = some fi) :
    s.func? f x = some (a, fi) := by
  unfold Store.func?
  simp [hx, hfi]

/-- No derivation of the recursive semantics runs the self call. -/
theorem no_eval {s : Store H} {fi : FuncInst H} {fn : Func} {x : FuncIdx} {a : Nat}
    (hfi : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn) (hbody : fn.body = [.call x])
    (hx : fi.module.funcs[x.toNat]? = some a) {s' : Store H} {f : Frame} {stk : List Val}
    {es : List BExpr} {r : Store H × Frame × Flow} (h : Eval s' f stk es r) :
    s' = s → f.module = fi.module → es = [.op (.call x) []] → False := by
  have back : ∀ {f₁ : Frame} {x' : FuncIdx} {a' : Nat} {fi' : FuncInst H} {fn' : Func},
      f₁.module = fi.module → x' = x → s.func? f₁ x' = some (a', fi') → fi'.code = .wasm fn' →
      fi' = fi ∧ liftInstrs fn'.body = [.op (.call x) []] := by
    intro f₁ x' a' fi' fn' hm hx' hf hc
    subst hx'
    obtain ⟨rfl, rfl⟩ := func?_eq hf (hm ▸ hx) hfi
    obtain rfl : fn' = fn := FuncCode.wasm.inj (hc.symm.trans hcode)
    exact ⟨rfl, by rw [hbody]; rfl⟩
  induction h with
  | callOk hargs hfi' hcode' _ _ _ _ _ ih _ =>
    intro hs hm he
    simp only [List.cons.injEq, BExpr.op.injEq, Instr.call.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    cases hargs
    subst hs
    obtain ⟨rfl, hl⟩ := back hm rfl hfi' hcode'
    exact ih rfl rfl hl
  | callTrap hargs hfi' hcode' _ _ _ ih =>
    intro hs hm he
    simp only [List.cons.injEq, BExpr.op.injEq, Instr.call.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    cases hargs
    subst hs
    obtain ⟨rfl, hl⟩ := back hm rfl hfi' hcode'
    exact ih rfl rfl hl
  | callThrow hargs hfi' hcode' _ _ _ ih =>
    intro hs hm he
    simp only [List.cons.injEq, BExpr.op.injEq, Instr.call.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    cases hargs
    subst hs
    obtain ⟨rfl, hl⟩ := back hm rfl hfi' hcode'
    exact ih rfl rfl hl
  | argsAbort hargs hfl =>
    intro _ _ he
    simp only [List.cons.injEq, BExpr.op.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    cases hargs
    exact hfl trivial
  | opOk hi => intro _ _ he; simp only [List.cons.injEq, BExpr.op.injEq] at he; exact hi x he.1.1
  | opStop hi => intro _ _ he; simp only [List.cons.injEq, BExpr.op.injEq] at he; exact hi x he.1.1
  | _ => intro _ _ he; simp at he

/-- A self-looping function has no closed outcome. -/
theorem no_closedOutcome {s : Store H} {a : Nat} (h : SelfLoop s a) (vs : List Val) (s' : Store H)
    (fl : Flow) : ¬ ClosedOutcome s a vs s' fl := by
  obtain ⟨fi, fn, x, ps, rs, hfi, hcode, hbody, hx, -⟩ := h
  rintro ⟨fi', fn', ps', rs', f₂, bfl, hfi', hcode', -, he, -⟩
  obtain rfl : fi' = fi := Option.some.inj (hfi'.symm.trans hfi)
  obtain rfl : fn' = fn := FuncCode.wasm.inj (hcode'.symm.trans hcode)
  exact no_eval hfi hcode hbody hx (evalO_closed_iff.mp he) rfl rfl (by rw [hbody]; rfl)

theorem close_eq_empty {s : Store H} {a : Nat} (h : SelfLoop s a) (vs : List Val) :
    Shape.close wasmOpen a s vs = ∅ := by
  rw [close_wasmOpen, Set.eq_empty_iff_forall_notMem]
  rintro _ ⟨s', fl, hc, -⟩
  exact no_closedOutcome h vs s' fl hc

/-- The logged run of a self-looping function reaches its own call at once. -/
theorem descends {s : Store H} {a : Nat} (h : SelfLoop s a) (c : (wasmOShape H).ClosedMod)
    (vs : List Val) : Shape.Descends wasmOpen c ⟨a, (vs, s)⟩ [] ⟨a, ([], s)⟩ := by
  obtain ⟨fi, fn, x, ps, rs, hfi, hcode, hbody, hx, hty⟩ := h
  have hf : s.func? (Frame.forCall fi.module vs fn.locals) x = some (a, fi) := func?_of hx hfi
  have d : EvalL s (Frame.forCall fi.module vs fn.locals) [] (liftInstrs fn.body)
      [OCall.mk a [] s (.inr 0) s] (s, Frame.forCall fi.module vs fn.locals, .throw 0) := by
    rw [hbody]
    exact show EvalL _ _ _ [.op (.call x) []] _ _ by simpa using EvalL.callThrow (stk := []) (es := []) (l₁ := []) (t := 0) (s₂ := s) .nil hf hty
  exact ⟨([OCall.mk a [] s (.inr 0) s], endOfFlow (.throw 0) s),
    ⟨fi, fn, ps, rs, s, _, .throw 0, .throw 0, hfi, hcode, hty, d, rfl, rfl⟩,
    [], ((.inr 0 : List Val ⊕ Nat), s), [], rfl, .nil⟩

theorem nil_of_empty : ∀ l : List (Call (Sig.empty.{0})), l = []
  | [] => rfl
  | ⟨m, _⟩ :: _ => PEmpty.elim m

/-- `closeD` gives a self-looping function exactly divergence. -/
theorem closeD_eq {s : Store H} {a : Nat} (h : SelfLoop s a) (vs : List Val) :
    Shape.closeD wasmOpen a s vs = {([], .div)} := by
  ext ⟨q, e⟩
  obtain rfl := nil_of_empty q
  simp only [Shape.closeD, close_eq_empty h, Set.empty_union, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, Prod.mk.injEq, true_and]
  refine ⟨fun h => h.1, fun he => ⟨he, ?_⟩⟩
  refine ⟨fun n => if n = 0 then ⟨a, (vs, s)⟩ else ⟨a, ([], s)⟩, fun _ => [], 0, rfl, ?_,
    fun _ _ => rfl, rfl⟩
  intro n
  rcases n with _ | n
  · exact descends h _ vs
  · exact descends h _ []

/-- With the Core hypotheses, the Core 3.0 abstract function of a self-looping
function is exactly divergence. -/
theorem wasmFun_eq {s : Store H} {a : Nat} (h : SelfLoop s a) {vs : List Val} (hs : StoreOk s)
    (hF : NativeFuncsOk s.funcs) (hS : Silmaril.Wasm.Interp.StoreChk s.funcs)
    (hok : InvokeOk s a vs) (P : Numerics.Profile) :
    wasmFun P closedHost a s vs = {([], .div)} := by
  rw [wasmFun_eq_close hs hF hS hok P, close_eq_empty h]
  ext y
  simp

theorem selfLoop_of_selfLoopB {s : Store H} {a : Nat} (h : selfLoopB s a = true) : SelfLoop s a := by
  unfold selfLoopB at h
  rcases hf : s.funcs[a]? with _ | fi
  · simp [hf] at h
  rcases hc : fi.code with fn | hh
  · rcases hb : fn.body with _ | ⟨i, _ | ⟨j, rest⟩⟩
    · simp [hf, hc, hb] at h
    · cases i <;> simp only [hf, hc, hb, Bool.false_eq_true] at h
      rename_i x
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at h
      obtain ⟨hx, ⟨ps, rs⟩, hty⟩ := h
      exact ⟨fi, fn, x, ps, rs, hf, hc, hb, hx, hty⟩
    · cases i <;> simp [hf, hc, hb] at h
  · simp [hf, hc] at h

end Silmaril.Proofs.Wasm.Abstract.SelfLoop
