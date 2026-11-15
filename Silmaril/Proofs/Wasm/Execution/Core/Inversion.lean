module

public import Silmaril.Wasm.Execution.Core.Inversion.Defs
public import Silmaril.Wasm.Execution.Core.Properties
public import Silmaril.Wasm.Execution.Core.Sim.Context
public import Silmaril.Wasm.SingleThreaded.Determinism.Family

@[expose] public section

namespace Silmaril.Wasm.Execution.Core.Proofs.Inversion

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (Det.famOf Det.Fam Det.FamShape)

variable {H : Type} {P : Profile} {host : HostSemantics H}

-- One closing tactic serves every rule; on some rules some of its branches are unused.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

/-- A context `vals vs ++ X ++ rest` with a nonempty prefix or suffix is not a single
instruction. -/
theorem split_single {a : Admin} {vs : List Val} {X rest : List Admin}
    (hc : vals vs ++ X ++ rest = [a]) (hX : X ≠ []) (hne : vs ≠ [] ∨ rest ≠ []) : False := by
  have hl := congrArg List.length hc
  have := List.length_pos_iff.2 hX
  simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hl
  rcases hne with h | h
  · exact h (List.eq_nil_of_length_eq_zero (by omega))
  · exact h (List.eq_nil_of_length_eq_zero (by omega))

/-- `ctxt-instrs` never applies to a one-instruction code. -/
theorem ctxt_single {a : Admin} {vs : List Val} {is rest : List Admin}
    (hc : vals vs ++ is ++ rest = [a]) (his : is.all Admin.isVal = false)
    (hne : vs ≠ [] ∨ rest ≠ []) : False :=
  split_single hc (by rintro rfl; simp at his) hne

/-- The last instruction of a family left-hand side is of that family. -/
theorem famShape_last {k : Det.Fam} {a : Admin} {l : List Admin} (h : Det.FamShape k l)
    (hl : l.getLast? = some a) : Det.famOf a = k := by
  obtain ⟨args, e, rfl, -, hk⟩ := h
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq] at hl
  exact hl ▸ hk

section
open SingleThreaded.Det
variable {a : Admin}
theorem fam_parametric {l l' : List Admin} (h : ParametricStep l l') (hl : l.getLast? = some a) :
    famOf a = .parametric := famShape_last (SingleThreaded.Det.ParametricStep.shape h) hl
theorem fam_numeric {l l' : List Admin} (h : NumericStep P l l') (hl : l.getLast? = some a) :
    famOf a = .numeric := famShape_last (SingleThreaded.Det.NumericStep.shape h) hl
theorem fam_vector {l l' : List Admin} (h : VectorStep P l l') (hl : l.getLast? = some a) :
    famOf a = .vector := famShape_last (SingleThreaded.Det.VectorStep.shape h) hl
theorem fam_variable {c c' : Config H} (h : VariableStep c c') (hl : c.code.getLast? = some a) :
    famOf a = .variable := by rcases c; exact famShape_last (SingleThreaded.Det.VariableStep.shape h) hl
theorem fam_table {c c' : Config H} (h : TableStep P c c') (hl : c.code.getLast? = some a) :
    famOf a = .table := by rcases c; exact famShape_last (SingleThreaded.Det.TableStep.shape h) hl
theorem fam_memory {c c' : Config H} (h : MemoryStep P c c') (hl : c.code.getLast? = some a) :
    famOf a = .memory := by rcases c; exact famShape_last (SingleThreaded.Det.MemoryStep.shape h) hl
theorem fam_reference {c c' : Config H} (h : RefStep c c') (hl : c.code.getLast? = some a) :
    famOf a = .reference := by rcases c; exact famShape_last (SingleThreaded.Det.RefStep.shape h) hl
theorem fam_aggregate {c c' : Config H} (h : AggregateStep c c') (hl : c.code.getLast? = some a) :
    famOf a = .aggregate := by rcases c; exact famShape_last (SingleThreaded.Det.AggregateStep.shape h) hl
end

/-- Closes the cases of a `Step` that cannot apply to a one-instruction code `[a]`
(`hc : c.code = [a]`), where `a` is a control instruction. -/
local macro "single_close" hc:ident : tactic => `(tactic| first
  | (exfalso; simp only [List.cons.injEq, List.ne_nil_of_mem, reduceCtorEq, and_false,
      List.append_eq_nil_iff, List.cons_ne_nil, false_and] at $hc:ident; done)
  | (exfalso; have hl := congrArg List.length $hc:ident
     simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hl
     omega)
  | (exfalso; have hl := congrArg List.getLast? $hc:ident; simp at hl; done)
  | (exfalso; exact split_single $hc:ident (by simp) ‹_›)
  | (exfalso; have hl := congrArg List.getLast? $hc:ident; simp at hl; subst hl
     simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]; done))


/-- Closes a family case of a `Step` from `[a]`, `a` a control instruction. -/
local macro "fam_close" hc:ident : tactic => `(tactic| first
  | (exfalso; have := fam_parametric ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_numeric ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_vector ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_variable ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_table ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_memory ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_reference ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done)
  | (exfalso; have := fam_aggregate ‹_› (by have hl := congrArg List.getLast? $hc:ident; simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons, Option.some_or, List.getLast?_cons] at hl; exact hl); simp [Det.famOf] at this; done))

theorem frame_inv {c c' : Config H} (h : Step P host c c') {n : Nat} {fi : Frame}
    {is : List Admin} (hc : c.code = [.frame n fi is]) :
    (∃ s' fi' is', Step P host ⟨c.store, fi, is⟩ ⟨s', fi', is'⟩ ∧
        c' = ⟨s', c.frame, [.frame n fi' is']⟩) ∨
      ∃ out, FrameExit c.store fi n is out ∧ c' = ⟨c.store, c.frame, out⟩ := by
  cases h with
  | ctxtInstrs hs hne => exact (ctxt_single hc hs.not_all_isVal hne).elim
  | ctxtFrame hs =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inl ⟨_, _, _, hs, rfl⟩
  | frameVals hn =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .vals hn, rfl⟩
  | returnFrame hn =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .ret hn, rfl⟩
  | trapFrame =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .trap, rfl⟩
  | throwRefFrame =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .throw _, rfl⟩
  | returnCallRefFrameNull hr =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .returnCallNull hr, rfl⟩
  | returnCallRefFrameAddr hr hf he hn =>
    simp only [List.cons.injEq, Admin.frame.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .returnCallAddr hr hf he hn, rfl⟩
  | _ =>
    try dsimp only at hc
    first | fam_close hc | single_close hc


/-- Closes every case that cannot apply to the one-instruction code `[a]` of `hc`. -/
local macro "inv_close" hc:ident : tactic => `(tactic| (
  try dsimp only at $hc:ident
  first
    | (exfalso; exact ctxt_single $hc:ident (Step.not_all_isVal ‹_›) ‹_›)
    | fam_close $hc
    | single_close $hc))

theorem trap_stuck {c c' : Config H} (h : Step P host c c') (hc : c.code = [.trap]) : False := by
  cases h <;> inv_close hc

theorem br_stuck {c c' : Config H} (h : Step P host c c') {l : LabelIdx}
    (hc : c.code = [.plain (.br l)]) : False := by
  cases h <;> inv_close hc

theorem return_stuck {c c' : Config H} (h : Step P host c c') (hc : c.code = [.plain .return_]) :
    False := by
  cases h <;> inv_close hc

theorem throwRef_stuck {c c' : Config H} (h : Step P host c c') (hc : c.code = [.plain .throwRef]) :
    False := by
  cases h <;> inv_close hc

theorem callRef_stuck {c c' : Config H} (h : Step P host c c') {r : Admin} (hr : r.IsCallRef)
    (hc : c.code = [r]) : False := by
  cases r with
  | plain i =>
    cases i <;> simp only [Admin.IsCallRef] at hr
    cases h <;> inv_close hc
  | callRefType d => cases h <;> inv_close hc
  | _ => simp only [Admin.IsCallRef] at hr

theorem unreachable_inv {c c' : Config H} (h : Step P host c c')
    (hc : c.code = [.plain .unreachable]) : c' = ⟨c.store, c.frame, [.trap]⟩ := by
  cases h with
  | parametric h' =>
    dsimp only at hc; subst hc
    generalize hl : [Admin.plain .unreachable] = l at h'
    cases h' <;> simp_all
  | _ => inv_close hc


theorem throwing_stuck {c c' : Config H} (h : Step P host c c') {a : Nat}
    (hc : c.code = throwing a) : False := by
  cases h with
  | @ctxtInstrs _ _ _ _ vs is _ rest hs hne =>
    dsimp only at hc
    obtain ⟨w, b, r, hb, rfl⟩ := Sim.exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs ++ w) ++ b :: (r ++ rest) =
        vals [Val.ref (.exn a)] ++ Admin.plain .throwRef :: [] := by
      simpa [throwing, vals, Val.toAdmin] using hc
    obtain ⟨h1, rfl, h3⟩ := Sim.vals_append_cons_inj hb rfl hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h3
    rcases List.append_eq_singleton_iff.1 h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp at hne
    · exact throwRef_stuck hs (by simp)
  | @trapInstrs _ _ vs rest _ =>
    dsimp only at hc
    have hc' : vals vs ++ Admin.trap :: rest =
        vals [Val.ref (.exn a)] ++ Admin.plain .throwRef :: [] := by
      simpa [throwing, vals, Val.toAdmin] using hc
    obtain ⟨-, h2, -⟩ := Sim.vals_append_cons_inj rfl rfl hc'
    cases h2
  | throwRefInstrs hne =>
    dsimp only at hc
    have hl := congrArg List.length hc
    simp only [throwing, List.length_append, vals_length, List.length_cons, List.length_nil] at hl
    rcases hne with h | h
    · exact h (List.eq_nil_of_length_eq_zero (by omega))
    · exact h (List.eq_nil_of_length_eq_zero (by omega))
  | _ =>
    try dsimp only at hc
    first
      | fam_close hc
      | (exfalso; simp [throwing] at hc; done)
      | (exfalso; have hl := congrArg List.length hc
         simp only [throwing, List.length_append, vals_length, List.length_cons, List.length_nil] at hl
         omega)
      | (exfalso; have hl := congrArg List.getLast? hc; simp [throwing] at hl; done)
      | (exfalso; have hl := congrArg List.getLast? hc; simp [throwing] at hl; subst hl
         simp_all [Admin.IsCallRef, Admin.IsReturnCallRef]; done)

theorem label_inv {c c' : Config H} (h : Step P host c c') {n : Nat} {cont : List Instr}
    {is : List Admin} (hc : c.code = [.label n cont is]) :
    (∃ s' f' is', Step P host ⟨c.store, c.frame, is⟩ ⟨s', f', is'⟩ ∧
        c' = ⟨s', f', [.label n cont is']⟩) ∨
      ∃ out, LabelExit n cont is out ∧ c' = ⟨c.store, c.frame, out⟩ := by
  cases h with
  | ctxtLabel hs =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inl ⟨_, _, _, hs, rfl⟩
  | labelVals =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .vals _, rfl⟩
  | brLabelZero hl hn =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .brZero hl hn, rfl⟩
  | brLabelSucc hl =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .brSucc hl, rfl⟩
  | returnLabel =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .ret, rfl⟩
  | returnCallRefLabel hr =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .returnCall hr, rfl⟩
  | throwRefLabel =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .throw _, rfl⟩
  | trapLabel =>
    simp only [List.cons.injEq, Admin.label.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .trap, rfl⟩
  | _ => inv_close hc

theorem handler_inv {c c' : Config H} (h : Step P host c c') {n : Nat} {cs : List Catch}
    {is : List Admin} (hc : c.code = [.handler n cs is]) :
    (∃ s' f' is', Step P host ⟨c.store, c.frame, is⟩ ⟨s', f', is'⟩ ∧
        c' = ⟨s', f', [.handler n cs is']⟩) ∨
      ∃ out, HandlerExit c.store c.frame n cs is out ∧ c' = ⟨c.store, c.frame, out⟩ := by
  cases h with
  | ctxtHandler hs =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inl ⟨_, _, _, hs, rfl⟩
  | handlerVals =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .vals _, rfl⟩
  | brHandler =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .br, rfl⟩
  | returnHandler =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .ret, rfl⟩
  | returnCallRefHandler hr =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .returnCall hr, rfl⟩
  | trapHandler =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .trap, rfl⟩
  | throwRefHandlerEmpty =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .throwEmpty _, rfl⟩
  | throwRefHandlerCatch he ht =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .catch_ he ht, rfl⟩
  | throwRefHandlerCatchRef he ht =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .catchRef he ht, rfl⟩
  | throwRefHandlerCatchAll =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .catchAll _, rfl⟩
  | throwRefHandlerCatchAllRef =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .catchAllRef _, rfl⟩
  | throwRefHandlerNext hn =>
    simp only [List.cons.injEq, Admin.handler.injEq, and_true] at hc
    obtain ⟨rfl, rfl, rfl⟩ := hc
    exact .inr ⟨_, .next hn, rfl⟩
  | _ => inv_close hc

/-- A one-instruction left-hand side `vals vs ++ [a]` has no values. -/
theorem vals_single {vs : List Val} {a b : Admin} (h : vals vs ++ [a] = [b]) : vs = [] ∧ a = b := by
  have hl := congrArg List.length h
  simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hl
  obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
  simpa using h

theorem block_inv {c c' : Config H} (h : Step P host c c') {bt : BlockType} {body : List Instr}
    (hc : c.code = [.plain (.block bt body)]) :
    ∃ t₂, c.frame.module.blockType? bt = some ([], t₂) ∧
      c' = ⟨c.store, c.frame, [.label t₂.length [] (expression body)]⟩ := by
  cases h with
  | block hbt hm =>
    obtain ⟨rfl, hc⟩ := vals_single hc
    simp only [Admin.plain.injEq, Instr.block.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain rfl : _ = [] := List.eq_nil_of_length_eq_zero hm.symm
    exact ⟨_, hbt, by simp [vals]⟩
  | _ => inv_close hc

theorem loop_inv {c c' : Config H} (h : Step P host c c') {bt : BlockType} {body : List Instr}
    (hc : c.code = [.plain (.loop bt body)]) :
    ∃ t₂, c.frame.module.blockType? bt = some ([], t₂) ∧
      c' = ⟨c.store, c.frame, [.label 0 [.loop bt body] (expression body)]⟩ := by
  cases h with
  | loop hbt hm =>
    obtain ⟨rfl, hc⟩ := vals_single hc
    simp only [Admin.plain.injEq, Instr.loop.injEq] at hc
    obtain ⟨rfl, rfl⟩ := hc
    obtain rfl : _ = [] := List.eq_nil_of_length_eq_zero hm.symm
    exact ⟨_, hbt, by simp [vals]⟩
  | _ => inv_close hc

theorem call_inv {c c' : Config H} (h : Step P host c c') {x : FuncIdx}
    (hc : c.code = [.plain (.call x)]) :
    ∃ a fi, c.frame.module.funcs[x.toNat]? = some a ∧ c.store.funcs[a]? = some fi ∧
      c' = ⟨c.store, c.frame, [.ref (.func a), .callRefType fi.type]⟩ := by
  cases h with
  | call hx hf =>
    simp only [List.cons.injEq, Admin.plain.injEq, Instr.call.injEq, and_true] at hc
    subst hc
    exact ⟨_, _, hx, hf, rfl⟩
  | _ => inv_close hc

/-- `vals vs ++ [x] ++ rest` is a single instruction only as `[x]`. -/
theorem mid_single {vs : List Val} {x y : Admin} {rest : List Admin}
    (h : vals vs ++ [x] ++ rest = [y]) : vs = [] ∧ rest = [] ∧ x = y := by
  have hl := congrArg List.length h
  simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hl
  obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
  obtain rfl : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
  simpa using h

theorem label_br_zero_inv {c c' : Config H} (h : Step P host c c') {n : Nat}
    {cont : List Instr} {l : LabelIdx} (hl : l.toNat = 0)
    (hc : c.code = [.label n cont [.plain (.br l)]]) :
    n = 0 ∧ c' = ⟨c.store, c.frame, expression cont⟩ := by
  rcases label_inv h hc with ⟨s', f', is', hs, -⟩ | ⟨out, hx, rfl⟩
  · exact (br_stuck hs rfl).elim
  · generalize hb : [Admin.plain (.br l)] = b at hx
    cases hx with
    | vals vs =>
      exact (SingleThreaded.Det.mem_vals (a := .plain (.br l)) (hb ▸ List.mem_singleton_self _)
        rfl).elim
    | @brZero vs' vs l' rest _ hn =>
      have hlen := congrArg List.length hb
      simp only [List.length_append, vals_length, List.length_cons, List.length_nil] at hlen
      obtain rfl : vs' = [] := List.eq_nil_of_length_eq_zero (by omega)
      obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
      exact ⟨hn.symm, by simp [vals]⟩
    | brSucc hl' =>
      obtain ⟨-, -, hx⟩ := mid_single hb.symm
      simp only [Admin.plain.injEq, Instr.br.injEq] at hx
      subst hx; omega
    | ret => simpa using (mid_single hb.symm).2.2
    | returnCall hr =>
      obtain ⟨-, -, rfl⟩ := mid_single hb.symm
      simp [Admin.IsReturnCallRef] at hr
    | throw => simp [throwing] at hb
    | trap => simp at hb

theorem isCallRef_control {r : Admin} (h : r.IsCallRef) : Det.famOf r = .control := by
  cases r with
  | plain i => cases i <;> simp_all [Admin.IsCallRef, Det.famOf]
  | _ => simp_all [Admin.IsCallRef, Det.famOf]

/-- Peel the last two instructions `x, r` off a code ending in a non-value `r`. -/
theorem last_two {vs ws : List Val} {v w : Val} {x y r r' : Admin} (hx : x.val? = some v) (hy : y.val? = some w)
    (hr : r.val? = none) (hr' : r'.val? = none)
    (h : vals vs ++ [x, r] = vals ws ++ [y, r']) : vs = ws ∧ x = y ∧ r = r' := by
  have h' : vals (vs ++ [v]) ++ r :: [] = vals (ws ++ [w]) ++ r' :: [] := by
    rw [Admin.eq_of_val? hx, Admin.eq_of_val? hy] at h; simpa [vals] using h
  obtain ⟨h1, rfl, -⟩ := Sim.vals_append_cons_inj hr hr' h'
  obtain ⟨rfl, h2⟩ := List.append_inj' h1 rfl
  obtain rfl := List.singleton_inj.1 h2
  exact ⟨rfl, (Admin.eq_of_val? hx).trans (Admin.eq_of_val? hy).symm, rfl⟩

theorem callRef_wasm_inv {c c' : Config H} (h : Step P host c c') :
    ∀ {vs : List Val} {a : Nat} {r : Admin} {fi : FuncInst H} {code : Func}, r.IsCallRef →
      c.store.funcs[a]? = some fi → fi.code = .wasm code →
      c.code = vals vs ++ [.ref (.func a), r] →
      ∃ vs₁ vs₂ ps rs, vs = vs₁ ++ vs₂ ∧ Expand fi.type (.func ps rs) ∧ vs₂.length = ps.length ∧
        c' = ⟨c.store, c.frame, vals vs₁ ++ [.frame rs.length (Frame.forCall fi.module vs₂ code.locals)
          [.label rs.length [] (expression code.body)]]⟩ := by
  induction h with
  | callRefFunc hr' hf' he hn hcode' =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    obtain rfl : _ = code := FuncCode.wasm.inj (hcode'.symm.trans hcode)
    exact ⟨[], _, _, _, rfl, he, hn, by simp [vals]⟩
  | callRefHost hr' hf' _ _ hcode' =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    cases hcode'.symm.trans hcode
  | callRefHostDiv hr' hf' _ _ hcode' =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨rfl, hx, rfl⟩ := last_two rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) hc
    simp only [Admin.ref.injEq, Ref.func.injEq] at hx
    subst hx
    obtain rfl : _ = fi := Option.some.inj (hf'.symm.trans hf)
    cases hcode'.symm.trans hcode
  | callRefNull hr' =>
    intro vs a r fi code hr hf hcode hc
    obtain ⟨-, hx, -⟩ := last_two (vs := []) rfl rfl (Admin.val?_of_isCallRef hr')
      (Admin.val?_of_isCallRef hr) (by simpa [vals] using hc)
    cases hx
  | @ctxtInstrs s s' f f' vs₀ is is' rest hs hne ih =>
    intro vs a r fi code hr hf hcode hc
    dsimp only at hc hf ⊢
    obtain ⟨w, b, t, hb, rfl⟩ := Sim.exists_head_of_not_all hs.not_all_isVal
    have hc' : vals (vs₀ ++ w) ++ b :: (t ++ rest) =
        vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨h1, rfl, h3⟩ := Sim.vals_append_cons_inj hb (Admin.val?_of_isCallRef hr) hc'
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 h3
    rcases List.eq_nil_or_concat w with rfl | ⟨w', x, rfl⟩
    · exact (callRef_stuck hs hr (by simp [vals])).elim
    · have h1' : (vs₀ ++ w') ++ [x] = vs ++ [Val.ref (.func a)] := by simpa using h1
      obtain ⟨hv, h2⟩ := List.append_inj' h1' rfl
      obtain rfl := List.singleton_inj.1 h2
      subst hv
      obtain ⟨vs₁, vs₂, ps, rs, rfl, he, hn, hc''⟩ :=
        ih (vs := w') hr hf hcode (by simp [vals, Val.toAdmin])
      refine ⟨vs₀ ++ vs₁, vs₂, ps, rs, by simp, he, hn, ?_⟩
      simp only [Config.mk.injEq] at hc'' ⊢
      obtain ⟨rfl, rfl, rfl⟩ := hc''
      simp
  | @trapInstrs s f vs₀ rest _ =>
    intro vs a r fi code hr hf hcode hc
    have hc' : vals vs₀ ++ Admin.trap :: rest = vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isCallRef hr) hc'
    simp [Admin.IsCallRef] at hr
  | @throwRefInstrs s f vs₀ x rest _ =>
    intro vs a r fi code hr hf hcode hc
    have hc' : vals (vs₀ ++ [.ref (.exn x)]) ++ Admin.plain .throwRef :: rest =
        vals (vs ++ [.ref (.func a)]) ++ r :: [] := by
      simpa [vals, Val.toAdmin, throwing] using hc
    obtain ⟨-, rfl, -⟩ := Sim.vals_append_cons_inj rfl (Admin.val?_of_isCallRef hr) hc'
    simp [Admin.IsCallRef] at hr
  | _ =>
    intro vs a r fi code hr hf hcode hc
    have hl := congrArg List.getLast? hc
    simp only [List.getLast?_append, List.getLast?_singleton, List.getLast?_cons_cons,
      Option.some_or, List.getLast?_cons] at hl
    have hk := isCallRef_control hr
    first
      | (exact absurd (fam_parametric ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_numeric ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_vector ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_variable ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_table ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_memory ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_reference ‹_› hl) (by simp [hk]))
      | (exact absurd (fam_aggregate ‹_› hl) (by simp [hk]))
      | (simp at hl; done)
      | (simp at hl; subst hl; simp [Admin.IsCallRef] at hr; done)
      | (simp at hl; subst hl; simp [Admin.IsCallRef, Det.famOf] at hk; done)

theorem call_inv_of {s : Store H} {f : Frame} {c : Config H} {x : FuncIdx} {a : Nat}
    {fi : FuncInst H} (hx : f.module.funcs[x.toNat]? = some a) (hf : s.funcs[a]? = some fi)
    (h : Step P host ⟨s, f, [.plain (.call x)]⟩ c) :
    c = ⟨s, f, [.ref (.func a), .callRefType fi.type]⟩ := by
  obtain ⟨a', fi', hx', hf', rfl⟩ := call_inv h rfl
  obtain rfl : a' = a := Option.some.inj (hx'.symm.trans hx)
  obtain rfl : fi' = fi := Option.some.inj (hf'.symm.trans hf)
  rfl

theorem callRef_wasm_inv_exact {s : Store H} {f : Frame} {c : Config H} {vs : List Val} {a : Nat}
    {r : Admin} {fi : FuncInst H} {code : Func} {ps rs : Ty (.list .val)} (hr : r.IsCallRef)
    (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm code) (he : Expand fi.type (.func ps rs))
    (hn : vs.length = ps.length) (h : Step P host ⟨s, f, vals vs ++ [.ref (.func a), r]⟩ c) :
    c = ⟨s, f, [.frame rs.length (Frame.forCall fi.module vs code.locals)
      [.label rs.length [] (expression code.body)]]⟩ := by
  obtain ⟨vs₁, vs₂, ps', rs', rfl, he', hn', rfl⟩ := callRef_wasm_inv h hr hf hcode rfl
  have := (Expand.iff.1 he).symm.trans (Expand.iff.1 he')
  simp only [Option.some.injEq, Ty.func.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  simp only [List.length_append] at hn
  obtain rfl : vs₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
  rfl

theorem loopBr0_inv {s : Store H} {f : Frame} {bt : BlockType} {c : Config H}
    (h : Step P host (loopBr0 s f bt) c) : c = labelBr0 s f bt := by
  obtain ⟨_, -, rfl⟩ := loop_inv h rfl
  rfl

theorem labelBr0_inv {s : Store H} {f : Frame} {bt : BlockType} {c : Config H}
    (h : Step P host (labelBr0 s f bt) c) : c = loopBr0 s f bt := by
  obtain ⟨-, rfl⟩ := label_br_zero_inv h rfl rfl
  rfl

theorem loopBr0_step {s : Store H} {f : Frame} {bt : BlockType} {t₂ : List CValType}
    (hbt : f.module.blockType? bt = some ([], t₂)) :
    Step P host (loopBr0 s f bt) (labelBr0 s f bt) := by
  have := Step.loop (P := P) (host := host) (s := s) (body := [.br ⟨0⟩]) (vs := []) hbt rfl
  simpa [vals, expression] using this

theorem labelBr0_step {s : Store H} {f : Frame} {bt : BlockType} :
    Step P host (labelBr0 s f bt) (loopBr0 s f bt) := by
  have := Step.brLabelZero (P := P) (host := host) (s := s) (f := f) (n := 0)
    (cont := [.loop bt [.br ⟨0⟩]]) (vs' := []) (vs := []) (l := ⟨0⟩) (rest := []) rfl rfl
  simpa [vals, expression] using this

theorem loopBr0_reach {s : Store H} {f : Frame} {bt : BlockType} {c : Config H}
    (h : Steps P host (loopBr0 s f bt) c) : c = loopBr0 s f bt ∨ c = labelBr0 s f bt := by
  induction h with
  | refl => exact .inl rfl
  | tail _ hs ih =>
    rcases ih with rfl | rfl
    · exact .inr (loopBr0_inv hs)
    · exact .inl (labelBr0_inv hs)

theorem loopBr0_diverges {s : Store H} {f : Frame} {bt : BlockType} {t₂ : List CValType}
    (hbt : f.module.blockType? bt = some ([], t₂)) : Diverges P host (loopBr0 s f bt) :=
  InfiniteTrace.coinduct (fun c => c = loopBr0 s f bt ∨ c = labelBr0 s f bt)
    (by
      rintro c (rfl | rfl)
      · exact ⟨_, loopBr0_step hbt, .inr rfl⟩
      · exact ⟨_, labelBr0_step, .inl rfl⟩)
    (.inl rfl)

theorem loopBr0_not_terminal {s : Store H} {f : Frame} {bt : BlockType} {c : Config H}
    (h : Steps P host (loopBr0 s f bt) c) : ¬ c.Terminal := by
  rintro ⟨r, hr⟩
  rcases loopBr0_reach h with rfl | rfl <;> rcases r with vs | a | _ <;>
    simp [Result.toAdmin, throwing] at hr <;>
    exact SingleThreaded.Det.mem_vals (hr ▸ List.mem_singleton_self _) rfl

end Silmaril.Wasm.Execution.Core.Proofs.Inversion
