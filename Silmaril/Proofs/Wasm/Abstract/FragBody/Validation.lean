module

public import Silmaril.Wasm.Binaryen.Typing
public import Silmaril.Wasm.SSA.Native.Defs

/-!
# Fragment trees and the principal typing of their lowering (step 1)

The route from Core validation of a fragment site to the fragment typing goes
through the principal typing of folded trees (`Binaryen.principal_tree`),
which applies to *saturated* trees with an *inferred* result
(`Binaryen.infer`). This file proves that fragment trees satisfy those side
conditions, constructor by constructor:

* leaves: `intConst`, `local.get` (`infer_intConst`, `infer_localGet`);
* operators applied to saturated operands whose inferred results match the
  operator's arity (`infer_op_of_args`);
* structured nodes (`infer_block`, `infer_loop`).

**Exception (counterexample to the naive statement).** `select` is a native
fragment operator, but `Binaryen.flatArity`/`flatResults` do not cover it (its
result type is not determined by the context alone), so a tree containing a
`select` is **not** `saturated` (`select_not_saturated`) and `principal_tree`
does not apply to it. Select trees need a separate inversion.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.FragBody

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Validation

theorem infer_intConst (C : Context) (t : IntType) (b : BitVec t.width) :
    infer C (.op (.intConst t b) []) = some (.vals [.num (.int t)]) ∧
      (BExpr.op (.intConst t b) []).saturated C = true := by
  simp [infer, inferList, botInstr, flatResults, BExpr.saturated, BExpr.saturatedList, flatArity]

theorem infer_localGet (C : Context) (x : LocalIdx) {lt : LocalType}
    (h : C.locals[x.toNat]? = some lt) :
    infer C (.op (.localGet x) []) = some (.vals [lt.type]) ∧
      (BExpr.op (.localGet x) []).saturated C = true := by
  simp [infer, inferList, botInstr, flatResults, BExpr.saturated, BExpr.saturatedList, flatArity, h]

/-- An operator over saturated operands whose inferred results it consumes
exactly is saturated, with the operator's results. -/
theorem infer_op_of_args (C : Context) {i : Instr} {args : List BExpr} {vs rs : List CValType}
    (ha : inferList C args = some (.vals vs)) (hs : BExpr.saturatedList C args = true)
    (hb : botInstr i = false) (har : flatArity C i = some vs.length)
    (hr : flatResults C i = some rs) :
    infer C (.op i args) = some (.vals rs) ∧ (BExpr.op i args).saturated C = true := by
  constructor
  · simp [infer, ha, hb, hr]
  · simp [BExpr.saturated, hs, hb, ha, har]

/-- A never-completing operator over saturated operands is saturated and bottom. -/
theorem infer_bot_of_args (C : Context) {i : Instr} {args : List BExpr} {vs : List CValType}
    (ha : inferList C args = some (.vals vs)) (hs : BExpr.saturatedList C args = true)
    (hb : botInstr i = true) :
    infer C (.op i args) = some .bot ∧ (BExpr.op i args).saturated C = true := by
  constructor
  · simp [infer, ha, hb]
  · simp [BExpr.saturated, hs, hb]

theorem infer_block (C : Context) {bt : BlockType} {body : List BExpr} {rs : List CValType}
    (hr : blockResults C bt = some rs) (hp : blockParams C bt = some 0) :
    infer C (.block bt body) = some (.vals rs) ∧ (BExpr.block bt body).saturated C = true := by
  simp [infer, hr, BExpr.saturated, hp]

theorem infer_loop (C : Context) {bt : BlockType} {body : List BExpr} {rs : List CValType}
    (hr : blockResults C bt = some rs) (hp : blockParams C bt = some 0) :
    infer C (.loop bt body) = some (.vals rs) ∧ (BExpr.loop bt body).saturated C = true := by
  simp [infer, hr, BExpr.saturated, hp]

/-- The fragment's block types (`ofBlockType?`) take no parameters and have
the expected results. -/
theorem blockType_frag (C : Context) {bt : BlockType} {ty : Option IntType}
    (h : SSA.ofBlockType? bt = some ty) :
    blockParams C bt = some 0 ∧ blockResults C bt = some ((SSA.resultTypes ty).map C.closeVal) := by
  cases bt with
  | empty => simp [SSA.ofBlockType?] at h; subst h; simp [blockParams, blockResults, SSA.resultTypes]
  | value t =>
    simp only [SSA.ofBlockType?, Option.map_eq_some_iff] at h
    obtain ⟨it, ht, rfl⟩ := h
    cases t with
    | num n =>
      cases n with
      | int it' =>
        simp [SSA.ofValType?] at ht; subst ht
        simp [blockParams, blockResults, SSA.resultTypes]
      | _ => simp [SSA.ofValType?] at ht
    | _ => simp [SSA.ofValType?] at ht
  | typeIdx x => simp [SSA.ofBlockType?] at h

/-- The concatenation of inferred operand results. -/
theorem inferList_cons_of (C : Context) {e : BExpr} {es : List BExpr} {ts us : List CValType}
    (he : infer C e = some (.vals ts)) (hes : inferList C es = some (.vals us)) :
    inferList C (e :: es) = some (.vals (ts ++ us)) := by
  simp [inferList, he, hes]

/-- **Counterexample.** A `select` tree is not saturated. -/
theorem select_not_saturated (C : Context) (a b c : BExpr)
    (ha : infer C a = some (.vals [.num (.int .i32)]))
    (hb : infer C b = some (.vals [.num (.int .i32)]))
    (hc : infer C c = some (.vals [.num (.int .i32)])) :
    (BExpr.op (.select none) [a, b, c]).saturated C = false := by
  simp [BExpr.saturated, inferList, ha, hb, hc, botInstr, flatArity]

/-- **Arity of recognised operators.** An instruction recognised by
`ofInstr?` as a native, non-`select` fragment operator (other than `br_if`,
whose arity depends on the label) either never completes, or has
`flatArity` equal to the number of its operand trees. -/
theorem ofInstr_arity (C : Context) {i : Instr} {es : List SSA.Expr} {e : SSA.Expr}
    (h : SSA.ofInstr? i es = some e)
    (hnat : ∀ o args, e = .op o args → o.native = true ∧ o ≠ .select)
    (hbr : ∀ l, i ≠ .brIf l) :
    botInstr i = true ∨ (botInstr i = false ∧ flatArity C i = some es.length) := by
  unfold SSA.ofInstr? at h
  split at h <;> simp_all [botInstr, flatArity]
  all_goals (subst h; first | exact absurd rfl (hnat _ _ rfl).2 | simp [SSA.Op.native] at hnat)

/-- **Results of recognised operators.** With the locals it reads present in the
context, a recognised native non-`select` operator other than `br_if` that
completes has inferable results. -/
theorem ofInstr_results (C : Context) {i : Instr} {es : List SSA.Expr} {e : SSA.Expr}
    (h : SSA.ofInstr? i es = some e)
    (hnat : ∀ o args, e = .op o args → o.native = true ∧ o ≠ .select)
    (hbr : ∀ l, i ≠ .brIf l)
    (hloc : ∀ x, (i = .localGet x ∨ i = .localTee x) → (C.locals[x.toNat]?).isSome) :
    botInstr i = true ∨ ∃ rs, flatResults C i = some rs := by
  unfold SSA.ofInstr? at h
  split at h <;> simp_all [botInstr, flatResults]
  all_goals (subst h; first | exact absurd rfl (hnat _ _ rfl).2 | simp [SSA.Op.native] at hnat)

/-! ## `br_if`, operand arities and `select`-freedom -/

open Silmaril.Wasm.SSA in
section
variable {L : List Ar} {R : Ar} {n : Nat} {r : Option (Option Ar)}

theorem ofInstr_brIf (C : Context) {l : LabelIdx} {es : List SSA.Expr} {ts : List CValType}
    (hl : C.labels[l.toNat]? = some ts) (hlen : ts.length + 1 = es.length) :
    botInstr (.brIf l) = false ∧ flatArity C (.brIf l) = some es.length ∧
      flatResults C (.brIf l) = some ts := by
  simp [botInstr, flatArity, flatResults, hl, hlen]

theorem tyE_op_args {o : Op} {args : List SSA.Expr} (h : tyE L R n (.op o args) = some r) :
    tyArgs L R n args = true := by
  rw [tyE] at h; by_contra hn; simp [hn] at h
theorem tyE_localSet {i : Nat} {e : SSA.Expr} (h : tyE L R n (.localSet i e) = some r) :
    tyE L R n e = some (some .one) := by
  rw [tyE] at h; by_contra hn; simp [hn] at h
theorem tyE_localTee {i : Nat} {e : SSA.Expr} (h : tyE L R n (.localTee i e) = some r) :
    tyE L R n e = some (some .one) := by
  rw [tyE] at h; by_contra hn; simp [hn] at h
theorem tyE_drop {e : SSA.Expr} (h : tyE L R n (.drop e) = some r) :
    tyE L R n e = some (some .one) := by
  rw [tyE] at h; by_contra hn; simp [hn] at h
theorem tyE_br {l : Nat} {args : List SSA.Expr} (h : tyE L R n (.br l args) = some r) :
    tyArgs L R n args = true := by
  rw [tyE] at h; by_contra hn; simp [hn] at h
theorem tyE_brIf {l : Nat} {args : List SSA.Expr} (h : tyE L R n (.brIf l args) = some r) :
    tyArgs L R n args = true := by
  rw [tyE] at h; by_contra hn; simp [hn] at h
theorem tyE_return {args : List SSA.Expr} (h : tyE L R n (.return_ args) = some r) :
    tyArgs L R n args = true := by
  rw [tyE] at h; by_contra hn; simp [hn] at h
theorem ofInstr_tyArgs {i : Instr} {es : List SSA.Expr} {e : SSA.Expr}
    (h : Silmaril.Wasm.SSA.ofInstr? i es = some e) (hty : tyE L R n e = some r) : tyArgs L R n es = true := by
  unfold Silmaril.Wasm.SSA.ofInstr? at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  all_goals first
    | exact tyE_op_args hty
    | exact tyE_br hty | exact tyE_brIf hty | exact tyE_return hty
    | simp [tyArgs, tyE_localSet hty] | simp [tyArgs, tyE_localTee hty] | simp [tyArgs, tyE_drop hty]
    | rfl

mutual
def noSel : SSA.Expr → Bool
  | .op o args => (o != .select) && noSelL args
  | .localSet _ e | .localTee _ e | .drop e => noSel e
  | .if_ _ c _ _ => noSel c
  | .br _ args | .brIf _ args | .return_ args => noSelL args
  | _ => true
def noSelL : List SSA.Expr → Bool
  | [] => true
  | e :: es => noSel e && noSelL es
end

def arLen : Ar → Nat
  | .none => 0
  | .one => 1

theorem ofInstr_noSel {i : Instr} {es : List SSA.Expr} {e : SSA.Expr}
    (h : Silmaril.Wasm.SSA.ofInstr? i es = some e) (hn : noSel e = true) :
    noSelL es = true ∧ ∀ o args, e = .op o args → o ≠ .select := by
  unfold Silmaril.Wasm.SSA.ofInstr? at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp_all [noSel, noSelL]


end

end Silmaril.Proofs.Wasm.Abstract.FragBody
