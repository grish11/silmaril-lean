module

public import Silmaril.Wasm.Binaryen.Typing
public import Silmaril.Wasm.SSA.Native.Defs
public import Silmaril.Proofs.Wasm.Abstract.FragBody.Typed

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
variable {L : List Ar} {R : Ar} {n : Nat} {r : Option Ar}

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


/-- A recognised tree whose native check is bottom has a bottom root (an
operand never is bottom: `tyArgs` requires arity one). -/
theorem ofInstr_bot_of_none {i : Instr} {es : List SSA.Expr} {e : SSA.Expr}
    (h : Silmaril.Wasm.SSA.ofInstr? i es = some e) (hty : tyE L R n e = some none) : botInstr i = true := by
  unfold Silmaril.Wasm.SSA.ofInstr? at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  all_goals first
    | rfl
    | (rw [tyE] at hty; simp at hty)

theorem ofInstr_none_of_bot {i : Instr} {es : List SSA.Expr} {e : SSA.Expr} {r : Option Ar}
    (h : Silmaril.Wasm.SSA.ofInstr? i es = some e) (hb : botInstr i = true) (hty : tyE L R n e = some r) :
    r = none := by
  unfold Silmaril.Wasm.SSA.ofInstr? at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  all_goals first
    | (simp [tyE] at hty; first | exact hty.symm | exact hty.2.symm)
    | (simp [botInstr] at hb)

theorem ofInstr_len (C : Context) {i : Instr} {es : List SSA.Expr} {e : SSA.Expr}
    {rs : List CValType} {a : Ar} (h : Silmaril.Wasm.SSA.ofInstr? i es = some e) (hbr : ∀ l, i ≠ .brIf l)
    (hr : flatResults C i = some rs) (hty : tyE L R n e = some (some a)) :
    rs.length = arLen a := by
  unfold Silmaril.Wasm.SSA.ofInstr? at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  all_goals (simp only [flatResults, Option.some.injEq, Option.map_eq_some_iff, reduceCtorEq] at hr)
  all_goals (simp [tyE] at hty)
  all_goals (try obtain ⟨_, _, hr⟩ := hr)
  all_goals (first | exact absurd rfl (hbr _) | (cases a <;> simp_all [arLen]))
  all_goals (subst hr; rfl)

/-! ## The saturation induction -/

theorem ofInstr_local {i : Instr} {es : List SSA.Expr} {e : SSA.Expr} {r : Option Ar} {x : LocalIdx}
    (h : Silmaril.Wasm.SSA.ofInstr? i es = some e) (hty : tyE L R n e = some r)
    (hx : i = .localGet x ∨ i = .localTee x) : x.toNat < n := by
  rcases hx with rfl | rfl
  · rcases es with _ | ⟨a, _ | _⟩ <;> simp [Silmaril.Wasm.SSA.ofInstr?] at h
    subst h; simp [tyE] at hty; exact hty.1
  · rcases es with _ | ⟨a, _ | _⟩ <;> simp [Silmaril.Wasm.SSA.ofInstr?] at h
    subst h; simp [tyE] at hty; exact hty.1.1

theorem ofInstr_brIf_shape {l : LabelIdx} {es : List SSA.Expr} {e : SSA.Expr}
    (h : Silmaril.Wasm.SSA.ofInstr? (.brIf l) es = some e) : e = .brIf l.toNat es := by
  unfold Silmaril.Wasm.SSA.ofInstr? at h
  split at h <;> simp_all

theorem tyE_brIf_some {l : Nat} {es : List SSA.Expr} {a : Ar}
    (h : tyE L R n (.brIf l es) = some (some a)) :
    L[l]? = some a ∧ (es.length = 1 ∨ es.length = 2) ∧ a = (if es.length = 2 then .one else .none) := by
  simp [tyE] at h
  obtain ⟨⟨⟨-, h1⟩, h2⟩, rfl⟩ := h
  exact ⟨h2, h1, rfl⟩

variable (C : Context)
  (hloc : ∀ x : LocalIdx, x.toNat < n → (C.locals[x.toNat]?).isSome)
  (hlab : ∀ (l : LabelIdx) a, L[l.toNat]? = some a → ∃ ts, C.labels[l.toNat]? = some ts ∧ ts.length = arLen a)

theorem resultTypes_len (ty : Option IntType) : ((Silmaril.Wasm.SSA.resultTypes ty).map C.closeVal).length = arLen (arOf ty) := by
  cases ty <;> rfl

set_option linter.unusedSectionVars false in
include hloc hlab in
mutual
/-- **Step 1.** A recognised, native-arity-checked, `select`-free tree is saturated, and
`infer` gives its native arity (results of that length, or bottom). -/
theorem sat_tree : ∀ (b : BExpr) (e : SSA.Expr) (r : Option Ar), Silmaril.Wasm.SSA.ofBExpr? b = some e →
    noSel e = true → tyE L R n e = some r →
    BExpr.saturated C b = true ∧ (∀ a, r = some a → ∃ ts, infer C b = some (.vals ts) ∧ ts.length = arLen a) ∧
      (r = none → infer C b = some .bot)
  | .op i args, e, r, h, hn, hty => by
    cases hes : Silmaril.Wasm.SSA.ofBExprs? args with
    | none => simp [Silmaril.Wasm.SSA.ofBExpr?, hes] at h
    | some es =>
      simp only [Silmaril.Wasm.SSA.ofBExpr?, hes] at h
      have hta := ofInstr_tyArgs h hty
      obtain ⟨hnl, hns⟩ := ofInstr_noSel h hn
      obtain ⟨hsl, ts, hts, htl⟩ := sat_list args es hes hnl hta
      by_cases hb : botInstr i = true
      · have hr := ofInstr_none_of_bot h hb hty
        subst hr
        obtain ⟨h1, h2⟩ := infer_bot_of_args C hts hsl hb
        exact ⟨h2, fun a ha => absurd ha (by simp), fun _ => h1⟩
      · have hb' : botInstr i = false := by simpa using hb
        cases r with
        | none => exact absurd (ofInstr_bot_of_none h hty) hb
        | some a =>
          by_cases hbr : ∃ l, i = .brIf l
          · obtain ⟨l, rfl⟩ := hbr
            have he := ofInstr_brIf_shape h
            subst he
            obtain ⟨hL, hlen, rfl⟩ := tyE_brIf_some hty
            obtain ⟨ls, hls, hll⟩ := hlab l _ hL
            obtain ⟨-, har, hres⟩ := ofInstr_brIf C (es := es) hls (by
              rcases hlen with h1 | h1 <;> simp [hll, h1, arLen])
            obtain ⟨h1, h2⟩ := infer_op_of_args C hts hsl hb' (by rw [har, htl]) hres
            exact ⟨h2, fun a' ha => ⟨ls, h1, by cases ha; exact hll⟩, fun ha => absurd ha (by simp)⟩
          · push Not at hbr
            have hnat : ∀ o args', e = .op o args' → o.native = true ∧ o ≠ .select := by
              intro o args' he
              refine ⟨?_, hns o args' he⟩
              subst he
              simp [tyE] at hty
              exact hty.1.1.1
            rcases ofInstr_arity C h hnat hbr with hb2 | ⟨-, har⟩
            · exact absurd hb2 hb
            rcases ofInstr_results C h hnat hbr (fun x hx => hloc x (ofInstr_local h hty hx)) with
              hb2 | ⟨rs, hrs⟩
            · exact absurd hb2 hb
            obtain ⟨h1, h2⟩ := infer_op_of_args C hts hsl hb' (by rw [har, htl]) hrs
            exact ⟨h2, fun a' ha => ⟨rs, h1, by cases ha; exact ofInstr_len C h hbr hrs hty⟩,
              fun ha => absurd ha (by simp)⟩
  | .block bt body, e, r, h, hn, hty => by
    cases hty' : Silmaril.Wasm.SSA.ofBlockType? bt with
    | none => simp [Silmaril.Wasm.SSA.ofBExpr?, hty'] at h
    | some ty =>
    cases hb : Silmaril.Wasm.SSA.ofBExprs? body with
    | none => simp [Silmaril.Wasm.SSA.ofBExpr?, hty', hb] at h
    | some body' =>
    simp [Silmaril.Wasm.SSA.ofBExpr?, hty', hb] at h
    subst h
    obtain ⟨hp, hr⟩ := blockType_frag C hty'
    obtain ⟨h1, h2⟩ := infer_block C (body := body) hr hp
    refine ⟨h2, fun a ha => ⟨_, h1, ?_⟩, fun ha => ?_⟩
    · rw [resultTypes_len]; subst ha; simp [tyE] at hty; rw [hty.2]
    · subst ha; simp [tyE] at hty
  | .loop bt body, e, r, h, hn, hty => by
    cases hty' : Silmaril.Wasm.SSA.ofBlockType? bt with
    | none => simp [Silmaril.Wasm.SSA.ofBExpr?, hty'] at h
    | some ty =>
    cases hb : Silmaril.Wasm.SSA.ofBExprs? body with
    | none => simp [Silmaril.Wasm.SSA.ofBExpr?, hty', hb] at h
    | some body' =>
    simp [Silmaril.Wasm.SSA.ofBExpr?, hty', hb] at h
    subst h
    obtain ⟨hp, hr⟩ := blockType_frag C hty'
    obtain ⟨h1, h2⟩ := infer_loop C (body := body) hr hp
    refine ⟨h2, fun a ha => ⟨_, h1, ?_⟩, fun ha => ?_⟩
    · rw [resultTypes_len]; subst ha; simp [tyE] at hty; rw [hty.2]
    · subst ha; simp [tyE] at hty
  | .if_ bt cond t el, e, r, h, hn, hty => by
    rcases cond with _ | ⟨c, _ | ⟨c₂, cs⟩⟩
    · simp [Silmaril.Wasm.SSA.ofBExpr?] at h
    swap
    · simp [Silmaril.Wasm.SSA.ofBExpr?] at h
    cases hty' : Silmaril.Wasm.SSA.ofBlockType? bt with
    | none => simp [Silmaril.Wasm.SSA.ofBExpr?, hty'] at h
    | some ty =>
    cases hc : Silmaril.Wasm.SSA.ofBExpr? c with
    | none => simp [Silmaril.Wasm.SSA.ofBExpr?, hty', hc] at h
    | some c' =>
    cases ht : Silmaril.Wasm.SSA.ofBExprs? t with
    | none => simp [Silmaril.Wasm.SSA.ofBExpr?, hty', hc, ht] at h
    | some t' =>
    cases he : Silmaril.Wasm.SSA.ofBExprs? el with
    | none => simp [Silmaril.Wasm.SSA.ofBExpr?, hty', hc, ht, he] at h
    | some e' =>
    simp [Silmaril.Wasm.SSA.ofBExpr?, hty', hc, ht, he] at h
    subst h
    simp only [noSel] at hn
    have hty₂ := hty
    simp [tyE] at hty₂
    obtain ⟨⟨⟨hcty, -⟩, -⟩, rfl⟩ := hty₂
    obtain ⟨hs, hv, -⟩ := sat_tree c c' _ hc hn hcty
    obtain ⟨ts, hts, hlt⟩ := hv _ rfl
    obtain ⟨hp, hr⟩ := blockType_frag C hty'
    have hil : inferList C [c] = some (.vals ts) := by simpa using inferList_cons_of C hts (es := []) rfl
    refine ⟨?_, fun a ha => ⟨(Silmaril.Wasm.SSA.resultTypes ty).map C.closeVal, ?_, ?_⟩, fun ha => absurd ha (by simp)⟩
    · simp [BExpr.saturated, BExpr.saturatedList, hs, hil, hp, hlt, arLen]
    · simp [infer, hil, hr]
    · cases ha; exact resultTypes_len C ty
  | .tryTable .., e, r, h, hn, hty => by simp [Silmaril.Wasm.SSA.ofBExpr?] at h
theorem sat_list : ∀ (bs : List BExpr) (es : List SSA.Expr), Silmaril.Wasm.SSA.ofBExprs? bs = some es →
    noSelL es = true → tyArgs L R n es = true →
    BExpr.saturatedList C bs = true ∧ ∃ ts, inferList C bs = some (.vals ts) ∧ ts.length = es.length
  | [], es, h, _, _ => by simp [Silmaril.Wasm.SSA.ofBExprs?] at h; subst h; simp [BExpr.saturatedList, inferList]
  | b :: bs, es, h, hn, ht => by
    cases hb : Silmaril.Wasm.SSA.ofBExpr? b with
    | none => simp [Silmaril.Wasm.SSA.ofBExprs?, hb] at h
    | some e =>
    cases hbs : Silmaril.Wasm.SSA.ofBExprs? bs with
    | none => simp [Silmaril.Wasm.SSA.ofBExprs?, hb, hbs] at h
    | some es' =>
    simp [Silmaril.Wasm.SSA.ofBExprs?, hb, hbs] at h
    subst h
    simp only [noSelL, Bool.and_eq_true] at hn
    simp only [tyArgs, Bool.and_eq_true, beq_iff_eq] at ht
    obtain ⟨hs₁, hv₁, -⟩ := sat_tree b e _ hb hn.1 ht.1
    obtain ⟨ts, hts, hlt⟩ := hv₁ _ rfl
    obtain ⟨hs₂, us, hus, hlu⟩ := sat_list bs es' hbs hn.2 ht.2
    refine ⟨by simp [BExpr.saturatedList, hs₁, hs₂], ts ++ us, inferList_cons_of C hts hus, ?_⟩
    simp [hlt, hlu, arLen]; omega
end

end

/-! ## Step 2: inverting Core validation -/

theorem Sub.num_up {Δ : TypeCtx} {n : NumType} {b : CValType} (h : Sub Δ (.num n) b) :
    b = .num n := by
  cases h; rfl

theorem resultSub_nums {Δ : TypeCtx} :
    ∀ {vs ws : List CValType}, ResultSub Δ vs ws → (∀ v ∈ vs, ∃ n, v = .num n) → ws = vs
  | [], [], _, _ => rfl
  | v :: vs, w :: ws, h, hv => by
    simp only [ResultSub, List.forall₂_cons] at h
    obtain ⟨n, rfl⟩ := hv v (by simp)
    rw [Sub.num_up h.1, resultSub_nums h.2 fun v hv' => hv v (by simp [hv'])]
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h

/-- **Operands against the operator.** If operands with numeric principal results
`vs` are followed by an instruction, every typing of the whole sequence types the
instruction with parameters exactly `vs` (when it takes that many). -/
theorem operands_params {D : Context} (hD : D.Wf) {args : List Instr} {i : Instr}
    {vs ps rs : List CValType} {xs : List Nat}
    (hp : Principal D args vs) (hvs : ∀ v ∈ vs, ∃ n, v = .num n)
    (h : InstrsOk D (args ++ [i]) ⟨ps, xs, rs⟩) :
    ∃ ya it₀, InstrOk (D.initLocals ya) i it₀ ∧
      (it₀.params.length = vs.length → it₀.params = vs) := by
  obtain ⟨m, ya, yb, ha, hb, -⟩ := InstrsOk.split hD h rfl
  obtain ⟨s1, -⟩ := hp ps ya m ha
  obtain ⟨ts, it₀, hi, hsub⟩ := InstrsOk.single_inv (hD.initLocals ya) hb
  refine ⟨ya, it₀, hi, fun hlen => ?_⟩
  have s2 : ResultSub _ m (ts ++ it₀.params) := hsub.1
  have hm := List.Forall₂.length_eq s1
  have hm2 := List.Forall₂.length_eq s2
  simp only [List.length_append] at hm hm2
  have e1 := List.take_append_drop ps.length m
  rw [← e1] at s1 s2
  have hl1 : (m.take ps.length).length = ps.length := by simp; omega
  have hl2 : (m.drop ps.length).length = vs.length := by simp; omega
  obtain ⟨-, s1b⟩ := Silmaril.Wasm.Binaryen.resultSub_append_split (by rw [hl2]) s1
  have : (m.take ps.length).length = ts.length := by omega
  obtain ⟨-, s2b⟩ := Silmaril.Wasm.Binaryen.resultSub_append_split (by omega) s2
  have h1 := resultSub_nums s1b hvs
  rw [h1] at s2b
  exact resultSub_nums s2b hvs

/-! ## Per-instruction typing inversions -/

theorem instrOk_intUnOp_inv {D : Context} {t : IntType} {op : IntUnOp} {it : InstrType}
    (h : InstrOk D (.intUnOp t op) it) : it = .plain [.num (.int t)] [.num (.int t)] := by
  cases h
  all_goals (rename_i h; cases h)
  rfl

theorem instrOk_intTestOp_inv {D : Context} {t : IntType} {op : IntTestOp} {it : InstrType}
    (h : InstrOk D (.intTestOp t op) it) : it = .plain [.num (.int t)] [.num (.int .i32)] := by
  cases h
  all_goals (rename_i h; cases h)
  rfl

theorem instrOk_intBinOp_inv {D : Context} {t : IntType} {op : IntBinOp} {it : InstrType}
    (h : InstrOk D (.intBinOp t op) it) :
    it = .plain [.num (.int t), .num (.int t)] [.num (.int t)] := by
  cases h
  all_goals (rename_i h; cases h)
  rfl

theorem instrOk_intRelOp_inv {D : Context} {t : IntType} {op : IntRelOp} {it : InstrType}
    (h : InstrOk D (.intRelOp t op) it) :
    it = .plain [.num (.int t), .num (.int t)] [.num (.int .i32)] := by
  cases h
  all_goals (rename_i h; cases h)
  rfl

theorem instrOk_select_inv {D : Context} {it : InstrType} (h : InstrOk D (.select none) it) :
    ∃ t, it = .plain [t, t, .num (.int .i32)] [t] := by
  cases h
  all_goals (rename_i h; cases h)
  exact ⟨_, rfl⟩

theorem instrOk_selectT_inv {D : Context} {vt : ValType} {it : InstrType}
    (h : InstrOk D (.select (some [vt])) it) :
    ∃ t, it = .plain [t, t, .num (.int .i32)] [t] := by
  cases h
  all_goals (rename_i h; cases h)
  exact ⟨_, rfl⟩

/-! ## Operator signatures from validation -/

open Silmaril.Wasm.Abstract.FragBody in
section

/-- An integer type as a Core value type. -/
abbrev numInt (t : IntType) : CValType := .num (.int t)

theorem opSig_of_instr {i : Instr} {es args : List Silmaril.Wasm.SSA.Expr} {o : Silmaril.Wasm.SSA.Op} {D : Context}
    {it₀ : InstrType} {τs : List IntType}
    (h : Silmaril.Wasm.SSA.ofInstr? i es = some (.op o args)) (hi : InstrOk D i it₀)
    (hp : it₀.params = τs.map numInt) (hnat : o.native = true) :
    ∃ t, OpSig o τs t ∧ it₀.results = [numInt t] := by
  unfold Silmaril.Wasm.SSA.ofInstr? at h
  split at h <;> (try split at h) <;> simp only [Option.some.injEq, reduceCtorEq, Silmaril.Wasm.SSA.Expr.op.injEq] at h
  all_goals (obtain ⟨rfl, rfl⟩ := h)
  all_goals first
    | (rw [instrOk_intConst_inv hi] at hp ⊢
       obtain rfl : τs = [] := by simpa using hp.symm
       exact ⟨_, ofInt_type _ _ ▸ OpSig.const _, by simp⟩)
    | (rw [instrOk_intUnOp_inv hi] at hp ⊢
       obtain ⟨t', rfl⟩ : ∃ t', τs = [t'] := by
         rcases τs with _ | ⟨a, _ | _⟩ <;> simp at hp; exact ⟨a, rfl⟩
       simp at hp; subst hp; exact ⟨_, .unInt _ _, rfl⟩)
    | (rw [instrOk_intTestOp_inv hi] at hp ⊢
       obtain ⟨t', rfl⟩ : ∃ t', τs = [t'] := by
         rcases τs with _ | ⟨a, _ | _⟩ <;> simp at hp; exact ⟨a, rfl⟩
       simp at hp; subst hp; exact ⟨_, .test _, rfl⟩)
    | (rw [instrOk_intBinOp_inv hi] at hp ⊢
       rcases τs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hp
       obtain ⟨rfl, rfl⟩ := hp; exact ⟨_, .binInt _ _, rfl⟩)
    | (rw [instrOk_intRelOp_inv hi] at hp ⊢
       rcases τs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp at hp
       obtain ⟨rfl, rfl⟩ := hp; exact ⟨_, .rel _ _, rfl⟩)
    | (obtain ⟨t, ht⟩ := instrOk_select_inv hi
       rw [ht] at hp ⊢
       rcases τs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> simp at hp
       obtain ⟨rfl, h2, h3⟩ := hp
       simp at h2 h3; subst h2; subst h3; exact ⟨_, .select _, rfl⟩)
    | (obtain ⟨t, ht⟩ := instrOk_selectT_inv hi
       rw [ht] at hp ⊢
       rcases τs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | _⟩⟩⟩ <;> simp at hp
       obtain ⟨rfl, h2, h3⟩ := hp
       simp at h2 h3; subst h2; subst h3; exact ⟨_, .select _, rfl⟩)
    | (simp [Silmaril.Wasm.SSA.Op.native] at hnat)

end

/-! ## Operator nodes from validation -/

open Silmaril.Wasm.Abstract.FragBody in
section

/-- **An operator node, inverted.** Operands typed at `τs` with principal results
`τs.map numInt`, followed by a native recognised operator, in a valid sequence:
the operator node is typed, at the operator's result. -/
theorem ty_op_node {D : Context} (hD : D.Wf) {Γ : List IntType} {ρ : Option IntType}
    {Λ : List (Option IntType)} {i : Instr} {args : List BExpr} {es : List Silmaril.Wasm.SSA.Expr}
    {o : Silmaril.Wasm.SSA.Op} {τs : List IntType} {ps rs : List CValType} {xs : List Nat}
    (hofi : Silmaril.Wasm.SSA.ofInstr? i es = some (.op o es)) (hnat : o.native = true)
    (hargs : ArgsTy Γ ρ Λ es τs) (hp : Principal D (BExpr.lowerList args) (τs.map numInt))
    (hlen : τs.length = es.length)
    (har : ∀ D' it₀, InstrOk D' i it₀ → it₀.params.length = es.length)
    (h : InstrsOk D (BExpr.lowerList args ++ [i]) ⟨ps, xs, rs⟩) :
    ∃ t, Ty Γ ρ Λ (.op o es) (some t) := by
  obtain ⟨ya, it₀, hi, hpar⟩ := operands_params hD hp (fun v hv => by
    simp only [List.mem_map] at hv; obtain ⟨t, -, rfl⟩ := hv; exact ⟨_, rfl⟩) h
  have hpe := hpar (by rw [har _ _ hi, List.length_map, hlen])
  obtain ⟨t, hs, -⟩ := opSig_of_instr hofi hi hpe hnat
  exact ⟨t, .op hs hargs⟩

theorem ofInstr_params_len {i : Instr} {es : List Silmaril.Wasm.SSA.Expr} {o : Silmaril.Wasm.SSA.Op} {args : List Silmaril.Wasm.SSA.Expr}
    (hofi : Silmaril.Wasm.SSA.ofInstr? i es = some (.op o args)) (hnat : o.native = true) :
    ∀ D' it₀, InstrOk D' i it₀ → it₀.params.length = es.length := by
  intro D' it₀ hi
  unfold Silmaril.Wasm.SSA.ofInstr? at hofi
  split at hofi <;> (try split at hofi) <;>
    simp only [Option.some.injEq, reduceCtorEq, Silmaril.Wasm.SSA.Expr.op.injEq] at hofi
  all_goals (obtain ⟨rfl, rfl⟩ := hofi)
  all_goals first
    | (rw [instrOk_intConst_inv hi]; rfl)
    | (rw [instrOk_intUnOp_inv hi]; rfl)
    | (rw [instrOk_intTestOp_inv hi]; rfl)
    | (rw [instrOk_intBinOp_inv hi]; rfl)
    | (rw [instrOk_intRelOp_inv hi]; rfl)
    | (obtain ⟨t, ht⟩ := instrOk_select_inv hi; rw [ht]; rfl)
    | (obtain ⟨t, ht⟩ := instrOk_selectT_inv hi; rw [ht]; rfl)
    | (simp [Silmaril.Wasm.SSA.Op.native] at hnat)

end

/-! ## Structured instructions: inversions exposing the body -/

theorem instrOk_block_body {D : Context} {bt : BlockType} {b : List Instr} {it : InstrType}
    (h : InstrOk D (.block bt b) it) :
    ∃ t₁ t₂ xs, BlockTypeOk D bt t₁ t₂ ∧ InstrsOk (D.withLabel t₂) b ⟨t₁, xs, t₂⟩ ∧
      it = .plain t₁ t₂ := by
  cases h
  all_goals first | exact ⟨_, _, _, by assumption, by assumption, rfl⟩ | (rename_i h; cases h)

theorem instrOk_loop_body {D : Context} {bt : BlockType} {b : List Instr} {it : InstrType}
    (h : InstrOk D (.loop bt b) it) :
    ∃ t₁ t₂ xs, BlockTypeOk D bt t₁ t₂ ∧ InstrsOk (D.withLabel t₁) b ⟨t₁, xs, t₂⟩ ∧
      it = .plain t₁ t₂ := by
  cases h
  all_goals first | exact ⟨_, _, _, by assumption, by assumption, rfl⟩ | (rename_i h; cases h)

theorem instrOk_if_body {D : Context} {bt : BlockType} {b₁ b₂ : List Instr} {it : InstrType}
    (h : InstrOk D (.if_ bt b₁ b₂) it) :
    ∃ t₁ t₂ xs₁ xs₂, BlockTypeOk D bt t₁ t₂ ∧ InstrsOk (D.withLabel t₂) b₁ ⟨t₁, xs₁, t₂⟩ ∧
      InstrsOk (D.withLabel t₂) b₂ ⟨t₁, xs₂, t₂⟩ ∧ it = .plain (t₁ ++ [.i32]) t₂ := by
  cases h
  all_goals first
    | exact ⟨_, _, _, _, by assumption, by assumption, by assumption, rfl⟩
    | (rename_i h; cases h)

/-! ## Context fit -/

/-- `D` fits the fragment typing context: local, label and return types are the
numeric images of `Γ`, `Λ`, `ρ`. -/
structure Fit (D : Context) (Γ : List IntType) (ρ : Option IntType) (Λ : List (Option IntType)) :
    Prop where
  loc : ∀ x : Nat, (D.locals[x]?).map LocalType.type = (Γ[x]?).map numInt
  lab : D.labels = Λ.map fun lt => lt.toList.map numInt
  ret : D.return_ = some (ρ.toList.map numInt)

theorem Fit.initLocals {D : Context} {Γ ρ Λ} (h : Fit D Γ ρ Λ) (ys : List Nat) :
    Fit (D.initLocals ys) Γ ρ Λ :=
  ⟨fun x => (initLocals_localType D ys x).trans (h.loc x), by simp [h.lab], by simp [h.ret]⟩

theorem Fit.withLabel {D : Context} {Γ ρ Λ} (h : Fit D Γ ρ Λ) (lt : Option IntType) :
    Fit (D.withLabel (lt.toList.map numInt)) Γ ρ (lt :: Λ) :=
  ⟨h.loc, by simp [Context.withLabel, h.lab], h.ret⟩

theorem Fit.local_type {D : Context} {Γ ρ Λ} (h : Fit D Γ ρ Λ) {x : Nat} {lt : LocalType}
    (hx : D.locals[x]? = some lt) : ∃ t, Γ[x]? = some t ∧ lt.type = numInt t := by
  have := h.loc x
  rw [hx] at this
  rcases hg : Γ[x]? with _ | t
  · rw [hg] at this; cases this
  · rw [hg] at this; exact ⟨t, rfl, Option.some.inj this⟩

theorem Fit.label {D : Context} {Γ ρ Λ} (h : Fit D Γ ρ Λ) {l : Nat} {ts : List CValType}
    (hl : D.labels[l]? = some ts) : ∃ lt, Λ[l]? = some lt ∧ ts = lt.toList.map numInt := by
  rw [h.lab, List.getElem?_map] at hl
  rcases hg : Λ[l]? with _ | lt
  · rw [hg] at hl; cases hl
  · rw [hg] at hl; exact ⟨lt, rfl, (Option.some.inj hl).symm⟩

end Silmaril.Proofs.Wasm.Abstract.FragBody
