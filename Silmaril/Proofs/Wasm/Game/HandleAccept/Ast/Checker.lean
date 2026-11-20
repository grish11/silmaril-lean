module

public import Silmaril.Wasm.Game.HandleAccept.Ast.Checkers.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Generic

/-!
# `addCheck` meets its specification

`addCheck_sat`: in every environment `ρ` and every profile, the instance of `addCheck` meets
the AST reader specification `astISpec arithRIx ρ addL` with the store invariant `StoreInv`.
The body is straight-line: what each allowed answer says (`tag_post`, `count_post`,
`child_post`) is collected along the way, and tagged nodes determine their tag and children
(`ofList_inj2`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Ast.Checker

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Ast Silmaril.Wasm.Game.HandleAccept.Ast.Checkers
  Silmaril.Wasm.Game.HandleAccept.Ast.Examples
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- A tagged node determines its tag and its children. -/
theorem ofList_inj2 {τ α : Type} {v v' : τ} {cs cs' : List (TExpr τ α)}
    (h : TExpr.ofList v cs = TExpr.ofList v' cs') : v = v' ∧ cs = cs' := by
  have hn := Sum.inr.inj (congrArg TExpr.node h)
  exact ⟨by simpa [TExpr.ofList, TExpr.node] using congrArg TNode.tag hn,
    by simpa [TExpr.ofList, TExpr.node] using congrArg TNode.children hn⟩

/-- `[i32] → [i32, i64]`. -/
abbrev tFT : FnType := ⟨[.num (.int .i32)], [.num (.int .i32), .num (.int .i64)]⟩
/-- `[i32 i32] → [i32]`. -/
abbrev cFT : FnType := ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩

/-- The import types of `addCheck`. -/
abbrev astFTs : List FnType := [tFT, qFT, cFT, aFT]

/-- The shape of the instantiated `addCheck`. -/
theorem add_shape : GShape (Verify.instOf addCheck) astFTs aFT [.i32] addBody [some (.i32 0)] :=
  GShape.of_ok (by decide +kernel)

/-! ## Allowed answers -/

section Posts

variable {I : ScalarInstance} (hI : I.imports = astFTs)
  {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST arithSig.toAstSig)}
  {L : Set (AST arithSig.toAstSig)}

include hI

/-- Only `accept` has a precondition. -/
theorem pre_of_ne {k : Nat} (hk : k < 4) (h3 : k ≠ 3) {args : List Val}
    (ht : List.Forall₂ ScalarType.HasVal (astFTs[k]'hk).params args) :
    ∃ e, I.importOp? k args = some e ∧ (astISpec (ts := I.imports) arithRIx ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_existsG hI hk ht
  refine ⟨e, he, fun h hd => ?_⟩
  have h1 := (importOp?_eq he).1
  simp [astDecAsk, arithRIx, h1, h3] at hd

/-- `accept(a)` is allowed when `a` denotes a member of `L`. -/
theorem pre_accept (a : BitVec 32) (hL : ∀ t, ρ a = some t → t ∈ L) :
    ∃ e, I.importOp? 3 [.i32 a] = some e ∧ (astISpec (ts := I.imports) arithRIx ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_existsG hI (k := 3) (by decide) (args := [.i32 a])
    (.cons ⟨a, rfl⟩ .nil)
  refine ⟨e, he, fun h hd => ?_⟩
  obtain ⟨h1, h2⟩ := importOp?_eq he
  simp [astDecAsk, arithRIx, h1, h2, i32Arg, Val.i32] at hd
  obtain rfl := hd
  exact hL

variable {e : I.E.Op} {v : I.E.Ar e} {a : BitVec 32} {res : List Val}

/-- An allowed answer of `tag(a)`: a code and a word; a decoded tag and payload is the node's. -/
theorem tag_post (he : I.importOp? 0 [.i32 a] = some e)
    (hv : (astISpec (ts := I.imports) arithRIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c w, res = [.i32 c, .i64 w] ∧ ∀ p, decTag arithRIx [.i32 c, .i64 w] = some p →
      ∃ cs, ρ a = some (TExpr.ofList p cs) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨c, w, rfl⟩ : ∃ c w, res = [.i32 c, .i64 w] := by
    rcases hty with _ | ⟨⟨c, rfl⟩, _ | ⟨⟨w, rfl⟩, hnil⟩⟩
    cases hnil
    exact ⟨c, w, rfl⟩
  refine ⟨c, w, rfl, fun p hp => ?_⟩
  have hd : astDecAns arithRIx e v = some (.read (.tag a) (.tag p)) := by
    unfold astDecAns astDecRead
    rw [hans]
    simp only [arithRIx, h1, h2, i32Arg, Val.i32] at hp ⊢
    simp [hp]
  exact (hv _ _ hd).2

/-- An allowed answer of `count(a)`. -/
theorem count_post (he : I.importOp? 1 [.i32 a] = some e)
    (hv : (astISpec (ts := I.imports) arithRIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ n, res = [.i32 n] ∧ ∃ p cs, ρ a = some (TExpr.ofList p cs) ∧ cs.length = n.toNat := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨n, rfl⟩ := res_i32 hty
  refine ⟨n, rfl, ?_⟩
  have hd : astDecAns arithRIx e v = some (.read (.count a) (.count n.toNat)) := by
    simp [astDecAns, astDecRead, arithRIx, h1, h2, hans, i32Arg, i32Res, Val.i32]
  exact (hv _ _ hd).2

/-- An allowed answer of `child(a, i)`. -/
theorem child_post {i : BitVec 32} (he : I.importOp? 2 [.i32 a, .i32 i] = some e)
    (hv : (astISpec (ts := I.imports) arithRIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ∃ p cs x, ρ a = some (TExpr.ofList p cs) ∧ cs[i.toNat]? = some x ∧
      ρ c = some x := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨c, rfl⟩ := res_i32 hty
  refine ⟨c, rfl, ?_⟩
  have hd : astDecAns arithRIx e v = some (.read (.child a i.toNat) (.handle c)) := by
    simp [astDecAns, astDecRead, arithRIx, h1, h2, hans, i32Res, Val.i32]
    rfl
  exact (hv _ _ hd).2

end Posts

/-! ## Instructions -/

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {f : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

theorem X.drop {v : Val} (h : HWP P host s f (vals us ++ expression is) Q) :
    HWP P host s f (vals (us ++ [v]) ++ expression (.drop :: is)) Q :=
  Wp.drop (m := .part) h

section Calls

variable {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST arithSig.toAstSig)}
  {L : Set (AST arithSig.toAstSig)} {a : BitVec 32}
  (hs : s.funcs = (Verify.instOf addCheck).store.funcs) (hm : f.module.funcs = List.range 5)

/-- The host of the checker. -/
abbrev H (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST arithSig.toAstSig))
    (L : Set (AST arithSig.toAstSig)) : HostSemantics Nat :=
  gameHost (Verify.instOf addCheck) (astISpec arithRIx ρ L)

include hs hm

theorem X.tag (hQ : Leaves Q s)
    (hc : ∀ c w, (∀ p, decTag arithRIx [.i32 c, .i64 w] = some p →
      ∃ cs, ρ a = some (TExpr.ofList p cs)) →
      HWP P (H ρ L) s f (vals (us ++ [.i32 c] ++ [.i64 w]) ++ expression is) Q) :
    HWP P (H ρ L) s f (vals (us ++ [.i32 a]) ++ expression (.call ⟨0⟩ :: is)) Q :=
  X.callG add_shape hs hm (k := 0) (by decide) rfl rfl
    (pre_of_ne add_shape.imports (k := 0) (by decide) (by decide) (.cons ⟨a, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨c, w, rfl, h⟩ := tag_post add_shape.imports he hv hr
      simpa using hc c w h) hQ

theorem X.count (hQ : Leaves Q s)
    (hc : ∀ n, (∃ p cs, ρ a = some (TExpr.ofList p cs) ∧ cs.length = n.toNat) →
      HWP P (H ρ L) s f (vals (us ++ [.i32 n]) ++ expression is) Q) :
    HWP P (H ρ L) s f (vals (us ++ [.i32 a]) ++ expression (.call ⟨1⟩ :: is)) Q :=
  X.callG add_shape hs hm (k := 1) (by decide) rfl rfl
    (pre_of_ne add_shape.imports (k := 1) (by decide) (by decide) (.cons ⟨a, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨n, rfl, h⟩ := count_post add_shape.imports he hv hr
      exact hc n h) hQ

theorem X.child {i : BitVec 32} (hQ : Leaves Q s)
    (hc : ∀ c, (∃ p cs x, ρ a = some (TExpr.ofList p cs) ∧ cs[i.toNat]? = some x ∧
      ρ c = some x) → HWP P (H ρ L) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (H ρ L) s f (vals (us ++ [.i32 a] ++ [.i32 i]) ++ expression (.call ⟨2⟩ :: is)) Q := by
  rw [List.append_assoc]
  exact X.callG add_shape hs hm (k := 2) (by decide) rfl rfl
    (pre_of_ne add_shape.imports (k := 2) (by decide) (by decide)
      (.cons ⟨a, rfl⟩ (.cons ⟨i, rfl⟩ .nil)))
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, h⟩ := child_post add_shape.imports he hv hr
      exact hc c h) hQ

theorem X.accept (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : Leaves Q s)
    (hc : HWP P (H ρ L) s f (vals us ++ expression is) Q) :
    HWP P (H ρ L) s f (vals (us ++ [.i32 a]) ++ expression (.call ⟨3⟩ :: is)) Q :=
  X.callG add_shape hs hm (k := 3) (by decide) rfl rfl (pre_accept add_shape.imports a hL)
    (fun _ _ he _ res hr => by
      obtain ⟨-, -⟩ := importOp?_eq he
      obtain ⟨hty, -⟩ := results_ofG add_shape.imports hr
      simp only [(importOp?_eq he).1] at hty
      obtain rfl := res_nil hty
      simpa using hc) hQ

end Calls

/-! ## The body -/

section Body

variable {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST arithSig.toAstSig)}

/-- A child that passes `leafCheck` is a leaf `num a`. -/
theorem leaf_step (hs : s.funcs = (Verify.instOf addCheck).store.funcs) {mi : ModuleInst}
    (hm : mi.funcs = List.range 5) {h l k : BitVec 32} {cs : List (AST arithSig.toAstSig)}
    (hh : ρ h = some (TExpr.ofList ⟨ArithTag.add, ()⟩ cs)) (hQ : Leaves Q s)
    (hk : ∀ c a, cs[k.toNat]? = some (numLeaf a) →
      HWP P (H ρ addL) s ⟨[some (.i32 h), some (.i32 c)], mi⟩ (vals [] ++ expression is) Q) :
    HWP P (H ρ addL) s ⟨[some (.i32 h), some (.i32 l)], mi⟩
      (vals [] ++ expression (leafCheck k ++ is)) Q := by
  simp only [leafCheck, List.cons_append, List.nil_append]
  refine X.localGet (v := .i32 h) rfl ?_
  refine X.i32Const ?_
  refine X.child hs hm hQ (fun c hc => ?_)
  obtain ⟨p, cs', x, hh', hx, hcx⟩ := hc
  obtain ⟨-, rfl⟩ := ofList_inj2 (Option.some.inj (hh.symm.trans hh'))
  refine X.localSet (by simp [Idx.toNat]) ?_
  refine X.localGet (v := .i32 c) rfl ?_
  refine X.tag hs hm hQ (fun c₁ w hc₁ => ?_)
  refine X.drop ?_
  refine X.neConst ?_
  refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun h0 => ?_)
  have hc0 : c₁ = 0 := bne_eq_false_iff_eq.1 (bool32_eq_zero h0)
  subst hc0
  obtain ⟨cs₁, hcs₁⟩ := hc₁ ⟨ArithTag.num, (Int64.ofBitVec w, ())⟩ rfl
  refine X.localGet (v := .i32 c) rfl ?_
  refine X.count hs hm hQ (fun n hn => ?_)
  refine X.neConst ?_
  refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun hn0 => ?_)
  have hn0' : n = 0 := bne_eq_false_iff_eq.1 (bool32_eq_zero hn0)
  subst hn0'
  obtain ⟨p', cs₂, hc₂, hl₂⟩ := hn
  obtain ⟨-, rfl⟩ := ofList_inj2 (Option.some.inj (hcs₁.symm.trans hc₂))
  obtain rfl : cs₁ = [] := List.eq_nil_of_length_eq_zero (by simpa using hl₂)
  have hxl : x = numLeaf (Int64.ofBitVec w) := Option.some.inj (hcx.symm.trans hcs₁)
  exact hk c _ (hxl ▸ hx)

theorem two_of {α : Type} {cs : List α} {x y : α} (hl : cs.length = 2) (h0 : cs[0]? = some x)
    (h1 : cs[1]? = some y) : cs = [x, y] := by
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> simp_all

/-- **`addCheck` meets the AST reader specification for `addL`** in every environment and every
profile. -/
theorem addCheck_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (AST arithSig.toAstSig)) :
    GameSat P (Verify.instOf addCheck) (StoreInv (Verify.instOf addCheck))
      (astISpec arithRIx ρ addL) (topISpec _) :=
  gameSat_ofG add_shape rfl fun fi s args Q hargs _ hm hs hQ _ => by
    obtain ⟨h, rfl⟩ : ∃ h, args = [.i32 h] := by
      rcases hargs with _ | ⟨⟨h, rfl⟩, hnil⟩
      cases hnil
      exact ⟨h, rfl⟩
    simp only [addBody, List.cons_append, List.nil_append, List.append_assoc]
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.tag hs hm hQ (fun c w hc => ?_)
    refine X.drop ?_
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun h1 => ?_)
    have hc1 : c = 1 := bne_eq_false_iff_eq.1 (bool32_eq_zero h1)
    subst hc1
    obtain ⟨cs, hcs⟩ := hc ⟨ArithTag.add, ()⟩ rfl
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.count hs hm hQ (fun n hn => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun hn2 => ?_)
    have hn2' : n = 2 := bne_eq_false_iff_eq.1 (bool32_eq_zero hn2)
    subst hn2'
    obtain ⟨p', cs', hc', hl'⟩ := hn
    obtain ⟨-, rfl⟩ := ofList_inj2 (Option.some.inj (hcs.symm.trans hc'))
    refine leaf_step hs hm hcs hQ (fun c₁ a₁ h₁ => ?_)
    refine leaf_step hs hm hcs hQ (fun c₂ a₂ h₂ => ?_)
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.accept hs hm (fun t ht => ?_) hQ (X.return_ ((hQ _).1 _))
    rw [hcs] at ht
    cases ht
    exact ⟨a₁, a₂, by rw [two_of hl' h₁ h₂]⟩

end Body

end Silmaril.Proofs.Wasm.Game.HandleAccept.Ast.Checker
