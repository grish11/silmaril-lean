module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Generic
public import Silmaril.Wasm.Game.HandleAccept.Writer.Builders.Defs

/-!
# `twoWords` meets its writer specification

What an allowed answer of the cons writer imports `nil`, `cons`, `word` (indices `twoIx`) says
under `writerISpec` without sentinel (`wNil_post`, `wCons_post`, `wWord_post`), the call rules
for an instance of shape `GShape I twoFTs runFT …`, and `twoWords_sat`: in every fixed
environment `ρ` and every profile, the instance of `twoWords` meets the writer specification
of `twoWordsL`, with the store invariant `StoreInv`. Straight-line code: the written handles
denote, in `ρ`, the trees built from the trees of their arguments.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- `[] → [i32]`. -/
abbrev nilFT : FnType := ⟨[], [.num (.int .i32)]⟩
/-- `[i32 i32] → [i32]`. -/
abbrev consFT : FnType := ⟨[.num (.int .i32), .num (.int .i32)], [.num (.int .i32)]⟩
/-- `[i64] → [i32]`. -/
abbrev wordFT : FnType := ⟨[.num (.int .i64)], [.num (.int .i32)]⟩
/-- `[i64] → []`. -/
abbrev runFT : FnType := ⟨[.num (.int .i64)], []⟩

/-- The import types of `twoWords`. -/
abbrev twoFTs : List FnType := [nilFT, consFT, wordFT, aFT]

/-- The writer specification without sentinel. -/
abbrev WSpec (I : ScalarInstance) (ρ : Env (BitVec 32) (SExp2 (BitVec 64)))
    (L : Set (SExp2 (BitVec 64))) : ISpec I.E :=
  writerISpec (consW (BitVec 64)) none (consWDecAsk (ts := I.imports) twoIx)
    (consWDecAns twoIx) ρ L

variable {P : Profile} {s : Store Nat} {f : Frame} {us : List Val} {is : List Instr}
  {Q : Post Nat}

/-! ## Answers -/

section Posts

variable {I : ScalarInstance} (hI : I.imports = twoFTs)
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}

include hI

/-- Only `accept` has a precondition. -/
theorem w_pre_of_ne {k : Nat} (hk : k < 4) (h3 : k ≠ 3) {args : List Val}
    (ht : List.Forall₂ ScalarType.HasVal (twoFTs[k]'hk).params args) :
    ∃ e, I.importOp? k args = some e ∧ (WSpec I ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_existsG hI hk ht
  refine ⟨e, he, fun h hd => ?_⟩
  have h1 := (importOp?_eq he).1
  simp [consWDecAsk, twoIx, h1, h3] at hd

/-- `accept(a)` is allowed when `a` denotes a member of `L`. -/
theorem w_pre_accept (a : BitVec 32) (hL : ∀ t, ρ a = some t → t ∈ L) :
    ∃ e, I.importOp? 3 [.i32 a] = some e ∧ (WSpec I ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_existsG hI (k := 3) (by decide) (.cons ⟨a, rfl⟩ .nil)
  refine ⟨e, he, fun h hd => ?_⟩
  obtain ⟨h1, h2⟩ := importOp?_eq he
  simp [consWDecAsk, twoIx, h1, h2, i32Arg] at hd
  obtain rfl := hd
  exact hL

variable {e : I.E.Op} {v : I.E.Ar e} {res : List Val}

/-- An allowed answer of `word(x)`. -/
theorem wWord_post {x : BitVec 64} (he : I.importOp? 2 [.i64 x] = some e)
    (hv : (WSpec I ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ r, res = [.i32 r] ∧ ρ r = some (.atom x) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨r, rfl⟩ := res_i32 hty
  refine ⟨r, rfl, ?_⟩
  have hd : consWDecAns twoIx e v = some (.write (.atom x) [] r) := by
    simp [consWDecAns, twoIx, h1, h2, retI32, hans, i32Res, i64Arg, Val.i32, Val.i64]
  rcases hv _ _ _ hd with h | ⟨t, ht, hr⟩
  · cases h
  · simp [Writer.built, Env.lookupAll, consW] at ht
    rw [hr, ← ht]

/-- An allowed answer of `nil()`. -/
theorem wNil_post (he : I.importOp? 0 [] = some e) (hv : (WSpec I ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ r, res = [.i32 r] ∧ ρ r = some .nil := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨r, rfl⟩ := res_i32 hty
  refine ⟨r, rfl, ?_⟩
  have hd : consWDecAns twoIx e v = some (.write .nil [] r) := by
    simp [consWDecAns, twoIx, h1, h2, retI32, hans, i32Res, Val.i32]
  rcases hv _ _ _ hd with h | ⟨t, ht, hr⟩
  · cases h
  · simp [Writer.built, Env.lookupAll, consW] at ht
    rw [hr, ← ht]

/-- An allowed answer of `cons(a, b)`. -/
theorem wCons_post {a b : BitVec 32} {x y : SExp2 (BitVec 64)} (ha : ρ a = some x)
    (hb : ρ b = some y) (he : I.importOp? 1 [.i32 a, .i32 b] = some e)
    (hv : (WSpec I ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ r, res = [.i32 r] ∧ ρ r = some (.cons x y) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨r, rfl⟩ := res_i32 hty
  refine ⟨r, rfl, ?_⟩
  have hd : consWDecAns twoIx e v = some (.write .cons [a, b] r) := by
    simp [consWDecAns, twoIx, h1, h2, retI32, hans, i32Res, i32Pair, Val.i32]
  rcases hv _ _ _ hd with h | ⟨t, ht, hr⟩
  · cases h
  · simp [Writer.built, Env.lookupAll, consW, ha, hb] at ht
    rw [hr, ← ht]

/-- An answer of `accept(a)` returns no values. -/
theorem wAccept_post {a : BitVec 32} (he : I.importOp? 3 [.i32 a] = some e)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) : res = [] := by
  obtain ⟨h1, -⟩ := importOp?_eq he
  obtain ⟨hty, -⟩ := results_ofG hI hr
  simp only [h1] at hty
  exact res_nil hty

end Posts

/-! ## Calls -/

section Calls

variable {I : ScalarInstance} {locals : List ValType} {body : List Instr} {D : List (Option Val)}
  (hS : GShape I twoFTs runFT locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = List.range (twoFTs.length + 1))
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}

include hS hs hm

/-- `word(x)`. -/
theorem X.wWord {x : BitVec 64} (hQ : Leaves Q s)
    (hc : ∀ r, ρ r = some (.atom x) →
      HWP P (gameHost I (WSpec I ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (WSpec I ρ L)) s f
      (vals (us ++ [.i64 x]) ++ expression (.call ⟨2⟩ :: is)) Q :=
  X.callG hS hs hm (k := 2) (by decide) rfl rfl
    (w_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨x, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := wWord_post hS.imports he hv hr
      exact hc r h) hQ

/-- `nil()`. -/
theorem X.wNil (hQ : Leaves Q s)
    (hc : ∀ r, ρ r = some .nil →
      HWP P (gameHost I (WSpec I ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (WSpec I ρ L)) s f (vals us ++ expression (.call ⟨0⟩ :: is)) Q := by
  have h := X.callG (us := us) (args := []) (x := ⟨0⟩) hS hs hm (k := 0) (by decide) rfl rfl
    (w_pre_of_ne hS.imports (by decide) (by decide) .nil)
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := wNil_post hS.imports he hv hr
      exact hc r h) hQ
  simpa using h

/-- `cons(a, b)`. -/
theorem X.wCons {a b : BitVec 32} {x y : SExp2 (BitVec 64)} (ha : ρ a = some x)
    (hb : ρ b = some y) (hQ : Leaves Q s)
    (hc : ∀ r, ρ r = some (.cons x y) →
      HWP P (gameHost I (WSpec I ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (WSpec I ρ L)) s f
      (vals (us ++ [.i32 a] ++ [.i32 b]) ++ expression (.call ⟨1⟩ :: is)) Q := by
  rw [List.append_assoc]
  exact X.callG hS hs hm (k := 1) (args := [.i32 a, .i32 b]) (by decide) rfl rfl
    (w_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨a, rfl⟩ (.cons ⟨b, rfl⟩ .nil)))
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := wCons_post hS.imports ha hb he hv hr
      exact hc r h) hQ

/-- `accept(a)`, for `a` denoting a member of `L`. -/
theorem X.wAccept {a : BitVec 32} (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : Leaves Q s)
    (hc : HWP P (gameHost I (WSpec I ρ L)) s f (vals us ++ expression is) Q) :
    HWP P (gameHost I (WSpec I ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨3⟩ :: is)) Q :=
  X.callG hS hs hm (k := 3) (by decide) rfl rfl (w_pre_accept hS.imports a hL)
    (fun _ _ he _ res hr => by
      obtain rfl := wAccept_post hS.imports he hr
      simpa using hc) hQ

end Calls

/-! ## `i64` arithmetic -/

theorem X.i64Const {host : HostSemantics Nat} {c : BitVec 64}
    (h : HWP P host s f (vals (us ++ [.i64 c]) ++ expression is) Q) :
    HWP P host s f (vals us ++ expression (.intConst .i64 c :: is)) Q := by
  simpa [vals, expression, Val.i64, Val.toAdmin] using h

theorem X.add64 {host : HostSemantics Nat} {x y : BitVec 64}
    (h : HWP P host s f (vals (us ++ [.i64 (x + y)]) ++ expression is) Q) :
    HWP P host s f (vals (us ++ [.i64 x] ++ [.i64 y]) ++ expression (.intBinOp .i64 .add :: is))
      Q := by
  rw [List.append_assoc]
  exact Wp.intBinOp (m := .part) (t := .i64) (x := x) (y := y) (z := x + y) rfl h

/-! ## The module -/

theorem two_shape : GShape (Verify.instOf twoWords) twoFTs runFT [] twoBody [] :=
  GShape.of_ok (by decide +kernel)

theorem args_runFT {args : List Val} (ht : List.Forall₂ ScalarType.HasVal runFT.params args) :
    ∃ x, args = [.i64 x] := by
  rcases ht with _ | ⟨⟨x, rfl⟩, hnil⟩
  cases hnil
  exact ⟨x, rfl⟩

/-- **`twoWords` meets the writer specification of `twoWordsL`** (no sentinel) in every fixed
environment and every profile. -/
theorem twoWords_sat (P : Profile) (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf twoWords) (StoreInv (Verify.instOf twoWords))
      (WSpec (Verify.instOf twoWords) ρ twoWordsL) (topISpec _) :=
  gameSat_ofG two_shape rfl fun fi s args Q ht _ hm hs hQ hQn => by
    obtain ⟨x, rfl⟩ := args_runFT ht
    have hS := two_shape
    simp only [twoBody]
    refine X.localGet (v := .i64 x) rfl ?_
    refine X.wWord (us := []) hS hs hm hQ (fun a ha => ?_)
    refine X.localGet (v := .i64 x) rfl ?_
    refine X.i64Const ?_
    refine X.add64 ?_
    refine X.wWord hS hs hm hQ (fun b hb => ?_)
    refine X.wNil hS hs hm hQ (fun n hn => ?_)
    refine X.wCons hS hs hm hb hn hQ (fun l2 hl2 => ?_)
    refine X.wCons (us := []) hS hs hm ha hl2 hQ (fun l1 hl1 => ?_)
    refine X.wAccept hS hs hm (fun t ht' => ?_) hQ (X.done (hQn _))
    rw [hl1] at ht'
    cases ht'
    exact ⟨x, rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords
