module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Writer.TwoWords
public import Silmaril.Wasm.Game.HandleAccept.Writer.Sentinel.Defs

/-!
# Sentinel-testing writer modules meet their specification

What an allowed answer of the cons writer imports says under `writerISpec` **with a sentinel
`sen`** (`sWord_post`, `sNil_post`, `sCons_post`: the result is the sentinel or denotes the
built tree), the call rules for an instance of shape `GShape I twoFTs runFT …`, the rules of the
two failure tests (`TestRule`: `isZ_rule`, `isM_rule`), and `sent_sat`: an instance whose body is
`sentBody test`, for a test of the sentinel `sen`, meets the writer specification of
`twoWordsL` with sentinel `sen` in every fixed environment and every profile. Every result is
tested before use: a failure returns, and past the test the result denotes its tree.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.Sentinel

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Formats.Api Silmaril.Accept.Handle Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Writers Silmaril.Wasm.Game.HandleAccept.Writers.Builders
  Silmaril.Wasm.Game.HandleAccept.Writers.Sentinel
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.TwoWords
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- The writer specification with sentinel `sen`. -/
abbrev SSpec (I : ScalarInstance) (sen : Option (BitVec 32))
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) (L : Set (SExp2 (BitVec 64))) : ISpec I.E :=
  writerISpec (consW (BitVec 64)) sen (consWDecAsk (ts := I.imports) twoIx)
    (consWDecAns twoIx) ρ L

variable {P : Profile} {s : Store Nat} {f : Frame} {us : List Val} {is : List Instr}
  {Q : Post Nat}

/-! ## Answers -/

section Posts

variable {I : ScalarInstance} (hI : I.imports = twoFTs) {sen : Option (BitVec 32)}
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}

include hI

theorem s_pre_of_ne {k : Nat} (hk : k < 4) (h3 : k ≠ 3) {args : List Val}
    (ht : List.Forall₂ ScalarType.HasVal (twoFTs[k]'hk).params args) :
    ∃ e, I.importOp? k args = some e ∧ (SSpec I sen ρ L).pre e :=
  w_pre_of_ne hI hk h3 ht

theorem s_pre_accept (a : BitVec 32) (hL : ∀ t, ρ a = some t → t ∈ L) :
    ∃ e, I.importOp? 3 [.i32 a] = some e ∧ (SSpec I sen ρ L).pre e :=
  w_pre_accept hI a hL

variable {e : I.E.Op} {v : I.E.Ar e} {res : List Val}

/-- An allowed answer of `word(x)`: the sentinel, or a handle of the atom. -/
theorem sWord_post {x : BitVec 64} (he : I.importOp? 2 [.i64 x] = some e)
    (hv : (SSpec I sen ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ r, res = [.i32 r] ∧ (sen = some r ∨ ρ r = some (.atom x)) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨r, rfl⟩ := res_i32 hty
  refine ⟨r, rfl, ?_⟩
  have hd : consWDecAns twoIx e v = some (.write (.atom x) [] r) := by
    simp [consWDecAns, twoIx, h1, h2, retI32, hans, i32Res, i64Arg, Val.i32, Val.i64]
  rcases hv _ _ _ hd with h | ⟨t, ht, hr⟩
  · exact .inl h
  · simp [Writer.built, Env.lookupAll, consW] at ht
    rw [hr, ← ht]
    exact .inr rfl

/-- An allowed answer of `nil()`. -/
theorem sNil_post (he : I.importOp? 0 [] = some e) (hv : (SSpec I sen ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ r, res = [.i32 r] ∧ (sen = some r ∨ ρ r = some .nil) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨r, rfl⟩ := res_i32 hty
  refine ⟨r, rfl, ?_⟩
  have hd : consWDecAns twoIx e v = some (.write .nil [] r) := by
    simp [consWDecAns, twoIx, h1, h2, retI32, hans, i32Res, Val.i32]
  rcases hv _ _ _ hd with h | ⟨t, ht, hr⟩
  · exact .inl h
  · simp [Writer.built, Env.lookupAll, consW] at ht
    rw [hr, ← ht]
    exact .inr rfl

/-- An allowed answer of `cons(a, b)`. -/
theorem sCons_post {a b : BitVec 32} {x y : SExp2 (BitVec 64)} (ha : ρ a = some x)
    (hb : ρ b = some y) (he : I.importOp? 1 [.i32 a, .i32 b] = some e)
    (hv : (SSpec I sen ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ r, res = [.i32 r] ∧ (sen = some r ∨ ρ r = some (.cons x y)) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨r, rfl⟩ := res_i32 hty
  refine ⟨r, rfl, ?_⟩
  have hd : consWDecAns twoIx e v = some (.write .cons [a, b] r) := by
    simp [consWDecAns, twoIx, h1, h2, retI32, hans, i32Res, i32Pair, Val.i32]
  rcases hv _ _ _ hd with h | ⟨t, ht, hr⟩
  · exact .inl h
  · simp [Writer.built, Env.lookupAll, consW, ha, hb] at ht
    rw [hr, ← ht]
    exact .inr rfl

end Posts

/-! ## Calls -/

section Calls

variable {I : ScalarInstance} {locals : List ValType} {body : List Instr} {D : List (Option Val)}
  (hS : GShape I twoFTs runFT locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = List.range (twoFTs.length + 1)) {sen : Option (BitVec 32)}
  {ρ : Env (BitVec 32) (SExp2 (BitVec 64))} {L : Set (SExp2 (BitVec 64))}

include hS hs hm

/-- `word(x)`. -/
theorem X.sWord {x : BitVec 64} (hQ : Leaves Q s)
    (hc : ∀ r, (sen = some r ∨ ρ r = some (.atom x)) →
      HWP P (gameHost I (SSpec I sen ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (SSpec I sen ρ L)) s f
      (vals (us ++ [.i64 x]) ++ expression (.call ⟨2⟩ :: is)) Q :=
  X.callG hS hs hm (k := 2) (by decide) rfl rfl
    (s_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨x, rfl⟩ .nil))
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := sWord_post hS.imports he hv hr
      exact hc r h) hQ

/-- `nil()`. -/
theorem X.sNil (hQ : Leaves Q s)
    (hc : ∀ r, (sen = some r ∨ ρ r = some .nil) →
      HWP P (gameHost I (SSpec I sen ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (SSpec I sen ρ L)) s f (vals us ++ expression (.call ⟨0⟩ :: is)) Q := by
  have h := X.callG (us := us) (args := []) (x := ⟨0⟩) hS hs hm (k := 0) (by decide) rfl rfl
    (s_pre_of_ne hS.imports (by decide) (by decide) .nil)
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := sNil_post hS.imports he hv hr
      exact hc r h) hQ
  simpa using h

/-- `cons(a, b)`. -/
theorem X.sCons {a b : BitVec 32} {x y : SExp2 (BitVec 64)} (ha : ρ a = some x)
    (hb : ρ b = some y) (hQ : Leaves Q s)
    (hc : ∀ r, (sen = some r ∨ ρ r = some (.cons x y)) →
      HWP P (gameHost I (SSpec I sen ρ L)) s f (vals (us ++ [.i32 r]) ++ expression is) Q) :
    HWP P (gameHost I (SSpec I sen ρ L)) s f
      (vals (us ++ [.i32 a] ++ [.i32 b]) ++ expression (.call ⟨1⟩ :: is)) Q := by
  rw [List.append_assoc]
  exact X.callG hS hs hm (k := 1) (args := [.i32 a, .i32 b]) (by decide) rfl rfl
    (s_pre_of_ne hS.imports (by decide) (by decide) (.cons ⟨a, rfl⟩ (.cons ⟨b, rfl⟩ .nil)))
    (fun _ _ he hv res hr => by
      obtain ⟨r, rfl, h⟩ := sCons_post hS.imports ha hb he hv hr
      exact hc r h) hQ

/-- `accept(a)`, for `a` denoting a member of `L`. -/
theorem X.sAccept {a : BitVec 32} (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : Leaves Q s)
    (hc : HWP P (gameHost I (SSpec I sen ρ L)) s f (vals us ++ expression is) Q) :
    HWP P (gameHost I (SSpec I sen ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨3⟩ :: is)) Q :=
  X.callG hS hs hm (k := 3) (by decide) rfl rfl (s_pre_accept hS.imports a hL)
    (fun _ _ he _ res hr => by
      obtain rfl := wAccept_post hS.imports he hr
      simpa using hc) hQ

end Calls

/-! ## Failure tests -/

/-- **A failure test of the sentinel `sen`**: from `r` on top of the stack, it leaves an `i32`
that is non-zero exactly when `r` is the sentinel. -/
def TestRule (test : List Instr) (sen : BitVec 32) : Prop :=
  ∀ {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {f : Frame} {us : List Val}
    {is : List Instr} {Q : Post Nat} (r : BitVec 32),
    (∀ c : BitVec 32, (c ≠ 0 ↔ r = sen) →
      HWP P host s f (vals (us ++ [.i32 c]) ++ expression is) Q) →
    HWP P host s f (vals (us ++ [.i32 r]) ++ expression (test ++ is)) Q

theorem bool32_ne_zero_iff (b : Bool) : bool32 b ≠ 0 ↔ b = true := by
  cases b <;> decide

theorem isZ_rule : TestRule isZ 0 := by
  intro P host s f us is Q r h
  simp only [isZ, List.cons_append, List.nil_append]
  exact X.eqz (h _ (by rw [bool32_ne_zero_iff]; simp))

theorem isM_rule : TestRule isM (-1) := by
  intro P host s f us is Q r h
  simp only [isM, List.cons_append, List.nil_append]
  refine X.i32Const (X.rel32 (h _ ?_))
  show bool32 (r == -1) ≠ 0 ↔ r = -1
  rw [bool32_ne_zero_iff]
  simp

/-- `guardRet test k` on a handle `r` held in local `k`: on the sentinel it returns, otherwise
it continues knowing `r ≠ sen`. -/
theorem X.guard_ {host : HostSemantics Nat} {test : List Instr} {sen : BitVec 32}
    (ht : TestRule test sen) {k : LocalIdx} {r : BitVec 32}
    (hk : f.local? k = some (some (.i32 r))) (hQ : Leaves Q s)
    (hc : r ≠ sen → HWP P host s f (vals [] ++ expression is) Q) :
    HWP P host s f (vals [] ++ expression (guardRet test k ++ is)) Q := by
  have hg : guardRet test k ++ is = .localGet k :: (test ++ .if_ .empty [.return_] [] :: is) := by
    unfold guardRet
    simp
  rw [hg]
  refine X.localGet (us := []) hk ?_
  refine ht r fun c hc' => ?_
  refine X.if_ (fun h0 => X.return_ ((hQ.label _).1 _)) (fun h0 => hc fun hr => ?_)
  exact (hc'.2 hr) h0

/-! ## The module -/

/-- The default values of four `i32` locals. -/
abbrev D4 : List (Option Val) := [some (.i32 0), some (.i32 0), some (.i32 0), some (.i32 0)]

/-- The locals of `sentBody`. -/
abbrev L4 : List ValType := [.i32, .i32, .i32, .i32]

/-- **A sentinel-testing body meets the writer specification of `twoWordsL`** with the
sentinel `sen`, in every fixed environment and every profile. -/
theorem sent_sat {I : ScalarInstance} {test : List Instr} {sen : BitVec 32}
    (ht : TestRule test sen) (hS : GShape I twoFTs runFT L4 (sentBody test) D4) (P : Profile)
    (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P I (StoreInv I) (SSpec I (some sen) ρ twoWordsL) (topISpec _) :=
  gameSat_ofG hS rfl fun fi s args Q htA _ hm hs hQ hQn => by
    obtain ⟨x, rfl⟩ := args_runFT htA
    simp only [sentBody, List.append_assoc, List.cons_append, List.nil_append]
    refine X.localGet (v := .i64 x) rfl ?_
    refine X.sWord (us := []) hS hs hm hQ (fun a ha => ?_)
    refine X.localSet (by simp [Idx.toNat]) ?_
    refine X.guard_ ht rfl hQ (fun ha' => ?_)
    have ha : ρ a = some (.atom x) := ha.resolve_left (fun h => ha' (Option.some.inj h).symm)
    refine X.localGet (v := .i64 x) rfl ?_
    refine X.i64Const ?_
    refine X.add64 ?_
    refine X.sWord hS hs hm hQ (fun b hb => ?_)
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    refine X.guard_ ht rfl hQ (fun hb' => ?_)
    have hb : ρ b = some (.atom (x + 1)) :=
      hb.resolve_left (fun h => hb' (Option.some.inj h).symm)
    refine X.sNil (us := []) hS hs hm hQ (fun n hn => ?_)
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    refine X.guard_ ht rfl hQ (fun hn' => ?_)
    have hn : ρ n = some .nil := hn.resolve_left (fun h => hn' (Option.some.inj h).symm)
    refine X.localGet (v := .i32 b) rfl ?_
    refine X.localGet (v := .i32 n) rfl ?_
    refine X.sCons (us := []) hS hs hm hb hn hQ (fun l2 hl2 => ?_)
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    refine X.guard_ ht rfl hQ (fun hl2' => ?_)
    have hl2 : ρ l2 = some (.cons (.atom (x + 1)) .nil) :=
      hl2.resolve_left (fun h => hl2' (Option.some.inj h).symm)
    refine X.localGet (v := .i32 a) rfl ?_
    refine X.localGet (v := .i32 l2) rfl ?_
    refine X.sCons (us := []) hS hs hm ha hl2 hQ (fun l1 hl1 => ?_)
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    refine X.guard_ ht rfl hQ (fun hl1' => ?_)
    have hl1 : ρ l1 = some (.cons (.atom x) (.cons (.atom (x + 1)) .nil)) :=
      hl1.resolve_left (fun h => hl1' (Option.some.inj h).symm)
    refine X.localGet (v := .i32 l1) rfl ?_
    refine X.sAccept (us := []) hS hs hm (fun t ht' => ?_) hQ (X.done (hQn _))
    rw [hl1] at ht'
    cases ht'
    exact ⟨x, rfl⟩

theorem shapeZ : GShape (Verify.instOf twoWordsZ) twoFTs runFT L4 (sentBody isZ) D4 :=
  GShape.of_ok (by decide +kernel)

theorem shapeM : GShape (Verify.instOf twoWordsM) twoFTs runFT L4 (sentBody isM) D4 :=
  GShape.of_ok (by decide +kernel)

/-- **`twoWordsZ` meets the writer specification of `twoWordsL` with the sentinel `0`.** -/
theorem twoWordsZ_sat (P : Profile) (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf twoWordsZ) (StoreInv (Verify.instOf twoWordsZ))
      (SSpec (Verify.instOf twoWordsZ) (some 0) ρ twoWordsL) (topISpec _) :=
  sent_sat isZ_rule shapeZ P ρ

/-- **`twoWordsM` meets the writer specification of `twoWordsL` with the sentinel `-1`.** -/
theorem twoWordsM_sat (P : Profile) (ρ : Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf twoWordsM) (StoreInv (Verify.instOf twoWordsM))
      (SSpec (Verify.instOf twoWordsM) (some (-1)) ρ twoWordsL) (topISpec _) :=
  sent_sat isM_rule shapeM P ρ

end Silmaril.Proofs.Wasm.Game.HandleAccept.Writers.Sentinel
