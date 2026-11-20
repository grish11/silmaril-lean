module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Generic
public import Silmaril.Wasm.Game.HandleAccept.Tree2.Checkers.Defs

/-!
# `combCheck` meets its specification

What an allowed answer of the binary-tree reader imports `isAtom`, `left`, `right` and
`accept` (indices `combIx`) says under `tree2ISpec`, the call rules for an instantiated module
of shape `GShape I consFTs aFT …` (the import types are those of the cons reader), and
`combCheck_sat`: in every environment `ρ` and every profile, the instance of `combCheck` meets
the binary-tree reader specification for `combL` with the store invariant `StoreInv`. Loop
invariant: the locals are `[h, cur, k]` and if `cur` denotes a right comb of words (or nothing)
then so does `h`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Tree2 Silmaril.Wasm.Game.HandleAccept.Tree2.Checkers
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Strategy (ISpec)
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {P : Profile} {s : Store Nat} {f : Frame} {us : List Val} {is : List Instr}
  {Q : Post Nat}

/-! ## Answers -/

section Posts

variable {I : ScalarInstance} (hI : I.imports = consFTs)
  {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64))} {L : Set (Tree2 (BitVec 64))}

include hI

/-- Only `accept` has a precondition. -/
theorem t2_pre_of_ne {k : Nat} (hk : k < 5) (h4 : k ≠ 4) (a : BitVec 32) :
    ∃ e, I.importOp? k [.i32 a] = some e ∧ (tree2ISpec (ts := I.imports) combIx ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_existsG hI hk (args := [.i32 a]) (by
    rcases k with _ | _ | _ | _ | _ | k <;> first | exact .cons ⟨a, rfl⟩ .nil | omega)
  refine ⟨e, he, fun h hd => ?_⟩
  have h1 := (importOp?_eq he).1
  simp [t2DecAsk, combIx, h1, h4] at hd

/-- `accept(a)` is allowed when `a` denotes a member of `L`. -/
theorem t2_pre_accept (a : BitVec 32) (hL : ∀ t, ρ a = some t → t ∈ L) :
    ∃ e, I.importOp? 4 [.i32 a] = some e ∧ (tree2ISpec (ts := I.imports) combIx ρ L).pre e := by
  obtain ⟨e, he⟩ := importOp?_existsG hI (k := 4) (by decide) (.cons ⟨a, rfl⟩ .nil)
  refine ⟨e, he, fun h hd => ?_⟩
  obtain ⟨h1, h2⟩ := importOp?_eq he
  simp [t2DecAsk, combIx, h1, h2, i32Arg] at hd
  obtain rfl := hd
  exact hL

variable {e : I.E.Op} {v : I.E.Ar e} {a : BitVec 32} {res : List Val}

/-- An allowed answer of `isAtom(a)`. -/
theorem isAtom_post (he : I.importOp? 0 [.i32 a] = some e)
    (hv : (tree2ISpec (ts := I.imports) combIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ((c = 0 ∧ ∃ x y, ρ a = some (.cons x y)) ∨
      (c = 1 ∧ ∃ w, ρ a = some (.atom w))) := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨c, rfl⟩ := res_i32 hty
  refine ⟨c, rfl, ?_⟩
  have hd : t2DecAns combIx e v = some (.read (.isAtom a) (isAtomAns c)) := by
    simp [t2DecAns, t2DecRead, combIx, h1, h2, hans, i32Arg, i32Res, Val.i32]
  obtain ⟨-, hok⟩ := hv _ _ hd
  unfold isAtomAns at hok
  split_ifs at hok with hc0 hc1
  · obtain ⟨x, hx, hk⟩ := hok
    cases x with
    | atom => cases hk
    | cons x y => exact .inl ⟨hc0, x, y, hx⟩
  · obtain ⟨x, hx, hk⟩ := hok
    cases x with
    | atom w => exact .inr ⟨hc1, w, hx⟩
    | cons => cases hk
  · exact hok.elim

/-- An allowed answer of `left(a)`. -/
theorem left_post (he : I.importOp? 1 [.i32 a] = some e)
    (hv : (tree2ISpec (ts := I.imports) combIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ∃ x y, ρ a = some (.cons x y) ∧ ρ c = some x := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨c, rfl⟩ := res_i32 hty
  refine ⟨c, rfl, ?_⟩
  have hd : t2DecAns combIx e v = some (.read (.left a) (.handle c)) := by
    simp [t2DecAns, t2DecRead, combIx, h1, h2, hans, i32Arg, i32Res, Val.i32]
  exact (hv _ _ hd).2

/-- An allowed answer of `right(a)`. -/
theorem right_post (he : I.importOp? 2 [.i32 a] = some e)
    (hv : (tree2ISpec (ts := I.imports) combIx ρ L).post e v)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) :
    ∃ c, res = [.i32 c] ∧ ∃ x y, ρ a = some (.cons x y) ∧ ρ c = some y := by
  obtain ⟨h1, h2⟩ := importOp?_eq he
  obtain ⟨hty, hans⟩ := results_ofG hI hr
  simp only [h1] at hty
  obtain ⟨c, rfl⟩ := res_i32 hty
  refine ⟨c, rfl, ?_⟩
  have hd : t2DecAns combIx e v = some (.read (.right a) (.handle c)) := by
    simp [t2DecAns, t2DecRead, combIx, h1, h2, hans, i32Arg, i32Res, Val.i32]
  exact (hv _ _ hd).2

/-- An answer of `accept(a)` returns no values. -/
theorem t2Accept_post (he : I.importOp? 4 [.i32 a] = some e)
    (hr : Answer.toResult (ft := I.imports.get e.1) v = .values res) : res = [] := by
  obtain ⟨h1, -⟩ := importOp?_eq he
  obtain ⟨hty, -⟩ := results_ofG hI hr
  simp only [h1] at hty
  exact res_nil hty

end Posts

/-! ## Calls -/

section Calls

variable {I : ScalarInstance} {locals : List ValType} {body : List Instr} {D : List (Option Val)}
  (hS : GShape I consFTs aFT locals body D) (hs : s.funcs = I.store.funcs)
  (hm : f.module.funcs = List.range (consFTs.length + 1))
  {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64))} {L : Set (Tree2 (BitVec 64))}
  {a : BitVec 32}

include hS hs hm

/-- `isAtom(a)`. -/
theorem X.isAtom (hQ : Leaves Q s)
    (hc : ∀ c, ((c = 0 ∧ ∃ x y, ρ a = some (.cons x y)) ∨ (c = 1 ∧ ∃ w, ρ a = some (.atom w))) →
      HWP P (gameHost I (tree2ISpec combIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (tree2ISpec combIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨0⟩ :: is)) Q :=
  X.callG hS hs hm (k := 0) (by decide) rfl rfl (t2_pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, h⟩ := isAtom_post hS.imports he hv hr
      exact hc c h) hQ

/-- `left(a)`. -/
theorem X.left (hQ : Leaves Q s)
    (hc : ∀ c x y, ρ a = some (.cons x y) → ρ c = some x →
      HWP P (gameHost I (tree2ISpec combIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (tree2ISpec combIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨1⟩ :: is)) Q :=
  X.callG hS hs hm (k := 1) (by decide) rfl rfl (t2_pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, x, y, h₁, h₂⟩ := left_post hS.imports he hv hr
      exact hc c x y h₁ h₂) hQ

/-- `right(a)`. -/
theorem X.right (hQ : Leaves Q s)
    (hc : ∀ c x y, ρ a = some (.cons x y) → ρ c = some y →
      HWP P (gameHost I (tree2ISpec combIx ρ L)) s f (vals (us ++ [.i32 c]) ++ expression is) Q) :
    HWP P (gameHost I (tree2ISpec combIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨2⟩ :: is)) Q :=
  X.callG hS hs hm (k := 2) (by decide) rfl rfl (t2_pre_of_ne hS.imports (by omega) (by omega) a)
    (fun _ _ he hv res hr => by
      obtain ⟨c, rfl, x, y, h₁, h₂⟩ := right_post hS.imports he hv hr
      exact hc c x y h₁ h₂) hQ

/-- `accept(a)`, for `a` denoting a member of `L`. -/
theorem X.t2Accept (hL : ∀ t, ρ a = some t → t ∈ L) (hQ : Leaves Q s)
    (hc : HWP P (gameHost I (tree2ISpec combIx ρ L)) s f (vals us ++ expression is) Q) :
    HWP P (gameHost I (tree2ISpec combIx ρ L)) s f
      (vals (us ++ [.i32 a]) ++ expression (.call ⟨4⟩ :: is)) Q :=
  X.callG hS hs hm (k := 4) (by decide) rfl rfl (t2_pre_accept hS.imports a hL)
    (fun _ _ he _ res hr => by
      obtain rfl := t2Accept_post hS.imports he hr
      simpa using hc) hQ

end Calls

/-! ## The checker -/

/-- The body of `combCheck`'s function. -/
def combBody : List Instr := [.localGet ⟨0⟩, .localSet ⟨1⟩, .loop .empty combLoop]

theorem comb_shape : GShape (Verify.instOf combCheck) consFTs aFT [.i32, .i32] combBody
    [some (.i32 0), some (.i32 0)] :=
  GShape.of_ok (by decide +kernel)

/-- `h` denotes a right comb of words, if anything. -/
def GoodC (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64))) (h : BitVec 32) :
    Prop :=
  ∀ t, ρ h = some t → t ∈ combL

variable {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64))}

/-- The loop invariant. -/
def CombInv (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64))) (s₀ : Store Nat)
    (h : BitVec 32) (mi : ModuleInst) (s : Store Nat) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ cur k : BitVec 32, f = ⟨[some (.i32 h), some (.i32 cur), some (.i32 k)], mi⟩ ∧
    (GoodC ρ cur → GoodC ρ h)

theorem comb_loop {s : Store Nat} (hs : s.funcs = (Verify.instOf combCheck).store.funcs)
    {mi : ModuleInst} (hm : mi.funcs = List.range (consFTs.length + 1)) {h cur k : BitVec 32}
    {Q : Post Nat} (hQ : Leaves Q s) (hg : GoodC ρ cur → GoodC ρ h) :
    HWP P (gameHost (Verify.instOf combCheck) (tree2ISpec combIx ρ combL)) s
      ⟨[some (.i32 h), some (.i32 cur), some (.i32 k)], mi⟩
      (vals [] ++ expression combLoop)
      (loopPost 0 [] (fun s' f vs => vs = [] ∧ CombInv ρ s h mi s' f) Q) := by
  have hL := hQ.loop (Inv := fun s' f vs => vs = [] ∧ CombInv ρ s h mi s' f)
  have hS := comb_shape
  simp only [combLoop]
  refine X.localGet (v := .i32 cur) rfl ?_
  refine X.isAtom hS hs hm hL (fun c hc => ?_)
  refine X.localSet (by simp [Idx.toNat]) ?_
  refine X.localGet (v := .i32 c) rfl ?_
  refine X.neConst ?_
  refine X.eqz ?_
  refine X.if_ (fun h1 => ?_) (fun h1 => ?_)
  · have hc1 : c = 1 :=
      bne_eq_false_iff_eq.1 (bool32_eq_zero (beq_iff_eq.1 (bool32_ne_zero h1)))
    obtain ⟨w, hw⟩ : ∃ w, ρ cur = some (.atom w) := by
      rcases hc with ⟨rfl, -⟩ | ⟨-, hw⟩
      · exact absurd hc1 (by decide)
      · exact hw
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.t2Accept hS hs hm (hg fun t ht => ?_) hL.label (X.return_ ((hL.label _).1 _))
    rw [hw] at ht
    cases ht
    exact ⟨[], w, rfl⟩
  · refine X.localGet (v := .i32 c) rfl ?_
    refine X.if_ (fun _ => X.return_ ((hL.label _).1 _)) (fun hc0 => ?_)
    refine X.localGet (v := .i32 cur) rfl ?_
    refine X.left hS hs hm hL (fun e' x y hcur he' => ?_)
    refine X.isAtom hS hs hm hL (fun c₂ hc₂ => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hL.label _).1 _)) (fun h1 => ?_)
    have hc1 : c₂ = 1 := bne_eq_false_iff_eq.1 (bool32_eq_zero h1)
    obtain ⟨w, hw⟩ : ∃ w, ρ e' = some (.atom w) := by
      rcases hc₂ with ⟨rfl, -⟩ | ⟨-, hw⟩
      · exact absurd hc1 (by decide)
      · exact hw
    obtain rfl : x = .atom w := Option.some.inj (he'.symm.trans hw)
    refine X.localGet (v := .i32 cur) rfl ?_
    refine X.right hS hs hm hL (fun c' x' y' hcur' hc' => ?_)
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    refine X.br0 ⟨[], [], rfl, rfl, rfl, rfl, c', c, rfl, fun hg' => hg fun t ht => ?_⟩
    rw [hcur] at hcur'
    obtain ⟨-, rfl⟩ := Tree2.cons.inj (Option.some.inj hcur')
    rw [hcur] at ht
    cases ht
    obtain ⟨ws, w', rfl⟩ := hg' _ hc'
    exact ⟨w :: ws, w', rfl⟩

/-- **`combCheck` meets the binary-tree reader specification for `combL`** in every
environment and every profile. -/
theorem combCheck_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (Tree2 (BitVec 64))) :
    GameSat P (Verify.instOf combCheck) (StoreInv (Verify.instOf combCheck))
      (tree2ISpec combIx ρ combL) (topISpec _) :=
  gameSat_ofG comb_shape rfl fun fi s args Q ht _ hm hs hQ _ => by
    obtain ⟨h, rfl⟩ : ∃ h, args = [.i32 h] := by
      rcases ht with _ | ⟨⟨h, rfl⟩, hnil⟩
      cases hnil
      exact ⟨h, rfl⟩
    simp only [combBody]
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.localSet (by simp [Idx.toNat]) ?_
    exact X.loop (Inv := CombInv ρ s h fi.module)
      (fun s' f hI => by
        obtain ⟨rfl, cur, k, rfl, hg⟩ := hI
        exact comb_loop hs hm hQ hg) ⟨rfl, h, 0, rfl, id⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Tree2
