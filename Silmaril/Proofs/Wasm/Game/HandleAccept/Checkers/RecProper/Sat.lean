module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Proper
public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Generic
public import Silmaril.Wasm.Game.HandleAccept.Checkers.RecProper.Defs

/-!
# `recProperCheck` meets its specification

`recProperCheck_sat`: in every environment `ρ` and every profile, the instance of
`recProperCheck` meets the cons reader specification for `nestL` with the store invariant
`StoreInv`. Two nested loops, each with an invariant on the locals `[h, cur, k, c]`:

* outer (`RPOuterInv`): if `cur` denotes a member of `nestL` (or nothing) then so does `h`;
* inner (`RPInnerInv`): moreover `cur` denotes a cons cell `x . y`, and if the inner cursor `c`
  denotes a proper list of words (or nothing) then so does `x`.

The inner loop continues the outer one with `br 2` (from an `if` inside it), the atom case with
`br 1` (`X.brN`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {P : Profile} {host : HostSemantics Nat} {s : Store Nat} {f : Frame} {us : List Val}
  {is : List Instr} {Q : Post Nat}

/-- A branch to any label. -/
theorem X.brN {l : LabelIdx} (hq : Q s f (.br l.toNat us)) :
    HWP P host s f (vals us ++ expression (.br l :: is)) Q :=
  Wp.br (m := .part) hq

/-- `i32.const y; i32.eq`. -/
theorem X.eqConst {x y : BitVec 32}
    (h : HWP P host s f (vals (us ++ [.i32 (bool32 (x == y))]) ++ expression is) Q) :
    HWP P host s f (vals (us ++ [.i32 x]) ++
      expression (.intConst .i32 y :: .intRelOp .i32 .eq :: is)) Q :=
  X.i32Const (X.rel32 h)

/-! ## Languages -/

theorem nestElem_atom (w : BitVec 64) : NestElem (.atom w) := .inl ⟨w, rfl⟩

theorem nestElem_nil : NestElem .nil := .inr ⟨[], rfl⟩

theorem wordsL_cons_atom {w : BitVec 64} {y : SExp2 (BitVec 64)} (hy : y ∈ wordsL) :
    SExp2.cons (.atom w) y ∈ wordsL := by
  obtain ⟨ws, rfl⟩ := hy
  exact ⟨w :: ws, rfl⟩

/-! ## The module -/

/-- The body of `recProperCheck`'s function. -/
def rpBody : List Instr := [.localGet ⟨0⟩, .localSet ⟨1⟩, .loop .empty rpOuter]

theorem rp_shape : Shape (Verify.instOf recProperCheck) [.i32, .i32, .i32] rpBody
    [some (.i32 0), some (.i32 0), some (.i32 0)] :=
  Shape.of_ok (by decide +kernel)

variable {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))}

/-- The outer loop invariant. -/
def RPOuterInv (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))
    (s₀ : Store Nat) (h : BitVec 32) (mi : ModuleInst) (s : Store Nat) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ cur k c : BitVec 32,
    f = ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 c)], mi⟩ ∧
    (Good ρ nestL cur → Good ρ nestL h)

/-- The inner loop invariant. -/
def RPInnerInv (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))
    (s₀ : Store Nat) (h : BitVec 32) (mi : ModuleInst) (s : Store Nat) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ (cur k c : BitVec 32) (x y : SExp2 (BitVec 64)),
    f = ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 c)], mi⟩ ∧
    ρ cur = some (.cons x y) ∧ (Good ρ wordsL c → x ∈ wordsL) ∧
    (Good ρ nestL cur → Good ρ nestL h)

section Loops

variable {s : Store Nat} (hs : s.funcs = (Verify.instOf recProperCheck).store.funcs)
  {mi : ModuleInst} (hm : mi.funcs = [0, 1, 2, 3, 4, 5]) {h : BitVec 32} {Q : Post Nat}
  (hQ : Leaves Q s)

include hs hm hQ

/-- The postcondition of the outer loop body. -/
abbrev OPost (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (s : Store Nat)
    (h : BitVec 32) (mi : ModuleInst) (Q : Post Nat) : Post Nat :=
  loopPost 0 [] (fun s' f vs => vs = [] ∧ RPOuterInv ρ s h mi s' f) Q

theorem rp_inner {cur k c : BitVec 32} {x y : SExp2 (BitVec 64)}
    (hcur : ρ cur = some (.cons x y)) (hx : Good ρ wordsL c → x ∈ wordsL)
    (hg : Good ρ nestL cur → Good ρ nestL h) :
    HWP P (gameHost (Verify.instOf recProperCheck) (consISpec consIx ρ nestL)) s
      ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 c)], mi⟩
      (vals [] ++ expression rpInner)
      (loopPost 0 [] (fun s' f vs => vs = [] ∧ RPInnerInv ρ s h mi s' f) (OPost ρ s h mi Q)) := by
  have hLo : Leaves (OPost ρ s h mi Q) s := hQ.loop
  have hL := hLo.loop (Inv := fun s' f vs => vs = [] ∧ RPInnerInv ρ s h mi s' f)
  have hS := rp_shape
  simp only [rpInner, rpAdvance, List.cons_append, List.nil_append]
  refine X.localGet (v := .i32 c) rfl ?_
  refine X.kind hS hs hm hL (fun k' hk => ?_)
  refine X.localSet (by simp [Idx.toNat]) ?_
  refine X.localGet (v := .i32 k') rfl ?_
  refine X.eqz ?_
  refine X.if_ (fun h0 => ?_) (fun h0 => ?_)
  · -- the element is finished: `cur := cdr(cur)`, continue the outer loop
    have hk0 : k' = 0 := by simpa using bool32_ne_zero h0
    have hnil : ρ c = some .nil := by
      rcases hk with ⟨-, hn⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hn
      · exact absurd hk0 (by decide)
      · exact absurd hk0 (by decide)
    have hxw : x ∈ wordsL := hx fun t ht => by
      rw [hnil] at ht
      cases ht
      exact ⟨[], rfl⟩
    refine X.localGet (v := .i32 cur) rfl ?_
    refine X.cdr hS hs hm hL.label (fun c' x' y' hcur' hc' => ?_)
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    rw [hcur] at hcur'
    obtain ⟨rfl, rfl⟩ := SExp2.cons.inj (Option.some.inj hcur')
    refine X.brN ⟨[], [], rfl, rfl, rfl, rfl, c', k', c, rfl, fun hg' => hg fun t ht => ?_⟩
    rw [hcur] at ht
    cases ht
    exact .cons (.inr hxw) (hg' _ hc')
  · refine X.localGet (v := .i32 k') rfl ?_
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hL.label _).1 _)) (fun h2 => ?_)
    have hk2 : k' = 2 := bne_eq_false_iff_eq.1 (bool32_eq_zero h2)
    refine X.localGet (v := .i32 c) rfl ?_
    refine X.car hS hs hm hL (fun e a b hc he => ?_)
    refine X.kind hS hs hm hL (fun k₂ hk₂ => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hL.label _).1 _)) (fun h1 => ?_)
    have hk1 : k₂ = 1 := bne_eq_false_iff_eq.1 (bool32_eq_zero h1)
    obtain ⟨w, hw⟩ : ∃ w, ρ e = some (.atom w) := by
      rcases hk₂ with ⟨rfl, -⟩ | ⟨-, hw⟩ | ⟨rfl, -⟩
      · exact absurd hk1 (by decide)
      · exact hw
      · exact absurd hk1 (by decide)
    obtain rfl : a = .atom w := Option.some.inj (he.symm.trans hw)
    refine X.localGet (v := .i32 c) rfl ?_
    refine X.cdr hS hs hm hL (fun c' a' b' hc' hcc => ?_)
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    rw [hc] at hc'
    obtain ⟨-, rfl⟩ := SExp2.cons.inj (Option.some.inj hc')
    refine X.br0 ⟨[], [], rfl, rfl, rfl, rfl, cur, k', c', x, y, rfl, hcur,
      fun hg' => hx fun t ht => ?_, hg⟩
    rw [hc] at ht
    cases ht
    exact wordsL_cons_atom (hg' _ hcc)

theorem rp_outer {cur k c : BitVec 32} (hg : Good ρ nestL cur → Good ρ nestL h) :
    HWP P (gameHost (Verify.instOf recProperCheck) (consISpec consIx ρ nestL)) s
      ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 c)], mi⟩
      (vals [] ++ expression rpOuter) (OPost ρ s h mi Q) := by
  have hL : Leaves (OPost ρ s h mi Q) s := hQ.loop
  have hS := rp_shape
  simp only [rpOuter, stepHead, rpAdvance, List.cons_append, List.nil_append]
  refine X.localGet (v := .i32 cur) rfl ?_
  refine X.kind hS hs hm hL (fun k' hk => ?_)
  refine X.localSet (by simp [Idx.toNat]) ?_
  refine X.localGet (v := .i32 k') rfl ?_
  refine X.eqz ?_
  refine X.if_ (fun h0 => ?_) (fun h0 => ?_)
  · have hk0 : k' = 0 := by simpa using bool32_ne_zero h0
    have hnil : ρ cur = some .nil := by
      rcases hk with ⟨-, hn⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hn
      · exact absurd hk0 (by decide)
      · exact absurd hk0 (by decide)
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.accept hS hs hm (hg fun t ht => ?_) hL.label ?_
    · rw [hnil] at ht
      cases ht
      exact .nil
    · exact X.return_ ((hL.label _).1 _)
  · refine X.localGet (v := .i32 k') rfl ?_
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hL.label _).1 _)) (fun h2 => ?_)
    refine X.localGet (v := .i32 cur) rfl ?_
    refine X.car hS hs hm hL (fun e x y hcur he => ?_)
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    refine X.localGet (v := .i32 e) rfl ?_
    refine X.kind hS hs hm hL (fun k₂ hk₂ => ?_)
    refine X.eqConst ?_
    refine X.if_ (fun h1 => ?_) (fun h1 => ?_)
    · -- an atom element: `cur := cdr(cur)`, continue the outer loop
      have hk1 : k₂ = 1 := beq_iff_eq.1 (bool32_ne_zero h1)
      obtain ⟨w, hw⟩ : ∃ w, ρ e = some (.atom w) := by
        rcases hk₂ with ⟨rfl, -⟩ | ⟨-, hw⟩ | ⟨rfl, -⟩
        · exact absurd hk1 (by decide)
        · exact hw
        · exact absurd hk1 (by decide)
      obtain rfl : x = .atom w := Option.some.inj (he.symm.trans hw)
      refine X.localGet (v := .i32 cur) rfl ?_
      refine X.cdr hS hs hm hL.label (fun c' x' y' hcur' hc' => ?_)
      refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
      rw [hcur] at hcur'
      obtain ⟨-, rfl⟩ := SExp2.cons.inj (Option.some.inj hcur')
      refine X.brN ⟨[], [], rfl, rfl, rfl, rfl, c', k', e, rfl, fun hg' => hg fun t ht => ?_⟩
      rw [hcur] at ht
      cases ht
      exact .cons (nestElem_atom w) (hg' _ hc')
    · -- otherwise the inner loop
      exact X.loop (Inv := RPInnerInv ρ s h mi)
        (fun s' f hI => by
          obtain ⟨rfl, cur', k'', c'', x', y', rfl, hcur', hx', hg'⟩ := hI
          exact rp_inner hs hm hQ hcur' hx' hg')
        ⟨rfl, cur, k', e, x, y, rfl, hcur, fun hge => hge _ he, hg⟩

end Loops

/-- **`recProperCheck` meets the cons reader specification for `nestL`** in every environment
and every profile. -/
theorem recProperCheck_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf recProperCheck) (StoreInv (Verify.instOf recProperCheck))
      (consISpec consIx ρ nestL) (topISpec _) :=
  gameSat_of rp_shape fun fi s h Q _ hm hs hQ => by
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.localSet (by simp [Idx.toNat]) ?_
    exact X.loop (Inv := RPOuterInv ρ s h fi.module)
      (fun s' f hI => by
        obtain ⟨rfl, cur, k, c, rfl, hg⟩ := hI
        exact rp_outer hs hm hQ hg) ⟨rfl, h, 0, 0, rfl, id⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
