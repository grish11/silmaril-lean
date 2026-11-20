module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Proper

/-!
# `sortedCheck` meets its specification

`sortedCheck_sat`: in every environment `ρ` and every profile, the instance of `sortedCheck`
meets the cons reader specification for `sortedL` (lists of words, non-decreasing in the signed
`i64` order) with the store invariant `StoreInv`. Loop invariant: the locals are
`[h, cur, k, e, w, p, b]`, and if `cur` denotes a sorted list of words all at least `p` when
`b ≠ 0` (`GoodS ρ (bound b p) cur`), then `h` denotes a sorted list of words.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- The body of `sortedCheck`'s function. -/
def sortedBody : List Instr :=
  [.localGet ⟨0⟩, .localSet ⟨1⟩, .loop .empty (stepHead ++ elemAtom ++ elemSorted ++ stepTail)]

theorem sorted_shape : Shape (Verify.instOf sortedCheck) [.i32, .i32, .i32, .i64, .i64, .i32]
    sortedBody [some (.i32 0), some (.i32 0), some (.i32 0), some (.i64 0), some (.i64 0),
      some (.i32 0)] :=
  Shape.of_ok (by decide +kernel)

/-- A sorted list of words, all at least `p` if `q = some p`. -/
def SortedFrom (q : Option (BitVec 64)) (t : SExp2 (BitVec 64)) : Prop :=
  ∃ ws, t = SExp2.ofAtoms ws ∧ ws.Pairwise (fun a b => a.sle b = true) ∧
    ∀ p, q = some p → ∀ w ∈ ws, p.sle w = true

/-- `c` denotes a sorted list of words bounded by `q`, if anything. -/
def GoodS (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))
    (q : Option (BitVec 64)) (c : BitVec 32) : Prop :=
  ∀ t, ρ c = some t → SortedFrom q t

/-- The lower bound recorded in the locals: the previous word, once there is one. -/
def bound (b : BitVec 32) (p : BitVec 64) : Option (BitVec 64) := if b = 0 then none else some p

theorem sle_trans {a b c : BitVec 64} (h₁ : a.sle b = true) (h₂ : b.sle c = true) :
    a.sle c = true := by
  simp only [BitVec.sle, decide_eq_true_eq] at *
  omega

/-- One more word in front. -/
theorem sortedFrom_cons {b : BitVec 32} {p w : BitVec 64} {y : SExp2 (BitVec 64)}
    (hle : b ≠ 0 → p.sle w = true) (h : SortedFrom (some w) y) :
    SortedFrom (bound b p) (.cons (.atom w) y) := by
  obtain ⟨ws, rfl, hs, hb⟩ := h
  refine ⟨w :: ws, rfl, List.pairwise_cons.2 ⟨hb w rfl, hs⟩, fun p' hp' a ha => ?_⟩
  unfold bound at hp'
  split_ifs at hp' with hb0
  obtain rfl := Option.some.inj hp'
  rcases List.mem_cons.1 ha with rfl | ha
  · exact hle hb0
  · exact sle_trans (hle hb0) (hb w rfl a ha)

variable {P : Profile} {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))}

/-- The loop invariant. -/
def SortedInv (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (s₀ : Store Nat)
    (h : BitVec 32) (mi : ModuleInst) (s : Store Nat) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ (cur k e : BitVec 32) (w p : BitVec 64) (b : BitVec 32),
    f = ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e), some (.i64 w),
      some (.i64 p), some (.i32 b)], mi⟩ ∧
    (GoodS ρ (bound b p) cur → GoodS ρ none h)

/-- After the comparison: record the word, read the tail, loop. -/
theorem sorted_tail {s : Store Nat} (hs : s.funcs = (Verify.instOf sortedCheck).store.funcs)
    {mi : ModuleInst} (hm : mi.funcs = [0, 1, 2, 3, 4, 5]) {h cur k e : BitVec 32}
    {w p : BitVec 64} {b : BitVec 32} {Q : Post Nat} {x y : SExp2 (BitVec 64)}
    (hQ : Leaves (loopPost 0 [] (fun s' f vs => vs = [] ∧ SortedInv ρ s h mi s' f) Q) s)
    (hg : GoodS ρ (bound b p) cur → GoodS ρ none h) (hcur : ρ cur = some (.cons x y))
    (hx : x = .atom w) (hle : b ≠ 0 → p.sle w = true) :
    HWP P (gameHost (Verify.instOf sortedCheck) (consISpec consIx ρ sortedL)) s
      ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e), some (.i64 w),
        some (.i64 p), some (.i32 b)], mi⟩
      (vals [] ++ expression [.localGet ⟨4⟩, .localSet ⟨5⟩, .intConst .i32 1, .localSet ⟨6⟩,
        .localGet ⟨1⟩, .call ⟨2⟩, .localSet ⟨1⟩, .br ⟨0⟩])
      (loopPost 0 [] (fun s' f vs => vs = [] ∧ SortedInv ρ s h mi s' f) Q) := by
  refine X.localGet (v := .i64 w) rfl ?_
  refine X.localSet (by simp [Idx.toNat]) ?_
  refine X.i32Const ?_
  refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
  refine X.localGet (v := .i32 cur) rfl ?_
  refine X.cdr sorted_shape hs hm hQ (fun c' x' y' hcur' hc' => ?_)
  refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
  refine X.br0 ⟨[], [], rfl, rfl, rfl, rfl, c', k, e, w, w, 1, rfl, fun hg' => hg fun t ht => ?_⟩
  rw [hcur] at hcur' ht
  obtain ⟨rfl, rfl⟩ := SExp2.cons.inj (Option.some.inj hcur')
  cases ht
  subst hx
  have hb1 : bound 1 w = some w := by simp [bound]
  exact sortedFrom_cons hle (hb1 ▸ hg' _ hc')

theorem sorted_loop {s : Store Nat} (hs : s.funcs = (Verify.instOf sortedCheck).store.funcs)
    {mi : ModuleInst} (hm : mi.funcs = [0, 1, 2, 3, 4, 5]) {h cur k e : BitVec 32}
    {w p : BitVec 64} {b : BitVec 32} {Q : Post Nat}
    (hQ : Leaves Q s) (hg : GoodS ρ (bound b p) cur → GoodS ρ none h) :
    HWP P (gameHost (Verify.instOf sortedCheck) (consISpec consIx ρ sortedL)) s
      ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e), some (.i64 w),
        some (.i64 p), some (.i32 b)], mi⟩
      (vals [] ++ expression (stepHead ++ elemAtom ++ elemSorted ++ stepTail))
      (loopPost 0 [] (fun s' f vs => vs = [] ∧ SortedInv ρ s h mi s' f) Q) := by
  have hL := hQ.loop (Inv := fun s' f vs => vs = [] ∧ SortedInv ρ s h mi s' f)
  have hS := sorted_shape
  simp only [stepHead, elemAtom, elemSorted, stepTail, List.cons_append, List.nil_append]
  refine X.localGet (v := .i32 cur) rfl ?_
  refine X.kind hS hs hm hL (fun c hc => ?_)
  refine X.localSet (by simp [Idx.toNat]) ?_
  refine X.localGet (v := .i32 c) rfl ?_
  refine X.eqz ?_
  refine X.if_ (fun h0 => ?_) (fun h0 => ?_)
  · have hc0 : c = 0 := by simpa using bool32_ne_zero h0
    have hnil : ρ cur = some .nil := by
      rcases hc with ⟨-, hn⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hn
      · exact absurd hc0 (by decide)
      · exact absurd hc0 (by decide)
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.accept hS hs hm (fun t ht => ?_) hL.label ?_
    · obtain ⟨ws, rfl, hws, -⟩ := hg (fun t ht' => by
        rw [hnil] at ht'
        cases ht'
        exact ⟨[], rfl, .nil, fun _ _ _ hw => absurd hw List.not_mem_nil⟩) t ht
      exact ⟨ws, rfl, hws⟩
    · exact X.return_ ((hL.label _).1 _)
  · refine X.localGet (v := .i32 c) rfl ?_
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hL.label _).1 _)) (fun _ => ?_)
    refine X.localGet (v := .i32 cur) rfl ?_
    refine X.car hS hs hm hL (fun e' x y hcur he' => ?_)
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    refine X.localGet (v := .i32 e') rfl ?_
    refine X.kind hS hs hm hL (fun c₂ hc₂ => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hL.label _).1 _)) (fun h1 => ?_)
    refine X.localGet (v := .i32 e') rfl ?_
    refine X.word hS hs hm hL (fun w' hw' => ?_)
    have hx : x = .atom w' := Option.some.inj (he'.symm.trans hw')
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    refine X.localGet (v := .i32 b) rfl ?_
    refine X.if_ (fun hb => ?_) (fun hb => ?_)
    · refine X.localGet (v := .i64 p) rfl ?_
      refine X.localGet (v := .i64 w') rfl ?_
      refine X.les64 (us := []) ?_
      refine X.eqz ?_
      refine X.if_ (fun _ => X.return_ ((hL.label.label _).1 _)) (fun hz => ?_)
      have hle : p.sle w' = true := by simpa [bool32] using hz
      exact X.blockEnd (sorted_tail hs hm hL hg hcur hx fun _ => hle)
    · exact sorted_tail hs hm hL hg hcur hx fun hb' => absurd hb hb'

/-- **`sortedCheck` meets the cons reader specification for `sortedL`** in every environment
and every profile. -/
theorem sortedCheck_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf sortedCheck) (StoreInv (Verify.instOf sortedCheck))
      (consISpec consIx ρ sortedL) (topISpec _) :=
  gameSat_of sorted_shape fun fi s h Q _ hm hs hQ => by
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.localSet (by simp [Idx.toNat]) ?_
    exact X.loop (Inv := SortedInv ρ s h fi.module)
      (fun s' f hI => by
        obtain ⟨rfl, cur, k, e, w, p, b, rfl, hg⟩ := hI
        exact sorted_loop hs hm hQ hg)
      ⟨rfl, h, 0, 0, 0, 0, 0, rfl, fun hg => by simpa [bound] using hg⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
