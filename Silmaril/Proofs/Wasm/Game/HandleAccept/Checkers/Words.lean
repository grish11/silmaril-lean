module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Proper

/-!
# `wordsCheck` meets its specification

`wordsCheck_sat`: in every environment `ρ` and every profile, the instance of `wordsCheck`
meets the cons reader specification for `wordsL` (proper lists of words) with the store
invariant `StoreInv`. Loop invariant: the locals are `[h, cur, k, e]` and if `cur` denotes a
list of words (or nothing) then so does `h`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- The body of `wordsCheck`'s function. -/
def wordsBody : List Instr :=
  [.localGet ⟨0⟩, .localSet ⟨1⟩, .loop .empty (stepHead ++ elemAtom ++ stepTail)]

theorem words_shape : Shape (Verify.instOf wordsCheck) [.i32, .i32, .i32] wordsBody
    [some (.i32 0), some (.i32 0), some (.i32 0)] :=
  Shape.of_ok (by decide +kernel)

variable {P : Profile} {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))}

/-- The loop invariant. -/
def WordsInv (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (s₀ : Store Nat)
    (h : BitVec 32) (mi : ModuleInst) (s : Store Nat) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ cur k e : BitVec 32,
    f = ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e)], mi⟩ ∧
    (Good ρ wordsL cur → Good ρ wordsL h)

theorem words_loop {s : Store Nat} (hs : s.funcs = (Verify.instOf wordsCheck).store.funcs)
    {mi : ModuleInst} (hm : mi.funcs = [0, 1, 2, 3, 4, 5]) {h cur k e : BitVec 32} {Q : Post Nat}
    (hQ : Leaves Q s) (hg : Good ρ wordsL cur → Good ρ wordsL h) :
    HWP P (gameHost (Verify.instOf wordsCheck) (consISpec consIx ρ wordsL)) s
      ⟨[some (.i32 h), some (.i32 cur), some (.i32 k), some (.i32 e)], mi⟩
      (vals [] ++ expression (stepHead ++ elemAtom ++ stepTail))
      (loopPost 0 [] (fun s' f vs => vs = [] ∧ WordsInv ρ s h mi s' f) Q) := by
  have hL := hQ.loop (Inv := fun s' f vs => vs = [] ∧ WordsInv ρ s h mi s' f)
  have hS := words_shape
  simp only [stepHead, elemAtom, stepTail, List.cons_append, List.nil_append]
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
    refine X.accept hS hs hm (hg fun t ht => ?_) hL.label ?_
    · rw [hnil] at ht
      cases ht
      exact ⟨[], rfl⟩
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
    have hc1 : c₂ = 1 := bne_eq_false_iff_eq.1 (bool32_eq_zero h1)
    obtain ⟨w, hw⟩ : ∃ w, ρ e' = some (.atom w) := by
      rcases hc₂ with ⟨rfl, -⟩ | ⟨-, hw⟩ | ⟨rfl, -⟩
      · exact absurd hc1 (by decide)
      · exact hw
      · exact absurd hc1 (by decide)
    obtain rfl : x = .atom w := Option.some.inj (he'.symm.trans hw)
    refine X.localGet (v := .i32 cur) rfl ?_
    refine X.cdr hS hs hm hL (fun c' x' y' hcur' hc' => ?_)
    refine X.localSet (by simp [Frame.setLocal, Idx.toNat]) ?_
    refine X.br0 ⟨[], [], rfl, rfl, rfl, rfl, c', c, e', rfl, fun hg' => hg fun t ht => ?_⟩
    rw [hcur] at hcur'
    obtain ⟨-, rfl⟩ := SExp2.cons.inj (Option.some.inj hcur')
    rw [hcur] at ht
    cases ht
    obtain ⟨ws, rfl⟩ := hg' _ hc'
    exact ⟨w :: ws, rfl⟩

/-- **`wordsCheck` meets the cons reader specification for `wordsL`** in every environment
and every profile. -/
theorem wordsCheck_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf wordsCheck) (StoreInv (Verify.instOf wordsCheck))
      (consISpec consIx ρ wordsL) (topISpec _) :=
  gameSat_of words_shape fun fi s h Q _ hm hs hQ => by
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.localSet (by simp [Idx.toNat]) ?_
    exact X.loop (Inv := WordsInv ρ s h fi.module)
      (fun s' f hI => by
        obtain ⟨rfl, cur, k, e, rfl, hg⟩ := hI
        exact words_loop hs hm hQ hg) ⟨rfl, h, 0, 0, rfl, id⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
