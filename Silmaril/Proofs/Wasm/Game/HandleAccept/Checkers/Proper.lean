module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers.Basic

/-!
# `properCheck` meets its specification

`properCheck_sat`: in every environment `ρ` and every profile, the instance of `properCheck`
meets the cons reader specification for `properL` (spine-proper lists) with the store
invariant `StoreInv`. Loop invariant: the locals are `[h, cur, k]` and if `cur` denotes a
spine-proper list (or nothing) then so does `h` (`Good`).

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Wasm.Game.HandleAccept Silmaril.Wasm.Game.HandleAccept.Checkers
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-- `h` denotes a member of `L`, if anything. -/
def Good (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64)))
    (L : Set (SExp2 (BitVec 64))) (h : BitVec 32) : Prop :=
  ∀ t, ρ h = some t → t ∈ L

/-- The body of `properCheck`'s function. -/
def properBody : List Instr := [.localGet ⟨0⟩, .localSet ⟨1⟩, .loop .empty (stepHead ++ stepTail)]

theorem proper_shape : Shape (Verify.instOf properCheck) [.i32, .i32] properBody
    [some (.i32 0), some (.i32 0)] :=
  Shape.of_ok (by decide +kernel)

variable {P : Profile} {ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))}

/-- The loop invariant. -/
def ProperInv (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) (s₀ : Store Nat)
    (h : BitVec 32) (mi : ModuleInst) (s : Store Nat) (f : Frame) : Prop :=
  s = s₀ ∧ ∃ cur k : BitVec 32, f = ⟨[some (.i32 h), some (.i32 cur), some (.i32 k)], mi⟩ ∧
    (Good ρ properL cur → Good ρ properL h)

theorem proper_loop {s : Store Nat} (hs : s.funcs = (Verify.instOf properCheck).store.funcs)
    {mi : ModuleInst} (hm : mi.funcs = [0, 1, 2, 3, 4, 5]) {h cur k : BitVec 32} {Q : Post Nat}
    (hQ : Leaves Q s) (hg : Good ρ properL cur → Good ρ properL h) :
    HWP P (gameHost (Verify.instOf properCheck) (consISpec consIx ρ properL)) s
      ⟨[some (.i32 h), some (.i32 cur), some (.i32 k)], mi⟩
      (vals [] ++ expression (stepHead ++ stepTail))
      (loopPost 0 [] (fun s' f vs => vs = [] ∧ ProperInv ρ s h mi s' f) Q) := by
  have hL := hQ.loop (Inv := fun s' f vs => vs = [] ∧ ProperInv ρ s h mi s' f)
  have hS := proper_shape
  simp only [stepHead, stepTail, List.cons_append, List.nil_append]
  refine X.localGet (v := .i32 cur) rfl ?_
  refine X.kind hS hs hm hL (fun c hc => ?_)
  refine X.localSet (by exact (by decide : (2 : Nat) < 3)) ?_
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
      exact .nil
    · exact X.return_ ((hL.label _).1 _)
  · refine X.localGet (v := .i32 c) rfl ?_
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hL.label _).1 _)) (fun h2 => ?_)
    refine X.localGet (v := .i32 cur) rfl ?_
    refine X.cdr hS hs hm hL (fun c' x y hcur hc' => ?_)
    refine X.localSet (by exact (by decide : (1 : Nat) < 3)) ?_
    refine X.br0 ⟨[], [], rfl, rfl, rfl, rfl, c', c, rfl, fun hg' => hg fun t ht => ?_⟩
    rw [hcur] at ht
    cases ht
    exact .cons x (hg' y hc')

/-- **`properCheck` meets the cons reader specification for `properL`** in every environment
and every profile. -/
theorem properCheck_sat (P : Profile) (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp2 (BitVec 64))) :
    GameSat P (Verify.instOf properCheck) (StoreInv (Verify.instOf properCheck))
      (consISpec consIx ρ properL) (topISpec _) :=
  gameSat_of proper_shape fun fi s h Q _ hm hs hQ => by
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.localSet (by exact (by decide : (1 : Nat) < 3)) ?_
    exact X.loop (Inv := ProperInv ρ s h fi.module)
      (fun s' f hI => by
        obtain ⟨rfl, cur, k, rfl, hg⟩ := hI
        exact proper_loop hs hm hQ hg) ⟨rfl, h, 0, rfl, id⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers
