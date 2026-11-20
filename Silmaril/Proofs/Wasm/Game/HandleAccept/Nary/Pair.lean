module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.Nary.Basic

/-!
# `pairCheck` meets its specification

`pairCheck_sat`: in every environment `ρ` and every profile, the instance of `pairCheck`
(`Silmaril.Wasm.Game.HandleAccept.Nary.Examples`) meets the n-ary reader specification for
`pairL` (two-element lists) with the store invariant `StoreInv`. Straight-line code: `kind`
answers list and `count` answers two, so the handle denotes `SExp.ofList [a, b]`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Nary

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Logic.Hoare Silmaril.Wasm.Logic.GameLink
  Silmaril.Formats Silmaril.Wasm.Game.HandleAccept
  Silmaril.Wasm.Game.HandleAccept.Nary Silmaril.Wasm.Game.HandleAccept.Nary.Examples
  Silmaril.Proofs.Wasm.Game.HandleAccept.Checkers

/-- The body of `pairCheck`'s function. -/
def pairBody : List Instr :=
  [.localGet ⟨0⟩, .call ⟨0⟩, .intConst .i32 1, .intRelOp .i32 .ne, .if_ .empty [.return_] [],
   .localGet ⟨0⟩, .call ⟨1⟩, .intConst .i32 2, .intRelOp .i32 .ne, .if_ .empty [.return_] [],
   .localGet ⟨0⟩, .call ⟨4⟩]

theorem pair_shape : GShape (Verify.instOf pairCheck) sxFTs aFT [] pairBody [] :=
  GShape.of_ok (by decide +kernel)

/-- **`pairCheck` meets the n-ary reader specification for `pairL`** in every environment and
every profile. -/
theorem pairCheck_sat (P : Profile)
    (ρ : Silmaril.Accept.Handle.Env (BitVec 32) (SExp (BitVec 64))) :
    GameSat P (Verify.instOf pairCheck) (StoreInv (Verify.instOf pairCheck))
      (sexpISpec pairIx ρ pairL) (topISpec _) :=
  gameSat_ofG pair_shape rfl fun fi s args Q ht _ hm hs hQ hQn => by
    obtain ⟨h, rfl⟩ := args_aFT ht
    have hS := pair_shape
    simp only [pairBody]
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.sxKind hS hs hm hQ (fun c _ => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun _ => ?_)
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.sxCount hS hs hm hQ (fun c cs hcs hlen => ?_)
    refine X.neConst ?_
    refine X.if_ (fun _ => X.return_ ((hQ.label _).1 _)) (fun h2 => ?_)
    have hc2 : c = 2 := bne_eq_false_iff_eq.1 (bool32_eq_zero h2)
    subst hc2
    have hl : cs.length = 2 := hlen
    refine X.localGet (v := .i32 h) rfl ?_
    refine X.sxAccept hS hs hm (fun t ht' => ?_) hQ (X.done (hQn _))
    rw [hcs] at ht'
    cases ht'
    match cs, hl with
    | [a, b], _ => exact ⟨a, b, rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Nary
