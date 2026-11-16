module

public import Silmaril.Wasm.Abstract.HostReachXP.Defs
public import Silmaril.Wasm.Abstract.HostClosingXP.Thms
public import Silmaril.Games.Abstract.CloseReach.Thms

/-!
# The canonical closure with reach (proofs)

Every reach is already a prefix of a cut behaviour of `wasmHOpenXP` (`reachLXP_cut`), so
`Shape.closeR_eq_close` applies.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostReachXP

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

variable {H : Type}

theorem reachXP_syn (x : (wasmHShape H).self.Op) (u : List (HCall H))
    (z : (wasmHShape H).self.Op) (h : reachXP x u z) :
    ∃ w ∈ wasmHOpenXP x.1 x.2.2 x.2.1, ∃ ans rest, w.1 = u ++ ⟨.inr z, ans⟩ :: rest := by
  obtain ⟨fi, fn, l, hf, hcode, ⟨ps, rs, hty⟩, hr, rfl⟩ := h
  obtain ⟨ws, f', d⟩ := reachLXP_cut hr
  refine ⟨((l ++ [OCall.mk z.1 z.2.1 z.2.2 (.inl ws) z.2.2]).map OCall.lift, endOfFlow .trap z.2.2),
    Or.inl ⟨fi, fn, ps, rs, _, _, _, _, _, hf, hcode, hty, d, rfl, rfl⟩, (.inl ws, z.2.2), [], ?_⟩
  simp only [List.map_append, List.map_cons, List.map_nil, OCall.mk, OCall.lift]
  rfl

theorem closeR_eq : Shape.closeR (wasmHOpenXP (H := H)) reachXP = Shape.close wasmHOpenXP :=
  Shape.closeR_eq_close reachXP_syn

end Silmaril.Proofs.Wasm.Abstract.HostReachXP
