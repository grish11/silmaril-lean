module

import Silmaril.SSA.Isotope.LetSeq.StraightLine.Thms

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv Tm)
open Silmaril.Semantics.NondeterministicTrace

set_option backward.isDefEq.respectTransparency false

private abbrev Out : Types := .product Packet Packet

private def first : Term 1 := .op (.ask false) (.bv 0)
private def left : Term 1 := .op (.ask true) (.let₁ first (.bv 0))
private def mixed : Term 1 := .let₂ (.pair left first) (.pair (.bv 0) (.bv 1))

private def mixedTyping : Derivation Request Γ₀ input mixed Out :=
  .let₂ (.pair (.op (.let₁ (.op .bv) .bv)) (.op .bv)) (.pair .bv .bv)

-- The input is used whole, and both an operation argument and the operands
-- of a pair are effectful. Only the native typing is supplied.
example : ∃ u : Term 3, ∃ _ : ProductProgram ((input.snoc Atom).snoc Atom) u Out,
    Equiv false Γ₀ input mixed (.let₂ (.bv 0) u) Out :=
  packet_program mixedTyping

private def observedResult : Value Out := (((6 : Nat), (7 : Nat)), ((4 : Nat), (5 : Nat)))
private def receiveFirst : Log := FreeMonoid.of ⟨.ask false, (0, 1), (2, 3)⟩
private def receiveSecond : Log := FreeMonoid.of ⟨.ask true, (2, 3), (4, 5)⟩
private def receiveRight : Log := FreeMonoid.of ⟨.ask false, (0, 1), (6, 7)⟩

-- The nested argument runs first, the outer primitive receives its reply,
-- and the right operand starts only after both. Destructuring swaps the values.
example : (observedResult, receiveFirst * (receiveSecond * receiveRight)) ∈
    (run mixedTyping (packetEnv (0, 1))).outcomes := by
  simp only [mixedTyping, run, Derivation.denote, pure_bind, bind_assoc]
  apply mem_request_trace.mpr
  refine ⟨(2, 3), receiveSecond * receiveRight, ?_, rfl⟩
  apply mem_request_trace.mpr
  refine ⟨(4, 5), receiveRight, ?_, rfl⟩
  apply mem_request_trace.mpr
  exact ⟨(6, 7), 1, rfl, mul_one _⟩

end Silmaril.Isotope.LetSeq.StraightLine
