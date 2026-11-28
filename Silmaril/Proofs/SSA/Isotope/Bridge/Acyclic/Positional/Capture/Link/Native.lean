module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Link.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link

open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.Structural.Finite (StructuralContext)
open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Reply (Γ₀)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ] {d : Nat}
  {β : BoundCtx (Ty Empty) d} {L : LCtx (Ty Empty)}

theorem identity_equiv_proof (h : L ≠ [])
    (ok : (identityTable (Φ := Φ) (β := β) h).check = true) (packet : Operand Φ β (packedExitType L)) :
    Equiv false Γ₀ β ((identityTable h).toLetCase ok 0 packet).1 packet.1 (packedExitType L) := by
  unfold Table.toLetCase Table.toFiniteExit
  rw [show (identityTable h).compileAt ok 0 .base = (identityTree h).render .base
    from Reverse.Tree.build_compile (identityTree h) .empty .base]
  cases L with
  | nil => exact (h rfl).elim
  | cons X R =>
    exact (Equiv.let₁ (.refl packet.2.toHasType)
      (Reverse.decoder_repack false (rfl : At (X :: R) 0 X) (.base : Scope β β))).trans
      (Equiv.letEta packet.2.toHasType)

/-- Receiving a packet via the written identity emits the native bound
variable at the actual input interface. -/
theorem identity_continuation_proof (h : L ≠ [])
    (ok : (identityTable (Φ := Φ) (β := β) h).check = true) :
    Equiv false Γ₀ (β.snoc (packedExitType L))
      (continuation (L := L) (identityTable (Φ := Φ) (β := β) h) 0 ⟨.bv 0, .bv⟩ ok).1
      (.bv 0) (packedExitType L) := by
  unfold continuation
  rw [Reverse.tableTree_render]
  rw [show (identityTable h).compileAt ok 0 (.skip .base (packedExitType L)) =
    (identityTree h).render (.skip .base (packedExitType L))
    from Reverse.Tree.build_compile (identityTree h) .empty _]
  cases L with
  | nil => exact (h rfl).elim
  | cons X R =>
    exact (Equiv.let₁ (.refl .bv)
      (Reverse.decoder_repack false (rfl : At (X :: R) 0 X) (.skip (.base : Scope β β) _))).trans
      (Equiv.letEta .bv)

theorem checked_congr_proof {K : LCtx (Ty Empty)} (input : StructuralContext β)
    {p₁ p₂ : CheckedTable Φ β L} (x y : CheckedTable Φ β K)
    {r₁ r₂ : Operand Φ (β.snoc (packedExitType L)) (packedExitType K)}
    (left : (Reverse.checkedSetoid Φ β L).r p₁ p₂)
    (right : (Reverse.operandSetoid Φ (β.snoc (packedExitType L)) K).r r₁ r₂)
    (hx : Equiv false Γ₀ β x.toLetCase.1 (bind p₁.toLetCase r₁).1 (packedExitType K))
    (hy : Equiv false Γ₀ β y.toLetCase.1 (bind p₂.toLetCase r₂).1 (packedExitType K)) :
    (Reverse.checkedSetoid Φ β K).r x y := by
  have eq := p₁.table.equiv_of_packed_replay p₂.table p₁.checked p₂.checked 0 0 p₁.entry p₂.entry input left
  exact (x.table.packed_replay_iff_equiv_finite y.table x.checked y.checked 0 0 x.entry y.entry input).mpr
    (hx.trans ((Equiv.let₁ eq right).trans hy.symm))

theorem operandClass_identity_proof (h : L ≠ [])
    (ok : (identityTable (Φ := Φ) (β := β) h).check = true)
    (operand : Quotient (Reverse.operandSetoid Φ β L)) :
    operandClass (L := L) (continuation (L := L) (identityTable h) 0 ⟨.bv 0, .bv⟩ ok) operand = operand :=
  Quotient.inductionOn operand fun packet =>
    Quotient.sound ((Equiv.let₁ (.refl packet.2.toHasType) (identity_continuation_proof h ok)).trans
      (Equiv.letEta packet.2.toHasType))

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Link
