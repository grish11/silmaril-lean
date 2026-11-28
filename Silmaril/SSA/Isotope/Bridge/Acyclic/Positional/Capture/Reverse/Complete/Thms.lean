module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Complete.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Thms
public import Silmaril.SSA.Isotope.Bridge.Acyclic.FiniteExit.Thms
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Complete.Replay
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Reverse.Complete.EmptyInterface

/-! # Native inverses for the checked ranked realization -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse

open Region (packedExitType)
open LetCase.LocallyNameless (Derivation Equiv)

universe u v w

section General

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] {n : Nat} {β : BoundCtx τ n} {L : LCtx τ}
  {t : LetCase.LocallyNameless.Tm Empty Φ n}

local notation "Γ₀" => (Ctx.nil : Ctx Empty τ)

/-- The checked CFG emits a native LetCase equivalent of the original typed
term. The decoder inspects a bound result and reconstructs the same ordered tag. -/
theorem CheckedTable.ofLetCase_emit (pe : ε) (h : L ≠ [])
    (d : Derivation Φ Γ₀ β t (packedExitType L)) :
    Equiv pe Γ₀ β (CheckedTable.ofLetCase h d).toLetCase.1 t (packedExitType L) :=
  ofLetCase_emit_proof h d

/-- A checked decoder re-encodes its input's original tag in native LetCase.
The context may already carry older packets. -/
theorem decoder_repack (pe : ε) {m i : Nat} {γ : BoundCtx τ m} {D : τ}
    (fallback : At L i D) (s : Scope β γ) :
    Equiv pe Γ₀ (γ.snoc (packedExitType L))
      ((decoder (Φ := Φ) fallback L ExitSuffix.here).render s).encode.toLetCase.1
      (.bv 0) (packedExitType L) :=
  decoder_repack_proof fallback s

/-- A finite ranked table cannot have an empty outward interface. -/
theorem CheckedTable.exits_ne_nil (q : CheckedTable Φ β L) : L ≠ [] :=
  (q.table.toFiniteExit q.checked 0 q.entry).exits_ne_nil

end General

open LetCase.Structural.Finite (StructuralContext Context Types)
open LetCase.Structural.Reply (Γ₀)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [LetCase.Structural.Finite.Signature Φ]
  {d n : Nat} {β : Context d} {L : List Types} {t : LetCase.LocallyNameless.Tm Empty Φ d}

/-- At inhabited finite inputs, an exact packed result supplies a nonempty
outward interface. A finite request head always has an inhabited reply. -/
theorem exits_ne_nil_of_operand (input : StructuralContext β)
    (a : Operand Φ β (packedExitType L)) : L ≠ [] :=
  finite_exits_proof input a

/-- The finite constructor-input fragment has a total checked realization. -/
@[expose] def CheckedTable.ofFiniteLetCase (input : StructuralContext β) (a : Operand Φ β (packedExitType L)) :
    CheckedTable Φ β L :=
  CheckedTable.ofLetCase (exits_ne_nil_of_operand input a) a.2

/-- The literal written region of the constructed table, with its ordered
exits packed, replays to the actual guarded structured reification. -/
theorem CheckedTable.ofLetCase_packed_replay (h : L ≠ [])
    (d : Derivation Φ Γ₀ β t (packedExitType L)) :
    let q := CheckedTable.ofLetCase h d
    ReplayEqv false β.toList (q.table.packedSSA 0 q.entry) ((Code.ofLetCase d).guardedSSA 0) [packedExitType L] :=
  let q := CheckedTable.ofLetCase h d
  (q.table.toLetCase_reify q.checked 0 q.entry).trans
    (reify_equiv_finite q.toLetCase.2 d (CheckedTable.ofLetCase_emit false h d))

/-- Reconstruct any checked captured CFG from its emitted LetCase operand. -/
def reconstruct (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) : CheckedTable Φ β L :=
  CheckedTable.ofLetCase (p.toFiniteExit ok i a).exits_ne_nil (p.toLetCase ok i a).2

/-- Both CFGs use the same original ambient context and packed ordered
interface. Replay applies at the literal original and reconstructed endpoints. -/
theorem reconstruct_packed_replay (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) :
    let q := reconstruct p ok i a
    ReplayEqv false β.toList (p.packedSSA i a) (q.table.packedSSA 0 q.entry) [packedExitType L] :=
  (p.toLetCase_reify ok i a).trans
    (CheckedTable.ofLetCase_packed_replay (p.toFiniteExit ok i a).exits_ne_nil (p.toLetCase ok i a).2).symm

/-- Native equation classes of exact LetCase operands at one ordered interface. -/
@[expose] def operandSetoid (Φ : Type) [LetCase.Structural.Finite.Signature Φ] (β : Context d) (L : List Types) :
    Setoid (Operand Φ β (packedExitType L)) where
  r a b := Equiv false Γ₀ β a.1 b.1 (packedExitType L)
  iseqv := ⟨fun a => .refl a.2.toHasType, fun h => h.symm, fun h k => h.trans k⟩

/-- Checked tables modulo native replay at the literal packed endpoints. -/
@[expose] def checkedSetoid (Φ : Type) [LetCase.Structural.Finite.Signature Φ] (β : Context d) (L : List Types) :
    Setoid (CheckedTable Φ β L) where
  r p q := ReplayEqv false β.toList (p.table.packedSSA 0 p.entry) (q.table.packedSSA 0 q.entry) [packedExitType L]
  iseqv := ⟨fun p => .refl (p.table.packedSSA_hasType 0 p.entry), fun h => h.symm, fun h k => h.trans k⟩

private theorem realize_respects (input : StructuralContext β) {a b : Operand Φ β (packedExitType L)}
    (eq : (operandSetoid Φ β L).r a b) :
    (checkedSetoid Φ β L).r (CheckedTable.ofFiniteLetCase input a) (CheckedTable.ofFiniteLetCase input b) :=
  let p := CheckedTable.ofFiniteLetCase input a
  let q := CheckedTable.ofFiniteLetCase input b
  let left := CheckedTable.ofLetCase_emit false (exits_ne_nil_of_operand input a) a.2
  let right := CheckedTable.ofLetCase_emit false (exits_ne_nil_of_operand input b) b.2
  (p.table.packed_replay_iff_equiv_finite q.table p.checked q.checked 0 0 p.entry q.entry input).mpr
    (left.trans (eq.trans right.symm))

/-- At a fixed inhabited finite input and ordered exit interface, emission
and checked reconstruction are inverse maps on native equation classes.
Arbitrary checked entry positions are covered by the reconstruction replay theorem. -/
def nativeClassEquiv (input : StructuralContext β) :
    Quotient (checkedSetoid Φ β L) ≃ Quotient (operandSetoid Φ β L) where
  toFun := Quotient.map CheckedTable.toLetCase
    (fun {p q} h => p.table.equiv_of_packed_replay q.table p.checked q.checked 0 0 p.entry q.entry input h)
  invFun := Quotient.map (CheckedTable.ofFiniteLetCase input)
    (fun {a b} eq => realize_respects (a := a) (b := b) input eq)
  left_inv := fun q => Quotient.inductionOn q fun p =>
    Quotient.sound (reconstruct_packed_replay p.table p.checked 0 p.entry).symm
  right_inv := fun q => Quotient.inductionOn q fun a =>
    Quotient.sound (CheckedTable.ofLetCase_emit false (exits_ne_nil_of_operand input a) a.2)

theorem nativeClassEquiv_mk (input : StructuralContext β) (p : CheckedTable Φ β L) :
    nativeClassEquiv input (Quotient.mk _ p) = Quotient.mk _ p.toLetCase := by
  unfold nativeClassEquiv
  rfl

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Reverse
