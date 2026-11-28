module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Native.Comparison.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Syntactic.Thms
import Silmaril.Semantics.NondeterministicTrace.Finite.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.ComparisonTests
set_option backward.isDefEq.respectTransparency false

open LetCase.LocallyNameless (Equiv)
open LetCase.Structural.Finite (Shape StructuralContext Types)
open LetCase.Structural.Reply (Γ₀)
open Region (packedExitType)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

private inductive Op | choose | left | right | finish

private abbrev bitShape : Shape := .sum .unit .unit
private abbrev Bit : Types := bitShape.ty
private abbrev ambient : BoundCtx Types 1 := .snoc .nil Bit
private abbrev exits : List Types := [.unit, .unit]
private abbrev Result := packedExitType exits

local instance : LetCase.Structural.Finite.Signature Op where
  source _ := bitShape
  target
    | .choose => .sum bitShape bitShape
    | _ => bitShape

private abbrev packet (_ : Fin 4) : Types := Bit

private def forward (swapExits : Bool) : Table Op ambient exits 3 where
  types := packet
  block i := ![
    .case ⟨.op .choose (.bv 0), .op .bv⟩ (.local 1) (.local 2),
    .jump ⟨.op .left (.bv 1), .op .bv⟩ (.local 3),
    .jump ⟨.op .right (.bv 1), .op .bv⟩ (.local 3),
    .case ⟨.op .finish (.bv 0), .op .bv⟩
      (if swapExits then .exit (i := 1) rfl else .exit (i := 0) rfl)
      (if swapExits then .exit (i := 0) rfl else .exit (i := 1) rfl)
  ] i

private def backward : Table Op ambient exits 3 where
  types := packet
  block i := ![
    .case ⟨.op .finish (.bv 0), .op .bv⟩ (.exit (i := 0) rfl) (.exit (i := 1) rfl),
    .jump ⟨.op .right (.bv 1), .op .bv⟩ (.local 0),
    .case ⟨.op .choose (.bv 0), .op .bv⟩ (.local 3) (.local 1),
    .jump ⟨.op .left (.bv 1), .op .bv⟩ (.local 0)
  ] i

private theorem forwardOk (swapExits : Bool) : (forward swapExits).check = true := by
  cases swapExits <;> cbv
private theorem backwardOk : backward.check = true := by cbv

example : (List.finRange 4).map (forward false).localTargets = [[1, 2], [3], [3], []] := rfl
example : (List.finRange 4).map backward.localTargets = [[], [0], [3, 1], [0]] := rfl

private def input : Operand Op ambient Bit := ⟨.bv 0, .bv⟩
private def inputLet : Operand Op ambient Bit := ⟨.let₁ (.bv 0) (.bv 0), .let₁ .bv .bv⟩

private theorem context : StructuralContext ambient := .snoc .nil bitShape

private def finishRow (swapped : Bool) : FiniteExit Op exits ((ambient.snoc Bit).snoc Bit |>.snoc Bit) :=
  .case ⟨.op .finish (.bv 0), .op .bv⟩
    (if swapped then .br (i := 1) rfl ⟨.bv 0, .bv⟩ else .br (i := 0) rfl ⟨.bv 0, .bv⟩)
    (if swapped then .br (i := 0) rfl ⟨.bv 0, .bv⟩ else .br (i := 1) rfl ⟨.bv 0, .bv⟩)

private def body (swapped : Bool) : FiniteExit Op exits (ambient.snoc Bit) :=
  .case ⟨.op .choose (.bv 0), .op .bv⟩
    (.join (.br ⟨.op .left (.bv 2), .op .bv⟩) (finishRow swapped))
    (.join (.br ⟨.op .right (.bv 2), .op .bv⟩) (finishRow swapped))

private theorem forwardBody (swapExits : Bool) :
    (forward swapExits).compileAt (forwardOk swapExits) 0 .base = body swapExits := by
  have join (s : Scope ambient ((ambient.snoc Bit).snoc Bit)) :
      (forward swapExits).compileAt (forwardOk swapExits) 3 s = finishRow swapExits := by
    rw [Table.compileAt.eq_def]
    cases swapExits <;> rfl
  rw [Table.compileAt.eq_def]
  change FiniteExit.case _ ((forward swapExits).compileAt (forwardOk swapExits) 1 (.skip .base Bit))
     ((forward swapExits).compileAt (forwardOk swapExits) 2 (.skip .base Bit)) = _
  conv_lhs => arg 2; rw [Table.compileAt.eq_def]
  conv_lhs => arg 3; rw [Table.compileAt.eq_def]
  change FiniteExit.case _
    (.join (.br _) ((forward swapExits).compileAt (forwardOk swapExits) 3 (.skip (.skip .base Bit) Bit)))
    (.join (.br _) ((forward swapExits).compileAt (forwardOk swapExits) 3 (.skip (.skip .base Bit) Bit))) = _
  rw [join]
  rfl

private theorem backwardBody :
    backward.compileAt backwardOk 2 .base = body false := by
  have join (s : Scope ambient ((ambient.snoc Bit).snoc Bit)) :
      backward.compileAt backwardOk 0 s = finishRow false := by
    rw [Table.compileAt.eq_def]
    rfl
  rw [Table.compileAt.eq_def]
  change FiniteExit.case _ (backward.compileAt backwardOk 3 (.skip .base Bit))
    (backward.compileAt backwardOk 1 (.skip .base Bit)) = _
  conv_lhs => arg 2; rw [Table.compileAt.eq_def]
  conv_lhs => arg 3; rw [Table.compileAt.eq_def]
  change FiniteExit.case _
    (.join (.br _) (backward.compileAt backwardOk 0 (.skip (.skip .base Bit) Bit)))
    (.join (.br _) (backward.compileAt backwardOk 0 (.skip (.skip .base Bit) Bit))) = _
  rw [join]
  rfl

/-- The two layouts share a successor. Both arms read the older capture, and
the redundant let in one entry is compared by native LetCase let η. -/
private theorem emitted_equiv :
    Equiv false Γ₀ ambient ((forward false).toLetCase (forwardOk false) 0 inputLet).1
      (backward.toLetCase backwardOk 2 input).1 Result := by
  unfold Table.toLetCase Table.toFiniteExit
  rw [forwardBody, backwardBody]
  exact .let₁ (Equiv.letEta .bv) (.refl (body false).encode.toLetCase.2.toHasType)

/-- With the same entry operand, the graphs already replay natively via
their common reification. Their local positions still differ. -/
example : ReplayEqv false ambient.toList ((forward false).packedSSA 0 input) (backward.packedSSA 2 input) [Result] := by
  apply ((forward false).packed_replay_iff_reified backward (forwardOk false) backwardOk 0 2 input input).mpr
  unfold Table.toLetCase Table.toFiniteExit
  rw [forwardBody, backwardBody]
  exact .refl (((Code.ofLetCase ((Code.join (.br input) (body false).encode).toLetCase.2)).guardedSSA_valueBranches rfl).hasType)

example :
    ReplayEqv false ambient.toList ((forward false).packedSSA 0 inputLet) (backward.packedSSA 2 input) [Result] :=
  ((forward false).packed_replay_iff_equiv_finite backward (forwardOk false) backwardOk 0 2 inputLet input context).mpr
    emitted_equiv

open LambdaSSA.Semantics.Categorical (denoteRegion)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)

/-- The native LetCase derivation gives equality of the original packed
arrows in the existing ordered trace model, across the two layouts. -/
example :
    let := traceInstructions (α := Empty) (Φ := Op)
    denoteRegion (traceJ (α := Empty) (Φ := Op)) (traceTypes Empty)
        ((forward false).packedSSA_hasType 0 inputLet) =
      denoteRegion (traceJ (α := Empty) (Φ := Op)) (traceTypes Empty)
        (backward.packedSSA_hasType 2 input) :=
  ((forward false).packed_trace_iff_equiv backward (forwardOk false) backwardOk 0 2 inputLet input context).mpr
    emitted_equiv

open LetCase.LocallyNameless (Derivation Pure)
open LetCase.Structural.Reply (run run_prefix_determined)
open LetSeq.StraightLine.Structural (Log)
open Silmaril.Semantics.NondeterministicTrace.Finite (mem_bind)

private abbrev TraceValue := LetCase.Structural.Finite.Value

private def leftBit : TraceValue Bit := .inl ()
private def assignment : Isotope.Semantics.BoundEnv TraceValue ambient :=
  Isotope.Semantics.BoundEnv.snoc (D := TraceValue) (fun i : Fin 0 => i.elim0) leftBit

private def outcomeLog : Log Empty Op :=
  FreeMonoid.of ⟨.choose, leftBit, .inl leftBit⟩ *
    (FreeMonoid.of ⟨.left, leftBit, leftBit⟩ * FreeMonoid.of ⟨.finish, leftBit, .inl ()⟩)

private def rendered (swapped : Bool) :=
  (Code.join (.br input) (body swapped).encode).toLetCase

private theorem outcomes (swapped : Bool) :
    ((if swapped then Sum.inr (Sum.inl ()) else Sum.inl () : TraceValue Result), outcomeLog)
      ∈ (run (rendered swapped).2 assignment).outcomes := by
  cases swapped <;>
    simp [rendered, body, finishRow, input, Code.toLetCase, FiniteExit.encode, FiniteExit.tag, run, Derivation.denote]
  all_goals
    let model := LetSeq.StraightLine.Structural.model (α := Empty) (Φ := Op)
    refine (mem_bind (p := model.eval .choose leftBit)).mpr
      ⟨.inl leftBit, FreeMonoid.of ⟨.choose, leftBit, .inl leftBit⟩, _, ⟨.inl leftBit, rfl⟩, ?_, rfl⟩
    refine (mem_bind (p := model.eval .left leftBit)).mpr
      ⟨leftBit, FreeMonoid.of ⟨.left, leftBit, leftBit⟩, _, ⟨leftBit, rfl⟩, ?_, rfl⟩
    refine (mem_bind (p := model.eval .finish leftBit)).mpr
      ⟨.inl (), FreeMonoid.of ⟨.finish, leftBit, .inl ()⟩, 1, ⟨.inl (), rfl⟩, ?_, mul_one _⟩
    exact rfl

/-- The same typed replies and ordered requests deliver different results when
the shared join swaps its two unit-payload outward positions. -/
example :
    ¬ (let := traceInstructions (α := Empty) (Φ := Op)
       denoteRegion (traceJ (α := Empty) (Φ := Op)) (traceTypes Empty)
           ((forward true).packedSSA_hasType 0 input) =
         denoteRegion (traceJ (α := Empty) (Φ := Op)) (traceTypes Empty)
           (backward.packedSSA_hasType 2 input)) := by
  intro equal
  have h := ((forward true).packed_trace_iff_equiv backward (forwardOk true) backwardOk 0 2 input input context).mp equal
  unfold Table.toLetCase Table.toFiniteExit at h
  rw [forwardBody, backwardBody] at h
  have trace := (LetCase.Structural.Finite.equiv_iff_traceArrow_eq context (rendered true).2 (rendered false).2).mp h
  have pointwise := (LetCase.Structural.Reply.traceArrow_eq_iff_run _ _).mp trace assignment
  have left := outcomes false
  have right := outcomes true
  rw [pointwise] at right
  have conflict := (run_prefix_determined (rendered false).2 assignment left right List.prefix_rfl).1
  cases conflict

private def pureGuard : LetCase.LocallyNameless.Tm Empty Op 1 :=
  .case (.bv 0) (.inl .unit) (.inr .unit)

/-- Purity in LetCase can hold for an expression outside the SSA branch-value
grammar. The transported β premise covers such expressions. -/
example : Pure false pureGuard ∧ ¬ LambdaSSA.Tm.BranchValue ambient.toList (Morphism.CaseSSA.erase pureGuard) Bit :=
  ⟨.case .bv (.inl .unit) (.inr .unit), fun h => by cases h⟩

open Region.Paper.RetainedLet (returnOnce)
open Morphism.CaseSSA (erase erase_hasType)
local notation "CaseTerm" => LetCase.LocallyNameless.Tm Empty Op

/-- The continuation uses the argument again after the first request. -/
private def useTwice {n : Nat} : CaseTerm (n + 1) :=
  .let₁ (.op .left (.bv 0)) (.op .right (.bv 1))

private def useTwiceTyped {n : Nat} {β : BoundCtx Types n} :
    Derivation Op Γ₀ (β.snoc Bit) useTwice Bit :=
  .let₁ (.op .bv) (.op .bv)

/-- The exact guard from the old premise audit substitutes at both uses in
an effectful continuation. The proof uses unit and sum η directly. -/
example :
    ReplayEqv false ambient.toList (returnOnce (erase (.let₁ pureGuard useTwice)))
      (returnOnce (erase (useTwice.instantiate pureGuard))) [Bit] := by
  rw [Morphism.CaseSSA.erase_instantiate]
  exact unit_case_letBeta (Tm.HasType.var (i := 0) rfl) (erase_hasType (useTwiceTyped (β := ambient)).toHasType)

private abbrev nestedAmbient : BoundCtx Types 2 := ambient.snoc (Ty.product Bit Bit)

private def nestedGuard : CaseTerm 2 :=
  .let₂ (.bv 0) (.case (.case (.bv 1) (.inr .unit) (.inl .unit)) (.bv 1) (.bv 4))

private def nestedTyped : Derivation Op Γ₀ nestedAmbient nestedGuard Bit :=
  .let₂ .bv (.case (.case .bv (.inr .unit) (.inl .unit)) .bv .bv)

private noncomputable def nestedInlinedTyped :
    Derivation Op Γ₀ nestedAmbient (useTwice.instantiate nestedGuard) Bit :=
  Classical.choice (Derivation.ofHasType (useTwiceTyped.toHasType.instantiate nestedTyped.toHasType))

/-- A nested test below two field binders can return the second field or an
older capture. Pure let β reaches the actual guarded reifier at both ends. -/
example :
    let t := Derivation.let₁ nestedTyped useTwiceTyped
    let u := nestedInlinedTyped
    ReplayEqv false nestedAmbient.toList ((Code.ofLetCase t).guardedSSA 0) ((Code.ofLetCase u).guardedSSA 0) [Bit] :=
  reify_equiv_finite _ _
    (Equiv.letBeta (.let₂ .bv (.case (.case .bv (.inr .unit) (.inl .unit)) .bv .bv))
      nestedTyped.toHasType useTwiceTyped.toHasType)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.ComparisonTests
