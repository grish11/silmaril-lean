module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.CategoryTests

open CategoryTheory
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.Structural.Finite (Context Shape StructuralContext Types)
open LetCase.Structural.Reply (Γ₀ run)
open LetCase.LocallyNameless (Derivation Equiv)
open LetSeq.StraightLine.Structural (Log Trace model)
open Silmaril.Semantics.NondeterministicTrace (Finite)
open Isotope.Semantics (BoundEnv)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

set_option backward.isDefEq.respectTransparency false

private inductive Op | first | middle | last

private abbrev bitShape : Shape := .sum .unit .unit
private abbrev Bit := bitShape.ty
private abbrev captures : Context 1 := .snoc .nil Bit
private abbrev exits : LCtx Types := [.unit, .unit]
private abbrev Packet := packedExitType exits
private abbrev Source := captures.snoc Packet

local instance : LetCase.Structural.Finite.Signature Op where
  source _ := .pair bitShape bitShape
  target _ := bitShape

private def call (f : Op) {A : Types} : Operand Op (Source.snoc A) Bit :=
  ⟨.op f (.pair (.bv 2) (.case (.bv 1) (.inl .unit) (.inr .unit))),
    .op (.pair .bv (.case .bv (.inl .unit) (.inr .unit)))⟩

private def first : CheckedTable Op Source exits :=
  ⟨0, ⟨fun _ => .unit, fun _ => .case (call .first) (.exit (i := 0) rfl) (.exit (i := 1) rfl)⟩,
    rfl, ⟨.unit, .unit⟩⟩

private def middleTable (cycle : Bool) : Table Op Source exits 2 where
  types := ![Ty.unit, Bit, Ty.unit]
  block := fun i => Fin.cases
    (motive := fun j => Block Op Source ![Ty.unit, Bit, Ty.unit] exits (![Ty.unit, Bit, Ty.unit] j))
    (.jump (call .middle) (.local 1))
    (Fin.cases
      (motive := fun j : Fin 2 => Block Op Source ![Ty.unit, Bit, Ty.unit] exits (![Ty.unit, Bit, Ty.unit] j.succ))
      (.case ⟨.bv 0, .bv⟩ (.exit (i := 1) rfl) (.exit (i := 0) rfl))
      (fun _ => if cycle then .jump ⟨.unit, .unit⟩ (.local 2) else .jump ⟨.inl .unit, .inl .unit⟩ (.local 1))) i

private def middle : CheckedTable Op Source exits := ⟨2, middleTable false, rfl, ⟨.unit, .unit⟩⟩

private def last : CheckedTable Op Source exits :=
  ⟨0, ⟨fun _ => Bit, fun _ => .case (call .last) (.exit (i := 0) rfl) (.exit (i := 1) rfl)⟩,
    rfl, ⟨.inl .unit, .inl .unit⟩⟩

private theorem input : StructuralContext captures := .snoc .nil bitShape

private def left : CheckedTable Op Source exits := seq (seq first middle) last
private def right : CheckedTable Op Source exits := seq first (seq middle last)

/-- Both associations check globally, including the unentered middle row five. -/
example : left.table.check = true ∧ right.table.check = true := ⟨rfl, rfl⟩
example : (List.finRange 9).map left.table.localTargets = [[1, 2], [3], [3], [4], [7, 6], [4], [8], [8], []] := rfl
example : (List.finRange 9).map right.table.localTargets = [[1, 2], [3], [3], [4], [7, 6], [4], [8], [8], []] := rfl

/-- A self-loop in that unreachable row is rejected by the raw written link. -/
example :
    let r := (BoundCtx.Renaming.succ captures Packet).up Packet
    (Link.Open.table first.table (Link.Open.renameTable r (middleTable true)) 0 ⟨.unit, .unit⟩).check = false :=
  rfl

example : ReplayEqv false Source.toList (left.table.packedSSA 0 left.entry)
    (right.table.packedSSA 0 right.entry) [Packet] :=
  associative_replay input first middle last

private def obj : Interface Op captures input := ⟨exits, List.cons_ne_nil _ _⟩

private def arrow (p : CheckedTable Op Source exits) : obj ⟶ obj := Quotient.mk _ p

example : arrow first ≫ arrow middle = arrow (seq first middle) := by
  change seqClass input (⟦first⟧ : Hom Op captures exits exits) ⟦middle⟧ = ⟦seq first middle⟧
  exact seqClass_mk input first middle

example : arrow first ≫ 𝟙 obj = arrow first := Category.comp_id _
example : (arrow first ≫ arrow middle) ≫ arrow last = arrow first ≫ (arrow middle ≫ arrow last) :=
  Category.assoc _ _ _

local notation "Val" => LetCase.Structural.Finite.Value

private def ambient : BoundEnv Val captures := (BoundEnv.snoc (β := .nil) (fun i => i.elim0) (.inr PUnit.unit))

private def tag : Val Bit → Val Packet
  | .inl x => .inl x
  | .inr x => .inr (.inl x)

private def getBit : Val Packet → Val Bit
  | .inl _ => .inl PUnit.unit
  | .inr _ => .inr PUnit.unit

private def swapTag : Val Bit → Val Packet
  | .inl x => .inr (.inl x)
  | .inr x => .inl x

private def request (f : Op) (x : Val Packet) : Trace Empty Op (Val Bit) :=
  model.eval f (ambient 0, getBit x)

private def expected (x : Val Packet) : Trace Empty Op (Val Packet) :=
  request .first x >>= fun a =>
  request .middle (tag a) >>= fun b =>
  request .last (swapTag b) >>= fun c => pure (tag c)

private theorem run_first (x : Val Packet) :
    run first.toLetCase.2 (ambient.snoc x) = (request .first x >>= fun a => pure (tag a)) := by
  unfold CheckedTable.toLetCase Table.toLetCase Table.toFiniteExit
  rw [Table.compileAt.eq_def]
  simp only [first, Block.compile, Target.compile, FiniteExit.encode, Code.toLetCase, call, Scope.operand,
    Derivation.rename, run, Derivation.denote, pure_bind, bind_assoc]
  simp only [exits, FiniteExit.tag, Derivation.denote, pure_bind]
  cases x <;>
    (conv_lhs =>
      arg 1
      first
      | change (pure (.inl PUnit.unit) : Trace Empty Op (Val Bit))
      | change (pure (.inr PUnit.unit) : Trace Empty Op (Val Bit)))
  all_goals
    simp only [pure_bind, request, getBit]
    congr 1
    funext v
    cases v <;> rfl

private theorem run_middle (x : Val Packet) :
    run middle.toLetCase.2 (ambient.snoc x) = (request .middle x >>= fun b => pure (swapTag b)) := by
  unfold CheckedTable.toLetCase Table.toLetCase Table.toFiniteExit
  rw [Table.compileAt.eq_def]
  change run (FiniteExit.join (.br middle.entry)
    (.join (.br ((Scope.base : Scope Source Source).operand (call (A := Ty.unit) .middle)))
      (middle.table.compileAt middle.checked 1 (.skip .base Ty.unit)))).encode.toLetCase.2
      (ambient.snoc x) = _
  rw [Table.compileAt.eq_def, show middle.table.block 1 =
    .case ⟨.bv 0, .bv⟩ (.exit (i := 1) rfl) (.exit (i := 0) rfl) from rfl]
  simp only [middle, Block.compile, Target.compile,
    FiniteExit.encode, Code.toLetCase, call, Scope.operand, Derivation.rename, run, Derivation.denote,
    pure_bind, bind_assoc]
  simp only [exits, FiniteExit.tag, Derivation.denote, pure_bind]
  cases x <;>
    (conv_lhs =>
      arg 1
      first
      | change (pure (.inl PUnit.unit) : Trace Empty Op (Val Bit))
      | change (pure (.inr PUnit.unit) : Trace Empty Op (Val Bit)))
  all_goals
    simp only [pure_bind, request, getBit]
    congr 1
    funext v
    cases v <;> rfl

private theorem run_last (x : Val Packet) :
    run last.toLetCase.2 (ambient.snoc x) = (request .last x >>= fun c => pure (tag c)) := by
  unfold CheckedTable.toLetCase Table.toLetCase Table.toFiniteExit
  rw [Table.compileAt.eq_def]
  simp only [last, Block.compile, Target.compile, FiniteExit.encode, Code.toLetCase, call, Scope.operand,
    Derivation.rename, run, Derivation.denote, pure_bind, bind_assoc]
  simp only [exits, FiniteExit.tag, Derivation.denote, pure_bind]
  cases x <;>
    (conv_lhs =>
      arg 1
      first
      | change (pure (.inl PUnit.unit) : Trace Empty Op (Val Bit))
      | change (pure (.inr PUnit.unit) : Trace Empty Op (Val Bit)))
  all_goals
    simp only [pure_bind, request, getBit]
    congr 1
    funext v
    cases v <;> rfl

/-- These are equalities of the whole ordered traces, retaining every typed
reply and final tag from both actual emitters. -/
private theorem left_run (x : Val Packet) : run left.toLetCase.2 (ambient.snoc x) = expected x := by
  simp only [left, seq_run, run_first, run_middle, run_last, bind_assoc, pure_bind, expected]

private theorem right_run (x : Val Packet) : run right.toLetCase.2 (ambient.snoc x) = expected x := by
  simp only [right, seq_run, run_first, run_middle, run_last, bind_assoc, pure_bind, expected]

private def event (f : Op) (x : Val Packet) (reply : Val Bit) : Log Empty Op :=
  FreeMonoid.of ⟨f, (ambient 0, getBit x), reply⟩

private abbrev low : Val Bit := .inl PUnit.unit
private abbrev high : Val Bit := .inr PUnit.unit

private def path (x : Val Packet) : Log Empty Op :=
  event .first x high * (event .middle (tag high) low * event .last (swapTag low) (getBit x))

private theorem chosen (x : Val Packet) : (tag (getBit x), path x) ∈ (expected x).outcomes :=
  Finite.mem_bind.mpr ⟨high, _, _, ⟨high, rfl⟩, Finite.mem_bind.mpr
    ⟨low, _, _, ⟨low, rfl⟩, Finite.mem_bind.mpr ⟨getBit x, _, 1, ⟨getBit x, rfl⟩, rfl, mul_one _⟩, rfl⟩, rfl⟩

/-- A selected three-request path keeps the two unit-payload tags distinct.
The event arguments include the old capture and the actual stage input. -/
example : (tag low, path (tag low)) ∈ (run left.toLetCase.2 (ambient.snoc (tag low))).outcomes ∧
    (tag high, path (tag high)) ∈ (run right.toLetCase.2 (ambient.snoc (tag high))).outcomes := by
  rw [left_run, right_run]
  exact ⟨chosen (tag low), chosen (tag high)⟩

/-- The composition square uses the actual category operation and the
literal native let after emission. -/
example : interfaceHomEquiv input obj obj (arrow first ≫ arrow middle) =
    Case.seqClass (interfaceHomEquiv input obj obj (arrow first))
      (interfaceHomEquiv input obj obj (arrow middle)) :=
  interfaceHomEquiv_comp input (arrow first) (arrow middle)

example : interfaceHomEquiv input obj obj (𝟙 obj) = Case.identity :=
  interfaceHomEquiv_id input obj

example : Equiv false Γ₀ Source (seq first middle).toLetCase.1
    (Case.seq first.toLetCase middle.toLetCase).1 Packet :=
  emit_seq_equiv input first middle

/-- Start from a native term reading the old capture and both input tags.
Its checked inverse is constructed from its actual derivation. -/
private def direct : Operand Op Source Packet :=
  ⟨.let₁ (.op .last (.pair (.bv 1) (.case (.bv 0) (.inl .unit) (.inr .unit))))
    (.case (.bv 0) (.inl (.bv 0)) (.inr (.inl (.bv 0)))),
    .let₁ (.op (.pair .bv (.case .bv (.inl .unit) (.inr .unit))))
      (.case .bv (.inl .bv) (.inr (.inl .bv)))⟩

private theorem directOutput : exits ≠ [] := List.cons_ne_nil _ _

private def rebuilt : CheckedTable Op Source exits :=
  CheckedTable.ofLetCase directOutput direct.2

example : rebuilt.table.check = true := rfl

example : emitClass input (Quotient.mk _ rebuilt) = (Quotient.mk _ direct : Case.Hom Op captures exits exits) := by
  rw [rebuilt, ← Case.readbackClass_mk directOutput direct]
  exact emit_readback input directOutput (Quotient.mk _ direct)

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.CategoryTests
