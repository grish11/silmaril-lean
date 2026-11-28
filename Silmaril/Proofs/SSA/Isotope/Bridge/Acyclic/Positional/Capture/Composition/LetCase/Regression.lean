module

import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Thms

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.LetCaseTests

open CategoryTheory
open Region (packedExitType)
open Reverse (CheckedTable)
open LetCase.Structural.Finite (Context Shape StructuralContext Types equiv_iff_traceArrow_eq_snoc)
open LetCase.Structural.Reply (Γ₀ run traceArrow_eq_iff_run)
open LetCase.LocallyNameless (Derivation Equiv)
open LetSeq.StraightLine.Structural (Log Trace)
open Isotope.Semantics (BoundEnv)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural

private inductive Op | probe | mix

private abbrev bitShape : Shape := .sum .unit .unit
private abbrev Bit := bitShape.ty
private abbrev captures : Context 2 := .snoc (.snoc .nil Bit) Bit
private abbrev exits : LCtx Types := [.unit, .unit]
private abbrev Packet := packedExitType exits
private abbrev Source := captures.snoc Packet

local instance : LetCase.Structural.Finite.Signature Op where
  source _ := .pair bitShape bitShape
  target _ := bitShape

private theorem input : StructuralContext captures := .snoc (.snoc .nil bitShape) bitShape
private theorem nonempty : exits ≠ [] := List.cons_ne_nil _ _

/-! Native terms written directly. The packet is slot zero, above the newer
capture at slot one and the older capture at slot two. -/

/-- Ask with the newer capture and the input tag, and return the reply tag. -/
private def probe : Operand Op Source Packet :=
  ⟨.let₁ (.op .probe (.pair (.bv 1) (.case (.bv 0) (.inl .unit) (.inr .unit))))
    (.case (.bv 0) (.inl (.bv 0)) (.inr (.inl (.bv 0)))),
    .let₁ (.op (.pair .bv (.case .bv (.inl .unit) (.inr .unit))))
      (.case .bv (.inl .bv) (.inr (.inl .bv)))⟩

/-- Ask with the older capture and the input tag, and return the other tag. -/
private def mix : Operand Op Source Packet :=
  ⟨.let₁ (.op .mix (.pair (.bv 2) (.case (.bv 0) (.inl .unit) (.inr .unit))))
    (.case (.bv 0) (.inr (.inl (.bv 0))) (.inl (.bv 0))),
    .let₁ (.op (.pair .bv (.case .bv (.inl .unit) (.inr .unit))))
      (.case .bv (.inr (.inl .bv)) (.inl .bv))⟩

/-- Exchange the two same-payload tags without a request. -/
private def flip : Operand Op Source Packet :=
  ⟨.case (.bv 0) (.inr (.inl .unit)) (.inl .unit), .case .bv (.inr (.inl .unit)) (.inl .unit)⟩

/-! Checked graphs written directly, with one row each. -/

private def ask (f : Op) {A : Types} : Operand Op (Source.snoc A) Bit :=
  ⟨.op f (.pair (.bv 3) (.case (.bv 1) (.inl .unit) (.inr .unit))),
    .op (.pair .bv (.case .bv (.inl .unit) (.inr .unit)))⟩

private def straight : CheckedTable Op Source exits :=
  ⟨0, ⟨fun _ => .unit, fun _ => .case (ask .probe) (.exit (i := 0) rfl) (.exit (i := 1) rfl)⟩,
    rfl, ⟨.unit, .unit⟩⟩

private def crossed : CheckedTable Op Source exits :=
  ⟨0, ⟨fun _ => Bit, fun _ => .case (ask .mix) (.exit (i := 1) rfl) (.exit (i := 0) rfl)⟩,
    rfl, ⟨.inr .unit, .inr .unit⟩⟩

private def written : Interface Op captures input := ⟨exits, nonempty⟩
private def native : Case.Interface Op captures input := ⟨exits, nonempty⟩

private def graph (p : CheckedTable Op Source exits) : written ⟶ written := Quotient.mk _ p
private def term (a : Operand Op Source Packet) : native ⟶ native := Quotient.mk _ a

private def rebuilt (a : Operand Op Source Packet) : CheckedTable Op Source exits :=
  CheckedTable.ofLetCase nonempty a.2

/-! ## Composition in the native category -/

/-- The native composite is the class of the literal typed let. -/
example : term probe ≫ term mix = term (Case.seq probe mix) := Case.seqClass_mk probe mix

/-- The receiver is weakened below its bound input. Its older capture moves
from slot two to slot three and its input stays at slot zero. -/
example : (Case.seq probe mix).1 =
    .let₁ probe.1
      (.let₁ (.op .mix (.pair (.bv 3) (.case (.bv 0) (.inl .unit) (.inr .unit))))
        (.case (.bv 0) (.inr (.inl (.bv 0))) (.inl (.bv 0)))) :=
  rfl

example : (𝟙 native : native ⟶ native) = term ⟨.bv 0, .bv⟩ := rfl
example : 𝟙 native ≫ term mix = term mix := Category.id_comp _
example : term probe ≫ 𝟙 native = term probe := Category.comp_id _
example : (term probe ≫ term mix) ≫ term flip = term probe ≫ (term mix ≫ term flip) :=
  Category.assoc _ _ _

/-! ## From native terms to checked graphs and back -/

/-- The global rank checker evaluates to true on each rebuilt graph. -/
example : (rebuilt probe).table.check = true ∧ (rebuilt mix).table.check = true ∧
    (rebuilt (Case.seq probe mix)).table.check = true :=
  ⟨rfl, rfl, rfl⟩

example : (readbackFunctor input).map (term mix) = graph (rebuilt mix) :=
  Case.readbackClass_mk nonempty mix

example : (emitFunctor input).map ((readbackFunctor input).map (term mix)) = term mix :=
  emitFunctor_map_readbackFunctor_map input (term mix)

/-- At representatives, the graph built from the term emits a natively
equal term in the same older context. -/
example : Equiv false Γ₀ Source (rebuilt mix).toLetCase.1 mix.1 Packet :=
  CheckedTable.ofLetCase_emit false nonempty mix.2

/-! ## From checked graphs to native terms and back -/

example : (emitFunctor input).map (graph crossed) = term crossed.toLetCase :=
  emitClass_mk input crossed

example : (readbackFunctor input).map ((emitFunctor input).map (graph crossed)) = graph crossed :=
  readbackFunctor_map_emitFunctor_map input (graph crossed)

/-- At representatives, the graph rebuilt from the emitted term replays to
the original graph at its literal packed endpoints. -/
example : ReplayEqv false Source.toList
    ((rebuilt crossed.toLetCase).table.packedSSA 0 (rebuilt crossed.toLetCase).entry)
    (crossed.table.packedSSA 0 crossed.entry) [Packet] := by
  have same := readback_emit input nonempty (Quotient.mk _ crossed)
  rw [emitClass_mk, Case.readbackClass_mk] at same
  exact Quotient.exact same

/-! ## Composition across the two functors -/

example : (emitFunctor input).map (graph straight ≫ graph crossed) =
    term straight.toLetCase ≫ term crossed.toLetCase := by
  rw [Functor.map_comp]
  exact congrArg₂ (· ≫ ·) (emitClass_mk input straight) (emitClass_mk input crossed)

example : (readbackFunctor input).map (term probe ≫ term mix) =
    graph (rebuilt probe) ≫ graph (rebuilt mix) := by
  rw [Functor.map_comp]
  exact congrArg₂ (· ≫ ·) (Case.readbackClass_mk nonempty probe) (Case.readbackClass_mk nonempty mix)

/-- The graph read back from the literal native let replays to the written
link of the two separately read graphs. -/
example :
    let whole := rebuilt (Case.seq probe mix)
    let linked := seq (rebuilt probe) (rebuilt mix)
    ReplayEqv false Source.toList (whole.table.packedSSA 0 whole.entry)
      (linked.table.packedSSA 0 linked.entry) [Packet] := by
  have same := readback_comp input nonempty nonempty
    (Quotient.mk _ probe : Case.Hom Op captures exits exits) (Quotient.mk _ mix)
  rw [Case.seqClass_mk, Case.readbackClass_mk, Case.readbackClass_mk, Case.readbackClass_mk,
    seqClass_mk] at same
  exact Quotient.exact same

/-- The two sides are different graphs, with three and nine rows after entry. -/
example : (rebuilt (Case.seq probe mix)).size = 3 ∧ (seq (rebuilt probe) (rebuilt mix)).size = 9 :=
  ⟨rfl, rfl⟩

/-- An emitted written graph composes with a term written natively, and
the composite reads back to the written link. -/
example : (readbackFunctor input).map ((emitFunctor input).map (graph straight) ≫ term mix) =
    graph straight ≫ graph (rebuilt mix) :=
  ((readbackFunctor input).map_comp _ _).trans
    (congrArg₂ (· ≫ ·) (readbackFunctor_map_emitFunctor_map input (graph straight))
      (Case.readbackClass_mk nonempty mix))

/-! ## Native classes stay distinct

Equal classes have equal ordered traces in every older context. The older
capture holds the left tag and the newer capture holds the right tag. -/

local notation "Val" => LetCase.Structural.Finite.Value

private def ambient : BoundEnv Val captures :=
  (BoundEnv.snoc (β := .nil) (fun i => i.elim0) (.inl PUnit.unit)).snoc (.inr PUnit.unit)

private abbrev low : Val Packet := .inl PUnit.unit
private abbrev high : Val Packet := .inr (.inl PUnit.unit)

/-- Return the tag held by the newer capture. -/
private def newer : Operand Op Source Packet :=
  ⟨.case (.bv 1) (.inl .unit) (.inr (.inl .unit)), .case .bv (.inl .unit) (.inr (.inl .unit))⟩

/-- Return the tag held by the older capture. -/
private def older : Operand Op Source Packet :=
  ⟨.case (.bv 2) (.inl .unit) (.inr (.inl .unit)), .case .bv (.inl .unit) (.inr (.inl .unit))⟩

private theorem separated {a b : Operand Op Source Packet} {x y : Val Packet} (packet : Val Packet)
    (left : run a.2 (ambient.snoc packet) = pure x) (right : run b.2 (ambient.snoc packet) = pure y)
    (differ : x ≠ y) : term a ≠ term b := by
  intro same
  have eq : Equiv false Γ₀ Source a.1 b.1 Packet := Quotient.exact same
  have runs := (traceArrow_eq_iff_run a.2 b.2).mp
    ((equiv_iff_traceArrow_eq_snoc input a.2 b.2).mp eq) (ambient.snoc packet)
  rw [left, right] at runs
  have mem : (x, 1) ∈ (pure y : Trace Empty Op (Val Packet)).outcomes := by
    rw [← runs]
    exact rfl
  have pair : (x, (1 : Log Empty Op)) = (y, 1) := mem
  exact differ (congrArg Prod.fst pair)

private theorem high_ne_low : high ≠ low := Sum.inr_ne_inl

section Runs

-- The typed values below are stated at their unfolded carriers.
set_option backward.isDefEq.respectTransparency false

private theorem run_flip : run flip.2 (ambient.snoc low) = pure high := by
  simp only [flip, run, Derivation.denote]
  erw [pure_bind]
  change (((pure PUnit.unit : Trace Empty Op (Val Ty.unit)) >>= fun a =>
    (pure (Sum.inl a) : Trace Empty Op (Val (packedExitType [Ty.unit])))) >>= fun b =>
    (pure (Sum.inr b) : Trace Empty Op (Val Packet))) = _
  simp only [pure_bind]

private theorem run_newer : run newer.2 (ambient.snoc low) = pure high := by
  simp only [newer, run, Derivation.denote]
  erw [pure_bind]
  change (((pure PUnit.unit : Trace Empty Op (Val Ty.unit)) >>= fun a =>
    (pure (Sum.inl a) : Trace Empty Op (Val (packedExitType [Ty.unit])))) >>= fun b =>
    (pure (Sum.inr b) : Trace Empty Op (Val Packet))) = _
  simp only [pure_bind]

private theorem run_older : run older.2 (ambient.snoc low) = pure low := by
  simp only [older, run, Derivation.denote]
  erw [pure_bind]
  change ((pure PUnit.unit : Trace Empty Op (Val Ty.unit)) >>= fun a =>
    (pure (Sum.inl a) : Trace Empty Op (Val Packet))) = _
  simp only [pure_bind]

end Runs

/-- Exchanging the tags is a different class from the input variable. -/
example : term flip ≠ 𝟙 native :=
  separated (b := ⟨.bv 0, .bv⟩) low run_flip rfl high_ne_low

/-- Two terms that differ only in the capture they read are different classes. -/
example : term newer ≠ term older :=
  separated low run_newer run_older high_ne_low

/-! ## The packaged equivalence -/

example : (categoryEquivalence (Φ := Op) input).functor = emitFunctor input ∧
    (categoryEquivalence (Φ := Op) input).inverse = readbackFunctor input :=
  ⟨rfl, rfl⟩

example : emitFunctor (Φ := Op) input ⋙ readbackFunctor input = 𝟭 _ :=
  emitFunctor_comp_readbackFunctor input

example : readbackFunctor (Φ := Op) input ⋙ emitFunctor input = 𝟭 _ :=
  readbackFunctor_comp_emitFunctor input

example : (emitFunctor (Φ := Op) input).IsEquivalence ∧ (readbackFunctor (Φ := Op) input).IsEquivalence :=
  ⟨(categoryEquivalence input).isEquivalence_functor, (categoryEquivalence input).isEquivalence_inverse⟩

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.LetCaseTests
