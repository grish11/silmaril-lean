module

import Silmaril.SSA.Peggy.Institution.SortMap.Thms

namespace Silmaril.SSA.Peggy.SortMap.Tests

open CategoryTheory
open PEG (EdgeKind Graph Index LoopForest Ref Ty Walk)
open RVSDG (Tuple)

private abbrev A : Ty Bool := .data false
private abbrev B : Ty Bool := .data true
private abbrev C : Ty Unit := .data ()

private inductive SourceOp : PEG.InstructionSet Bool
  | step : SourceOp [A, B] A

private inductive TargetOp : PEG.InstructionSet Unit
  | add : TargetOp [C, C] C

private def source : Signature.{0,0} := ⟨Bool, SourceOp⟩
private def target : Signature.{0,0} := ⟨Unit, TargetOp⟩

private def identify : source ⟶ target where
  sorts _ := ()
  opcode | .step => .add

private def model : Model.{0,0,0} target where
  carrier _ := Nat
  run
    | .add, .cons x (.cons y .nil) => some (Nat.add x y)

example : identify.sorts false = identify.sorts true := rfl
example : Ty.mapData identify.sorts .bool = .bool := rfl
example : Ty.mapData identify.sorts .count = .count := rfl

private def frame : LoopForest 1 := ⟨fun _ => none⟩

private def sorts : Fin 4 → Ty Bool :=
  Fin.cases A (Fin.cases B (Fin.cases A (Fin.cases A Fin.elim0)))

private def seed : Ref sorts A := ⟨0, rfl⟩
private def increment : Ref sorts B := ⟨1, rfl⟩
private def theta : Ref sorts A := ⟨2, rfl⟩
private def next : Ref sorts A := ⟨3, rfl⟩

private def recurrence : Graph SourceOp [A, B] [A, B] 4 1 where
  forest := frame
  sort := sorts
  node := Fin.cases (motive := fun i => PEG.Node SourceOp [A, B] (Fin 1) sorts (sorts i))
    (.ofLabel (.param .head) .nil)
    (Fin.cases (.ofLabel (.param (.tail .head)) .nil)
    (Fin.cases (.ofLabel (.theta 0) (.cons seed (.cons next .nil)))
    (Fin.cases (.ofLabel (.op .step) (.cons theta (.cons increment .nil))) (fun i => i.elim0))))
  roots := .cons theta (.cons increment .nil)

private theorem edgeFacts {a b : Fin 4} {k : EdgeKind (Fin 1)} (h : recurrence.Edge a k b) :
    (¬ k.IsFeedback → b.val < a.val) ∧ ∀ l, ¬ k.IsObserverAt l := by
  have localFacts : ∀ (a : Fin 4) (i : Fin (recurrence.node a).inputs.length),
      let k := (recurrence.node a).label.kind i
      let b := (recurrence.node a).arg i
      (¬ k.IsFeedback → b.id.val < a.val) ∧ ∀ l, ¬ k.IsObserverAt l := by
    unfold EdgeKind.IsObserverAt
    decide
  obtain ⟨i, rfl, rfl⟩ := h
  exact localFacts a i

private theorem noObserver {a b : Fin 4} {ks : List (EdgeKind (Fin 1))}
    (walk : Walk recurrence.Edge a ks b) : ∀ k ∈ ks, ∀ l, ¬ k.IsObserverAt l := by
  induction walk with
  | nil => simp
  | cons edge _ ih =>
    intro k hk l
    rcases List.mem_cons.mp hk with rfl | tail
    · exact (edgeFacts edge).2 l
    · exact ih k tail l

private theorem admitted : recurrence.WellFormed where
  forest := by
    intro i
    rintro ⟨ks, walk, nonempty⟩
    cases walk with
    | nil => exact nonempty rfl
    | cons edge _ => cases edge
  feedback := by
    intro a ks walk nonempty
    by_contra absent
    exact (Nat.lt_irrefl a.val) (walk.strictRank nonempty Fin.val
      (fun e hk => (edgeFacts e).1 (fun h => absent ⟨_, hk, h⟩)))
  loopScope := by
    intro a b ks start target walk ha hb
    have same : target = start := Subsingleton.elim _ _
    subst target
    exact .inl ⟨[], .nil start⟩
  outerFeedback := fun _ _ walk k hk l observer => (noObserver walk k hk l observer).elim

private abbrev seedRoots : Tuple (Ref sorts) [A, B] :=
  .cons seed (.cons increment .nil)

private abbrev sentence : Equation source where
  params := [A, B]
  results := [A, B]
  loops := 1
  forest := frame
  leftNodes := 4
  rightNodes := 4
  lhs := ⟨recurrence, rfl, admitted⟩
  rhs := ⟨recurrence.withRoots seedRoots, rfl, (recurrence.wellFormed_withRoots seedRoots).mpr admitted⟩

private abbrev translated := Equation.map identify sentence
private abbrev peggy := inst.{0,0,0}
private def input : Tuple model.Value [C, C] := .cons (2 : Nat) (.cons (9 : Nat) .nil)
private def clock (k : Nat) : Index 1 := fun _ => k

private def mappedGraph : Graph TargetOp [C, C] [C, C] 4 1 :=
  recurrence.mapData identify.opcode

private noncomputable def values : mappedGraph.Valuation model := translated.lhs.denote model input

private theorem solves : mappedGraph.Solves model input values :=
  mappedGraph.denote_solves model input (translated.lhs.graph.demandWellFounded translated.lhs.wellFormed)

private theorem thetaAtOne : values (2, clock 1) = some (11 : Nat) := by
  let prior := (clock 1).set 0 0
  have base : values (2, prior) = some (2 : Nat) :=
    (solves (2, prior)).trans (solves (0, prior))
  have right : values (1, prior) = some (9 : Nat) := solves (1, prior)
  have nextEq : values (3, prior) = some (11 : Nat) := by
    refine (solves (3, prior)).trans ?_
    change (PEG.collect (F := model.Value) [C, C] _).elim none (model.run TargetOp.add) = _
    have read : (fun i : Fin 2 =>
        (mappedGraph.node 3 |>.arg i).read model.carrier (values ((mappedGraph.node 3 |>.arg i).id, prior))) =
        (fun i : Fin 2 => Fin.cases (motive := fun j => Option (model.Value ([C, C][j])))
          (some (2 : Nat)) (Fin.cases (motive := fun j => Option (model.Value ([C, C][j.succ])))
            (some (9 : Nat)) (fun j => j.elim0)) i) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact base
      · exact Fin.cases right (fun empty => empty.elim0) j
    exact (congrArg (fun get =>
      (PEG.collect (F := model.Value) [C, C] get).elim none (model.run TargetOp.add)) read).trans rfl
  exact (solves (2, clock 1)).trans nextEq

private theorem orderedResult : translated.lhs.observe model input (clock 1) =
    (.cons (some (11 : Nat)) (.cons (some (9 : Nat)) .nil) :
      Tuple (fun ty => Option (model.Value ty)) [C, C]) := by
  change Tuple.cons (F := fun ty => Option (model.Value ty)) (t := C) (values (2, clock 1))
    (.cons (values (1, clock 1)) .nil) = _
  exact congrArg₂ Tuple.cons thetaAtOne (congrArg (fun x => Tuple.cons x .nil) (solves (1, clock 1)))

example : peggy.Sat model (peggy.map identify sentence) ↔
    peggy.Sat (peggy.reduct identify model) sentence :=
  Silmaril.Logic.Institution.satisfaction_condition peggy.I identify model sentence

-- The equation compares the recurrence with its initial value in the first slot.
example : ¬ peggy.Sat model (peggy.map identify sentence) := by
  intro holds
  have same := congrArg (fun roots => roots.get .head) (holds input (clock 1))
  change (translated.lhs.observe model input (clock 1)).get .head =
    (translated.rhs.observe model input (clock 1)).get .head at same
  have rhs : (translated.rhs.observe model input (clock 1)).get .head = some (2 : Nat) := by
    let rightGraph : Graph TargetOp [C, C] [C, C] 4 1 := translated.rhs.graph
    let wf : WellFounded rightGraph.Demand := rightGraph.demandWellFounded translated.rhs.wellFormed
    exact rightGraph.denote_solves model input wf (0, clock 1)
  rw [orderedResult, rhs] at same
  cases same

end Silmaril.SSA.Peggy.SortMap.Tests
