module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.Defs
import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate (Program)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GVN.Elimination (Rewrite Routing)
open Silmaril.SSA.SeaOfNodes.Pure.ConstantFold
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (Opcode model word)
open Silmaril.SSA.RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {p : Suffix} {edit : Rewrite Opcode (dataPorts [word, word]) [] p.sigs}
variable {intermediate : Result inputs sigs} {target : Program inputs sigs [word]}

private theorem suffixEdit?_accepted (accepted : suffixEdit? p = some edit) :
    ∃ (candidate : GVN.Producer p.dataflow word)
      (applied : AddIdealize.Applied (dataPorts [word, word]) [] p.sigs),
      p = suffix .left 0 ∧
      AddIdealize.step ⟨fun _ => none⟩ p candidate = .ok (some applied) ∧ applied.rewrite = edit := by
  unfold suffixEdit? at accepted
  obtain ⟨inner, _, accepted⟩ := Option.bind_eq_some_iff.mp accepted
  split at accepted
  · rename_i appliedEq
    exact ⟨inner.val, _, inner.property, appliedEq, Option.some.inj accepted⟩
  · contradiction

theorem suffixEdit?_agrees (accepted : suffixEdit? p = some edit)
    (entry : Tuple (Val model.value) (dataPorts [word, word])) :
    Routing.Agrees edit.route model entry (p.dataflow.eval model entry PUnit.unit)
      (edit.flow.eval model entry PUnit.unit) := by
  obtain ⟨_, _, _, checked, rfl⟩ := suffixEdit?_accepted accepted
  exact AddIdealize.step_agrees checked entry

theorem suffixEdit?_redirects
    {edit : Rewrite Opcode (dataPorts [word, word]) [] (suffix .left 0).sigs}
    (accepted : suffixEdit? (suffix .left 0) = some edit) :
    edit.route (.output (1 : Fin 3) .head) = .arg .head ∧
      (edit.route (.output (2 : Fin 3) .head)).address = .output 1 0 ∧
      AddRewrite.rewrittenProgram (suffix .left 0) edit = cleanedSuffix := by
  injection accepted with h
  subst edit
  exact ⟨rfl, rfl, rfl⟩

private theorem suffixEdit?_output (shape : p = suffix .left 0) (accepted : suffixEdit? p = some edit) :
    AddRewrite.rewrittenProgram p edit = cleanedSuffix := by
  subst p
  exact (suffixEdit?_redirects accepted).2.2

theorem rewrite?_eq_some_iff :
    rewrite? intermediate = some target ↔
      ∃ value p, intermediate = .materialized .left value p ∧
        p.suffix = suffix .left 0 ∧ target = { p with suffix := cleanedSuffix } := by
  constructor
  · intro accepted
    cases intermediate with
    | rotated _ => contradiction
    | materialized column value p =>
      cases column with
      | right => contradiction
      | left =>
        obtain ⟨edit, found, rfl⟩ := Option.map_eq_some_iff.mp accepted
        obtain ⟨_, _, shape, _, _⟩ := suffixEdit?_accepted found
        exact ⟨value, p, rfl, shape, by
          rw [suffixEdit?_output shape found]⟩
  · rintro ⟨value, p, rfl, shape, rfl⟩
    simp only [rewrite?]
    generalize hp : p.suffix = old
    rw [hp] at shape
    subst old
    rfl

private theorem cleanedSuffix_eval (entry : Tuple (Val model.value) (dataPorts [word, word])) :
    cleanedSuffix.eval model entry = (suffix .left 0).eval model entry := by
  have agrees := suffixEdit?_agrees (p := suffix .left 0) rfl entry
  exact (agrees _ (suffix .left 0).result).symm

theorem rewrite?_atSlot_eq {value : BitVec 64} {before : Program inputs sigs [word]}
    (accepted : rewrite? (.materialized .left value before) = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (slot : Slot) :
    target.atSlot entry slot = before.atSlot entry slot := by
  obtain ⟨_, _, same, shape, rfl⟩ := rewrite?_eq_some_iff.mp accepted
  cases same
  simp only [Program.atSlot, shape, cleanedSuffix_eval]
  rfl

theorem rewrite?_returns_iff (accepted : rewrite? intermediate = some target)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (returned : BitVec 64) :
    target.Returns entry returned ↔ intermediate.Returns entry returned := by
  obtain ⟨value, p, rfl, shape, rfl⟩ := rewrite?_eq_some_iff.mp accepted
  change (∃ values, p.diamond.Returns model entry values ∧
      cleanedSuffix.eval model (.cons (entry.get p.residual) values) = returned) ↔
    (∃ values, p.diamond.Returns model entry values ∧
      p.suffix.eval model (.cons (entry.get p.residual) values) = returned)
  simp only [shape, cleanedSuffix_eval]

end Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup
