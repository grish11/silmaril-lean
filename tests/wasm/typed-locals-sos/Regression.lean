module

import Silmaril.Wasm.Institution.Operational.Locals.Native.Thms

open Silmaril.Wasm
/-- An initialized i32 slot changes while the second i64 slot persists. -/
private abbrev old : Execution.Runtime.Value := .int .i32 7

open Silmaril.Wasm.Institution.Operational.Locals
open Silmaril.Wasm.SingleThreaded.Det (noHost)

private abbrev fresh : Execution.Runtime.Value := .int .i32 23
private abbrev saved : Execution.Runtime.Value := .int .i64 48
private abbrev slot : LocalIdx := ⟨0⟩
private abbrev missing : LocalIdx := ⟨2⟩

private abbrev start : State := ⟨[old, saved], [.value fresh, .tee slot, .get slot]⟩
private abbrev pending : State := ⟨[old, saved], [.value fresh, .value fresh, .set slot, .get slot]⟩
private abbrev assigned : State := ⟨[fresh, saved], [.value fresh, .get slot]⟩
private abbrev done : State := ⟨[fresh, saved], [.value fresh, .value fresh]⟩

private theorem typed : Admitted [.int .i32, .int .i64] [.int .i32, .int .i32] start :=
  ⟨rfl, rfl⟩

private theorem tee : Edge start pending :=
  context (fact (.tee [old, saved] slot fresh)) [] [.get slot]

private theorem write : Edge pending assigned :=
  context (fact (.set [old, saved] slot fresh (by decide))) [fresh] [.get slot]

private theorem read : Edge assigned done :=
  context (fact (.get [fresh, saved] slot fresh rfl)) [fresh] []

private theorem path : Runs start done :=
  ((Relation.ReflTransGen.single tee).tail write).tail read

private def v1Host : V1.Execution.HostSemantics Unit := fun _ _ _ _ => False
private def limeHost : Lime1.Execution.HostSemantics Unit := fun _ _ _ _ => False

private abbrev v1Store : V1.Execution.Store Unit :=
  { globals := [⟨old, .var⟩] }
private abbrev m : Execution.Runtime.ModuleInst := { globals := [⟨0⟩] }

private abbrev v1Start := v1Config v1Store m start
private abbrev v1Done := v1Config v1Store m done
private abbrev limeStart := v1Start.toLime
private abbrev limeDone := v1Done.toLime
private abbrev coreStart := limeStart.toCore
private abbrev coreDone := limeDone.toCore

example : V1.Execution.Step v1Host (v1Config v1Store m pending) (v1Config v1Store m assigned) :=
  v1_sound write

example : V1.Execution.Steps v1Host v1Start v1Done :=
  (v1_run_iff typed).mpr ⟨done, path, run_closed typed path, rfl⟩

example : Lime1.Execution.Steps limeHost limeStart limeDone := by
  change Lime1.Execution.Steps limeHost (v1Config _ _ start).toLime (v1Config _ _ done).toLime
  rw [v1_to_lime, v1_to_lime]
  exact (lime_run_iff typed).mpr ⟨done, path, run_closed typed path, rfl⟩

example : Execution.Core.Steps Numerics.Profile.spec noHost coreStart coreDone := by
  change Execution.Core.Steps Numerics.Profile.spec noHost
    (v1Config _ _ start).toLime.toCore (v1Config _ _ done).toLime.toCore
  rw [v1_to_lime, v1_to_lime, lime_to_core, lime_to_core]
  exact (core_run_iff typed).mpr ⟨done, path, run_closed typed path, rfl⟩

-- Readback allows arbitrary native targets, including frames not known in advance.
example (target : Execution.Core.Config Unit)
    (steps : Execution.Core.Steps Numerics.Profile.spec noHost coreStart target) :
    ∃ q, Runs start q ∧ Admitted [.int .i32, .int .i64] [.int .i32, .int .i32] q ∧
      target = coreConfig coreStart.store coreStart.frame.module q := by
  change Execution.Core.Steps Numerics.Profile.spec noHost (v1Config _ _ start).toLime.toCore _ at steps
  rw [v1_to_lime, lime_to_core] at steps
  exact (core_run_iff typed).mp steps

example : coreDone.store = coreStart.store ∧
    coreDone.frame.module = coreStart.frame.module ∧
    coreDone.frame.locals = [coreLocal fresh, coreLocal saved] := ⟨rfl, rfl, rfl⟩

-- An invalid local index fails admission. A native trap is an administrative outcome.
example : ¬ Admitted [.int .i32, .int .i64] [.int .i32]
    ⟨[old, saved], [.get missing]⟩ := by
  rintro ⟨_, checked⟩
  contradiction

example : ¬ Execution.Core.Step Numerics.Profile.spec noHost coreStart
    { coreStart with code := [.trap] } := by
  intro trap
  change Execution.Core.Step Numerics.Profile.spec noHost (v1Config _ _ start).toLime.toCore _ at trap
  rw [v1_to_lime, lime_to_core] at trap
  obtain ⟨q, _, eq⟩ := core_step_iff.mp trap
  have supported := coreCodec.supports_encode q.code
  have code : [.trap] = coreCodec.encode q.code := congrArg Execution.Core.Config.code eq
  rw [← code] at supported
  exact Bool.noConfusion (supported .trap (List.Mem.head _))

example : Execution.Core.Step Numerics.Profile.spec noHost
    { coreStart with code := [.plain .unreachable] } { coreStart with code := [.trap] } :=
  .parametric .unreachable

open Silmaril.Wasm.SingleThreaded.Det in
example (target : Execution.Core.Config Unit) :
    ¬ Execution.Core.Step Numerics.Profile.spec noHost
      { coreStart with code := [.plain (.localGet missing)] } target := by
  intro step
  rcases Silmaril.Wasm.SingleThreaded.Det.Step.decomp step with head | bubble
  · obtain ⟨saved, args, op, rest, _, first, _, reduction, _⟩ := fnv_headDec head
    change ([], [.plain (.localGet missing)]) = (saved ++ args, op :: rest) at first
    simp only [Prod.mk.injEq, List.nil_eq_append_iff, List.cons.injEq] at first
    obtain ⟨⟨_, rfl⟩, rfl, _⟩ := first
    have localStep := reduction.fam_inv (by change Fam.variable ≠ .control; decide)
    generalize eq : ([.plain (.localGet missing)] : List Execution.Core.Admin) = code at localStep
    cases localStep <;> simp at eq
    case localGet =>
      subst_vars
      contradiction
  · obtain ⟨_, _, _, _, _, ⟨first, _, _⟩ | ⟨_, first, _, _⟩⟩ := fnv_bubble bubble <;>
      change (([] : List Execution.Core.Val), [Execution.Core.Admin.plain (.localGet missing)]) = _ at first <;>
      simp at first
