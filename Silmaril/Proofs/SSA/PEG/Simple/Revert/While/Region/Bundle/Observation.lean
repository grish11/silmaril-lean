module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Bundle.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Thms
import Silmaril.SSA.PEG.Rules.Thms
import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Bundle.Proofs

open RVSDG (Port Tuple)
open Rules (readRef)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried rest : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried (result :: rest) n 1}
variable (cert : Certificate g) {m : Interpretation.{u,v,w} P} {input : Tuple m.Value carried}

private theorem tuple_ext {F : Ty Data → Type w} {ts : List (Ty Data)} (xs ys : Tuple F ts)
    (same : ∀ t (p : Port ts t), xs.get p = ys.get p) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys => exact congrArg₂ Tuple.cons (same _ .head) (ih ys fun t p => same t (.tail p))

private theorem setClock (idx : Index 1) (k : Nat) : idx.set 0 k = fun _ => k := by
  funext j
  have eq : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

private theorem observe_trace (idx : Index 1) {k : Nat} {final : Tuple m.Value (.bool :: carried)}
    (exit : cert.scalar.TraceObservation m
      ((scalarView g).denote m input cert.scalar.demandWellFounded) idx k final) :
    g.observe m (g.denote m input cert.scalar.demandWellFounded) idx =
      (cert.project m final).map (fun _ => some) := by
  apply tuple_ext
  intro t port
  simp only [Graph.observe, Certificate.project, Certificate.exitSlots, get_map]
  let root := g.roots.get port
  let slot := cert.slots.get port
  let values := (scalarView g).denote m input cert.scalar.demandWellFounded
  let theta := cert.scalar.descriptor.theta.get slot
  have row : Rules.HasNode (g := scalarView g) root (.eval 0)
      (.cons theta (.cons cert.scalar.descriptor.pass .nil)) :=
    (eqRec_heq root.typed (g.node root.id)).symm.trans (heq_of_eq (cert.roots t port))
  change readRef (g := scalarView g) values root idx = some (final.get (.tail slot))
  have pass : readRef (g := scalarView g) values cert.scalar.descriptor.pass idx = some ⟨k⟩ := exit.pass
  rw [Rules.eval_at ((scalarView g).denote_solves m input _) row, pass]
  change monotonize (fun j => readRef (g := scalarView g) values theta (idx.set 0 j)) k = _
  exact (monotonize_eq_some_iff _ _ _).mpr
    ⟨by rw [setClock]; exact exit.sample t slot,
      fun j hj => by rw [setClock]; exact exit.definedBefore j hj t slot⟩

private theorem unpack {output : Tuple m.Value (result :: rest)}
    (ran : Exec m cert.revert input (some output)) :
    ∃ (k : Nat) (start final : Tuple m.Value (.bool :: carried)),
      cert.scalar.guard.lower.runLoopFree m input = some start ∧
      WhileTrace m (.var .head) cert.scalar.body.enableWhile k start final ∧
      cert.project m final = output := by
  change Exec m (.seq (.seq cert.scalar.guard.lower.enableWhile
    (.while rfl (.var .head) cert.scalar.body.enableWhile)) (.project cert.exitSlots)) input
      (some output) at ran
  cases ran with
  | seq loop projected =>
    cases projected
    cases loop with
    | seq guard body =>
      obtain ⟨k, trace⟩ := Exec.while_trace body
      exact ⟨k, _, _, Exec.deterministic (cert.scalar.guard.lower.runLoopFree_enableWhile input)
        guard, trace, rfl⟩

theorem firstExit_of_exec
    (neg : ∀ b : Bool, m.run cert.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {output : Tuple m.Value (result :: rest)}
    (ran : Exec m cert.revert input (some output)) :
    ∃ k, readRef (g := g) (g.denote m input cert.scalar.demandWellFounded)
        cert.scalar.descriptor.pass idx = some ⟨k⟩ ∧
      g.observe m (g.denote m input cert.scalar.demandWellFounded) idx = output.map (fun _ => some) := by
  obtain ⟨k, _, _, guard, trace, rfl⟩ := unpack cert ran
  have exit := cert.scalar.traceObservation m input neg idx guard trace
  exact ⟨k, exit.pass, observe_trace cert idx exit⟩

theorem exec_of_observe (total : cert.scalar.Total m)
    (neg : ∀ b : Bool, m.run cert.scalar.descriptor.negate (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    (idx : Index 1) {output : Tuple m.Value (result :: rest)}
    (observed : g.observe m (g.denote m input cert.scalar.demandWellFounded) idx =
      output.map (fun _ => some)) :
    Exec m cert.revert input (some output) := by
  have head := congrArg (fun xs => xs.get .head) observed
  simp only [Graph.observe, get_map] at head
  have anchor : (scalarView g).observe m
      ((scalarView g).denote m input cert.scalar.demandWellFounded) idx =
        .cons (some (output.get .head)) .nil :=
    congrArg (fun x => Tuple.cons (F := fun t => Option (m.Value t)) x .nil) head
  obtain ⟨_, _, final, guard, witness⟩ := cert.scalar.exitWitness_of_defined m input total neg idx anchor
  have exit := cert.scalar.traceObservation m input neg idx guard witness.trace
  have mapped := (observe_trace cert idx exit).symm.trans observed
  have same : cert.project m final = output := by
    apply tuple_ext
    intro t port
    apply Option.some.inj
    simpa only [get_map] using congrArg (fun xs => xs.get port) mapped
  have ran : Exec m cert.revert input (some (cert.project m final)) :=
    .seq (.seq (guard ▸ cert.scalar.guard.lower.runLoopFree_enableWhile input) witness.trace.exec) .project
  exact same ▸ ran

theorem runFuel_exec (fuel : Nat) {output : Tuple m.Value (result :: rest)}
    (ran : cert.runFuel m fuel input = some output) : Exec m cert.revert input (some output) := by
  obtain ⟨final, computed, rfl⟩ := Option.map_eq_some_iff.mp ran
  obtain ⟨start, guard, loop⟩ := Option.bind_eq_some_iff.mp computed
  exact .seq (.seq (guard ▸ cert.scalar.guard.lower.runLoopFree_enableWhile input)
    (cert.scalar.runStore_exec m fuel start loop)) .project

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Bundle.Proofs
