module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Thms
import Silmaril.SSA.PEG.Simple.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered.Proofs

open RVSDG (Port Tuple)
open Simple (WhileTrace get_map)
open Simple.Revert.While.Region (nodeAt)

set_option backward.isDefEq.respectTransparency false

variable {Data : Type} {P : InstructionSet.{0,0} Data}
variable {carried : List (Ty Data)} {result : Ty Data} {n : Nat}
variable {g : Graph P carried carried n 1} {slot : Port carried result} {allowInvariant : Bool}
variable (b : Bundle g slot allowInvariant) (m : TotalModel P)
variable (input : Tuple m.toPEG.Value carried)

private theorem tuple_ext {F : Ty Data → Type} {ts : List (Ty Data)} (xs ys : Tuple F ts)
    (same : ∀ t (p : Port ts t), xs.get p = ys.get p) : xs = ys := by
  induction xs with
  | nil => cases ys; rfl
  | cons x xs ih =>
    cases ys with
    | cons y ys => exact congrArg₂ Tuple.cons (same _ .head) (ih ys (fun t p => same t (.tail p)))

private theorem setClock (idx : Index 1) (k : Nat) : idx.set 0 k = fun _ => k := by
  funext j
  have eq : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

private noncomputable abbrev values := g.denote m.toPEG input b.demandWellFounded

private noncomputable def read {t : Ty Data} (r : Ref g.sort t) (idx : Index 1) : Option (m.toPEG.Value t) :=
  r.read m.carrier (values b m input (r.id, idx))

private theorem read_row {t : Ty Data} (r : Ref g.sort t) (idx : Index 1) :
    let node := nodeAt (scalarView g slot) r
    read b m input r idx =
      node.label.interpret m.toPEG input idx (fun p j _ => read b m input (node.arg p) j) := by
  obtain ⟨id, typed⟩ := r
  cases typed
  exact g.denote_solves m.toPEG input b.demandWellFounded (id, idx)

private theorem eval_root (idx : Index 1) {k : Nat}
    {final : Tuple m.toPEG.Value (.bool :: carried)}
    (exit : b.scalar.TraceObservation m.toPEG (values b m input) idx k final)
    {t : Ty Data} (p : Port carried t) :
    (g.observe m.toPEG (values b m input) idx).get p = some (final.get (.tail p)) := by
  rw [Graph.observe, get_map]
  change read b m input (g.roots.get p) idx = _
  rw [read_row b m input, b.roots t p]
  change (read b m input b.scalar.descriptor.pass idx).elim none
    (fun count => monotonize (fun j => read b m input (b.scalar.descriptor.theta.get p) (idx.set 0 j))
      count.down) = _
  have pass : read b m input b.scalar.descriptor.pass idx = some ⟨k⟩ := exit.pass
  rw [pass]
  change monotonize (fun j => read b m input (b.scalar.descriptor.theta.get p) (idx.set 0 j)) k = _
  apply (monotonize_eq_some_iff _ _ _).mpr
  refine ⟨?_, fun j hj => ?_⟩
  · rw [setClock]
    exact exit.sample t p
  · rw [setClock]
    exact exit.definedBefore j hj t p

variable (neg : ∀ flag : Bool, m.run b.scalar.descriptor.negate (.cons ⟨flag⟩ .nil) = ⟨!flag⟩)

include neg

theorem firstExit_of_returns (idx : Index 1) (output : Tuple m.toPEG.Value carried)
    (ran : b.compile.Returns (Region.model m) (encode m input) (encode m output)) :
    ∃ (k : Nat) (start final : Tuple m.toPEG.Value (.bool :: carried)),
      b.scalar.guard.lower.runLoopFree m.toPEG input = some start ∧
      WhileTrace m.toPEG (.var .head) b.scalar.body.enableWhile k start final ∧
      carriedValues final = output ∧
      b.scalar.TraceObservation m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx k final ∧
      g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) := by
  obtain ⟨k, start, final, guard, trace, same⟩ :=
    (Region.returns_iff_trace b.scalar m input output).mp ran
  have scalarExit := b.scalar.traceObservation m.toPEG input
    (fun flag => congrArg some (neg flag)) idx guard trace
  have exit : b.scalar.TraceObservation m.toPEG (values b m input) idx k final :=
    Eq.mp (congrArg (fun vs => b.scalar.TraceObservation m.toPEG vs idx k final)
      (b.denote_scalarView m input)) scalarExit
  refine ⟨k, start, final, guard, trace, same, exit, tuple_ext _ _ ?_⟩
  intro t p
  have atExit := eval_root b m input idx exit p
  rw [get_map, ← same]
  cases final
  exact atExit

omit neg in
private theorem anchor_observe (idx : Index 1) (output : Tuple m.toPEG.Value carried)
    (observed : g.observe m.toPEG (values b m input) idx = output.map (fun _ => some)) :
    (scalarView g slot).observe m.toPEG
      ((scalarView g slot).denote m.toPEG input b.scalar.demandWellFounded) idx =
        .cons (some (output.get slot)) .nil := by
  have head := congrArg (fun xs : Tuple (fun t => Option (m.toPEG.Value t)) carried =>
    xs.get slot) observed
  simp only [Graph.observe, get_map] at head
  rw [Graph.observe, b.denote_scalarView m input]
  exact congrArg (fun x => Tuple.cons (F := fun t => Option (m.toPEG.Value t)) x .nil) head

theorem returns_iff_observe (idx : Index 1) (output : Tuple m.toPEG.Value carried) :
    b.compile.Returns (Region.model m) (encode m input) (encode m output) ↔
      g.observe m.toPEG (g.denote m.toPEG input b.demandWellFounded) idx = output.map (fun _ => some) := by
  constructor
  · intro ran
    obtain ⟨_, _, _, _, _, _, _, observed⟩ := firstExit_of_returns b m input neg idx output ran
    exact observed
  · intro observed
    obtain ⟨_, _, final, _, _, ran⟩ := Region.return_at_firstExit b.scalar m input neg idx
      (output.get slot) (anchor_observe b m input idx output observed)
    obtain ⟨_, _, _, _, _, _, _, returned⟩ :=
      firstExit_of_returns b m input neg idx (carriedValues final) ran
    have same := returned.symm.trans observed
    have tupleEq : carriedValues final = output := by
      apply tuple_ext
      intro t p
      apply Option.some.inj
      have atPort := congrArg (fun xs : Tuple (fun t => Option (m.toPEG.Value t)) carried =>
        xs.get p) same
      simpa only [get_map] using atPort
    exact tupleEq ▸ ran

end Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered.Proofs
