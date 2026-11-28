module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Scoped.Defs
import Silmaril.SSA.PEG.Bridge.RVSDG.Thms
import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Theta.Thms
import Silmaril.SSA.RVSDG.ValueMap.Thms

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Scoped.Proofs

open RVSDG (PortType Tuple)
open RVSDG.MLIR.Graph.Feedback.WholeTheta (runtime)
open RVSDG.Theta (Iterate bodyResult)

variable {D : Type} {P : InstructionSet.{0,0} D}
variable (m : TotalModel P)

/-- The PEG runtime has an empty state carrier and the stateless
institution uses unit for the unused state sort. Only typed data packets
are compared across the two models. -/
private def transport : (t : ValuePort D) → (Region.model m).Val t → (runtime (model m)).Val t
  | .value _, x => x
  | .control _, x => x
  | .state _, x => nomatch x

private theorem transport_encode {ts : List (Ty D)} (xs : Tuple m.toPEG.Value ts) :
    (Region.encode m xs).map (transport m) = encode m xs := by
  induction xs with
  | nil => rfl
  | @cons t ts x xs ih =>
    exact congrArg (Tuple.cons (F := (runtime (model m)).Val) (t := .value t) x) ih

private theorem transport_inj {ts : List (ValuePort D)} :
    Function.Injective (Tuple.map (ts := ts) (transport m)) := by
  induction ts with
  | nil => intro x y _; cases x; cases y; rfl
  | cons t ts ih =>
    intro x y same
    cases x with
    | cons x xs =>
      cases y with
      | cons y ys =>
        have ⟨heads, tails⟩ := Tuple.cons.inj same
        have headEq : x = y := by cases t <;> first | exact heads | exact PEmpty.elim x
        exact congrArg₂ Tuple.cons headEq (ih tails)

private theorem transport_run {ins out : List (ValuePort D)} (op : Region.Opcode P ins out)
    (input : Tuple (Region.model m).Val ins) :
    ((Region.model m).run op input).map (transport m) =
      (runtime (model m)).run op (input.map (transport m)) := by
  cases op with
  | @primitive ins out op =>
    obtain ⟨args, rfl⟩ := show ∃ args, Region.encode m args = input from
      ⟨fromPorts (F := (Region.model m).Val) _ input, to_fromPorts input⟩
    rw [transport_encode]
    change (Tuple.cons (F := (Region.model m).Val) (t := .value _) (m.run op
      (fromPorts _ (toPorts (F := (Region.model m).Val) args))) .nil).map (transport m) =
      Tuple.cons (F := (runtime (model m)).Val) (t := .value _)
        (m.run op (fromPorts _ (toPorts (F := (runtime (model m)).Val) args))) .nil
    have source : fromPorts (F := (Region.model m).Val) ins (toPorts args) = args :=
      from_toPorts (F := (Region.model m).Val) args
    have target : fromPorts (F := (runtime (model m)).Val) ins (toPorts args) = args :=
      from_toPorts (F := (runtime (model m)).Val) args
    simp only [source, target, Tuple.map, transport]
  | branch =>
    cases input with
    | cons flag rest => cases rest; rfl

private theorem iterate_map {X Y : Type} {f : X → Y} (surj : Function.Surjective f)
    {step : X → Bool → X → Prop} {step' : Y → Bool → Y → Prop}
    (agrees : ∀ x k y, step x k y ↔ step' (f x) k (f y)) (x y : X) :
    Iterate step x y ↔ Iterate step' (f x) (f y) := by
  constructor
  · intro ran
    induction ran with
    | stop h => exact .stop ((agrees _ _ _).mp h)
    | again h _ ih => exact .again ((agrees _ _ _).mp h) ih
  · suffices reflect : ∀ {u v}, Iterate step' u v → ∀ x y, f x = u → f y = v → Iterate step x y from
      fun ran => reflect ran x y rfl rfl
    intro u v ran
    induction ran with
    | stop h =>
      intro x y hx hy
      exact .stop ((agrees _ _ _).mpr (hx ▸ hy ▸ h))
    | @again u v w first _ ih =>
      intro x y hx hy
      obtain ⟨next, hn⟩ := surj v
      exact .again ((agrees _ _ _).mpr (hx ▸ hn ▸ first)) (ih next y hn hy)

theorem runtime_returns {carried : List (Ty D)} {sigs : List (List (ValuePort D))}
    (g : RVSDG.Theta.Graph (Region.Opcode P) (valuePorts carried) sigs)
    (input output : Tuple m.toPEG.Value carried) :
    g.Returns (Region.model m) (Region.encode m input) (Region.encode m output) ↔
      g.Returns (runtime (model m)) (encode m input) (encode m output) := by
  have surj : Function.Surjective (Tuple.map (ts := valuePorts carried) (transport m)) := by
    intro out
    let args : Tuple m.toPEG.Value carried := fromPorts (F := (runtime (model m)).Val) carried out
    exact ⟨Region.encode m args, (transport_encode m args).trans (to_fromPorts out)⟩
  rw [← transport_encode m input, ← transport_encode m output]
  apply iterate_map surj
  intro x again y
  have run := g.body.run_map (transport m) (transport_run m) (fun _ _ => rfl) x
  have result : (bodyResult (Region.model m) again y).map (transport m) =
      bodyResult (runtime (model m)) again (y.map (transport m)) := rfl
  rw [← run, ← result]
  exact (transport_inj m).eq_iff.symm

end Silmaril.SSA.PEG.Bridge.Theta.Region.MLIR.Scoped.Proofs
