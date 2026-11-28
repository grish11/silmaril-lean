module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader.Seed
import Silmaril.SSA.SeaOfNodes.GVN.Elimination.Thms
import Silmaril.SSA.SeaOfNodes.Loop.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader

open Silmaril.SSA.SeaOfNodes
open Diamond (Ty Val ValueSort dataPorts sortValue)
open GVN.Cyclic.Activation (Inputs inputSlot)
open GVN.Cyclic.Builder.Preheader
open Pure.SubZero (model)
open Silmaril.SSA.RVSDG (Origin Port Tuple Wires)
open Loop (appendTuple headerPorts)

variable {inputs carried added : List (ValueSort Unit)} {entrySigs headerSigs : List (List (Ty Unit))}
variable {out : ValueSort Unit}
variable {loop : Native inputs carried entrySigs headerSigs out}

private theorem front_read (caps : Inputs model added) (input : Inputs model inputs)
    {sort : ValueSort Unit} (port : Port added sort) :
    (prependValues caps input).get (inputSlot (frontPort port)) = caps.get (inputSlot port) := by
  induction port with
  | head => cases caps; rfl
  | tail inner ih => cases caps with | cons _ tail => exact ih tail

private theorem entryWires_get (input : Inputs model inputs) {lanes : List (ValueSort Unit)}
    (lift : ∀ {sort}, Port lanes sort → Port carried sort) {sort : ValueSort Unit} (port : Port lanes sort) :
    ((entryWires loop (number loop) lanes lift).read (preparedInput loop input) PUnit.unit).get (inputSlot port) =
      (loop.initial model input).get (inputSlot (lift port)) := by
  induction port with
  | head =>
    exact (front_read (loop.initial model input) input (canonicalLane loop (number loop) (lift .head))).trans
      (canonical_value input (lift .head))
  | tail inner ih => exact ih (fun p => lift (.tail p))

private theorem inputs_eq {sorts : List (ValueSort Unit)} (lhs rhs : Inputs model sorts)
    (agrees : ∀ {sort} (port : Port sorts sort), lhs.get (inputSlot port) = rhs.get (inputSlot port)) : lhs = rhs := by
  induction sorts with
  | nil => cases lhs; cases rhs; rfl
  | cons _ _ ih =>
    cases lhs with
    | cons lhs leftTail =>
      cases rhs with
      | cons rhs rightTail =>
        exact congrArg₂ Tuple.cons (agrees .head) (ih leftTail rightTail (fun p => agrees (.tail p)))

theorem prepare_initial (input : Inputs model inputs) :
    (prepare loop).initial model (preparedInput loop input) = loop.initial model input :=
  inputs_eq _ _ (fun port => entryWires_get input (fun p => p) port)

theorem lift_read (caps : Inputs model added) (input : Inputs model inputs) (old : Inputs model carried)
    {t : Ty Unit} (port : Port (headerPorts inputs carried) t) :
    (appendTuple old (prependValues caps input)).get (liftHeaderPort added port) =
      (appendTuple old input).get port := by
  induction added with
  | nil => cases caps; rfl
  | cons _ _ ih => cases caps with | cons _ tail => exact ih tail

private theorem tuple_map_map {F G H : Ty Unit → Type} {ports : List (Ty Unit)}
    (values : Tuple F ports) (first : ∀ t, F t → G t) (second : ∀ t, G t → H t) :
    (values.map first).map second = values.map (fun t x => second t (first t x)) := by
  induction values with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Tuple.cons _) ih

private theorem read_arguments {args target : List (Ty Unit)}
    (embedding : ∀ {t}, Port args t → Port target t)
    (source : Tuple (Val model.value) args) (new : Tuple (Val model.value) target)
    (agree : ∀ {t} (p : Port args t), new.get (embedding p) = source.get p) :
    Wires.read ((Silmaril.SSA.RVSDG.NestedTheta.identityPorts args).map
      (fun _ p => Origin.arg (past := []) (embedding p))) new PUnit.unit = source := by
  induction source with
  | nil => rfl
  | cons head tail ih =>
    simp only [Silmaril.SSA.RVSDG.NestedTheta.identityPorts, Tuple.map, tuple_map_map]
    exact congrArg₂ Tuple.cons (agree .head) (ih (fun p => embedding (.tail p)) (fun p => agree (.tail p)))

theorem observations_eq {args : List (Ty Unit)} {past : List (List (Ty Unit))}
    (packet : Wires args past (ObservationPorts carried out)) :
    Tuple.cons (packet.get .head) (.cons (packet.get (.tail .head)) (observationTail packet)) = packet := by
  cases packet with
  | cons _ tail => cases tail; rfl

@[expose] def packetOutcome (packet : Tuple (Val model.value) (ObservationPorts carried out)) :
    sortValue model.value out ⊕ Inputs model carried :=
  match packet with
  | .cons guard (.cons result feedback) => if guard.down then .inr feedback else .inl result

theorem step_packet (loop : Native inputs carried entrySigs headerSigs out)
    (input : Inputs model inputs) (old : Inputs model carried) :
    let args := appendTuple old input
    loop.step model input old = packetOutcome ((observations loop).read args (loop.header.eval model args PUnit.unit)) :=
  rfl

theorem prepare_packet (input : Inputs model inputs) (old : Inputs model carried) :
    let args := appendTuple old input
    let expanded := appendTuple old (preparedInput loop input)
    (observations (prepare loop)).read expanded ((prepare loop).header.eval model expanded PUnit.unit) =
      (observations loop).read args (loop.header.eval model args PUnit.unit) := by
  let expanded := appendTuple old (preparedInput loop input)
  let compiled := GVN.Elimination.plug loop.header (observations loop) (headerInputs carried)
  have readInputs : (headerInputs carried).read expanded PUnit.unit = appendTuple old input :=
    read_arguments (liftHeaderPort carried) _ _ (lift_read (loop.initial model input) input old)
  have preserved := GVN.Elimination.plug_read loop.header (observations loop) (headerInputs carried)
    model expanded PUnit.unit
  change compiled.2.read expanded (compiled.1.eval model expanded PUnit.unit) = _ at preserved
  rw [readInputs] at preserved
  exact (congrArg (fun packet => Wires.read packet expanded (compiled.1.eval model expanded PUnit.unit))
    (observations_eq compiled.2)).trans preserved

theorem prepare_step (input : Inputs model inputs) (old : Inputs model carried) :
    (prepare loop).step model (preparedInput loop input) old = loop.step model input old :=
  (step_packet _ _ _).trans ((congrArg packetOutcome (prepare_packet input old)).trans (step_packet _ _ _).symm)

end Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Preheader
