module

public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Relabel.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel.Defs

public section

namespace Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Relabel.Proofs

open RVSDG (Port Tuple)
open RVSDG.LambdaSSA.Theta
open Isotope.LambdaSSA (Tm Region)
open Simple.Revert.While.Region (Certificate Schedule)
open Silmaril.SSA.PEG.Bridge.Theta.Region.Ordered (Bundle)

variable {Data : Type} {P Q : InstructionSet.{0,0} Data}
variable {carried vars outs ins : List (Ty Data)} {t : Ty Data} {n : Nat}
variable {g : Graph P carried [t] n 1} {invariants : Bool}
variable (f : InstructionMap P Q)

private theorem field_map (p : Port vars t) (arg : Tm (Primitive P)) :
    (Schedule.field p arg).mapInstr (Primitive.map f) =
      Schedule.field p (arg.mapInstr (Primitive.map f)) := by
  induction p generalizing arg with
  | head => rfl
  | tail p ih => simp only [Schedule.field, Tm.mapInstr, ih]

private theorem tupleTerm_map (layout : Schedule.Layout P vars) (slots : Tuple (Port vars) ins) :
    (Schedule.tupleTerm layout slots).mapInstr (Primitive.map f) =
      Schedule.tupleTerm (fun p => (layout p).mapInstr (Primitive.map f)) slots := by
  induction slots with
  | nil => rfl
  | cons _ _ ih => simp only [Schedule.tupleTerm, Tm.mapInstr, ih]

private theorem shift_map (layout : Schedule.Layout P vars) {t : Ty Data} (p : Port vars t) :
    (layout.shift p).mapInstr (Primitive.map f) =
      (Schedule.Layout.shift (fun p => (layout p).mapInstr (Primitive.map f))) p :=
  Tm.mapInstr_rename _ _ _

private theorem push_map (layout : Schedule.Layout P vars) :
    (fun {s} (p : Port (t :: vars) s) => (layout.push p).mapInstr (Primitive.map f)) =
      (fun {s} (p : Port (t :: vars) s) =>
        (Schedule.Layout.push (fun p => (layout p).mapInstr (Primitive.map f))) p) := by
  funext s p
  cases p with
  | head => rfl
  | tail p => exact shift_map f layout p

private theorem emit_map {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    (s : Schedule g false roots scope) (layout : Schedule.Layout P vars)
    (finish : Schedule.Layout P outs → Region (Primitive P))
    (finish' : Schedule.Layout Q outs → Region (Primitive Q))
    (mapped : ∀ out : Schedule.Layout P outs, (finish out).mapInstr (Primitive.map f) =
      finish' (fun p => (out p).mapInstr (Primitive.map f))) :
    (Schedule.emit s layout finish).mapInstr (Primitive.map f) =
      Schedule.emit (Region.Relabel.schedule f s)
        (fun p => (layout p).mapInstr (Primitive.map f)) finish' := by
  induction s with
  | done reads => exact mapped (layout.select reads.slots)
  | bind i op refs fresh row reads tail ih =>
    simp only [Schedule.emit, Region.Relabel.schedule, Region.mapInstr, Tm.mapInstr, Primitive.map,
      tupleTerm_map, ih layout.push finish finish' mapped, push_map]
    rfl
  | branch enabled => cases enabled

private theorem route_map (cert : Certificate g invariants) (layout : Schedule.Layout P (.bool :: carried)) :
    (route cert layout).mapInstr (Primitive.map f) =
      route (Region.Relabel.certificate f cert) (fun p => (layout p).mapInstr (Primitive.map f)) := by
  simp only [route, Region.mapInstr, Tm.mapInstr, Primitive.map, tupleTerm_map]
  have old : (fun {s} (p : Port carried s) => (layout.shift (.tail p)).mapInstr (Primitive.map f)) =
      (fun {s} (p : Port carried s) =>
        (Schedule.Layout.shift (fun p => (layout p).mapInstr (Primitive.map f))) (.tail p)) := by
    funext s p
    exact shift_map f layout (.tail p)
  rw [emit_map f cert.update _ _ (fun next => .br 0 (Schedule.tupleTerm next (Simple.ports carried)))
    (fun _ => by simp only [Region.mapInstr, tupleTerm_map]), old]
  rfl

theorem lower_map {g : Graph P carried carried n 1} {slot : Port carried t}
    (b : Bundle g slot invariants) :
    lower (Region.Relabel.bundle f b) = (lower b).mapInstr (Primitive.map f) := by
  unfold lower Operational.loop
  simp only [Region.mapInstr, Tm.mapInstr]
  congr 1
  funext _
  unfold header
  rw [emit_map f b.scalar.guard _ _ _ (route_map f b.scalar)]
  congr 1
  funext s p
  exact (field_map f p (.var 0)).symm

end Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Relabel.Proofs
