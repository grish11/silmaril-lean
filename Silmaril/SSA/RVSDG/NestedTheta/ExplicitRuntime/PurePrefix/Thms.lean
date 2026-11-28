module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Thms
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Thms

/-! # Denotation of a checked pure prefix and its ordered continuation -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix

open OrderedRuntime.Structured (Ty Data Threaded runtime withRuntime Instruction)
open Splice (append_denote)

set_option backward.isDefEq.respectTransparency false

universe u v w
variable {V : Type u} {P E Q : Dialect.{u,v} V PUnit.{u+1}}
variable {args middle outs ins out : Ports (Ty V)}
variable {past sigs : List (Ports (Ty V))}
variable {a : Data args} {b : Data middle} {c : Data outs}
variable (m : Partial.Model.{u,max u v,w} (Ordered P E)) (pure : Total m Q)

theorem lift_denote {t : Term (Ordered P E) (Threaded args) past sigs (Threaded outs)}
    {live : Origin (Threaded args) past runtime} (checked : ExplicitRuntime.Checked P E a c live t)
    (entry : Tuple m.Val (Threaded args)) (locals : Locals m.Val past) :
    (lift (Q := Q) checked).1.denoteOpenWith (model m pure) entry locals = t.denoteOpenWith m entry locals :=
  Institution.denoteOpen_map orderedMap (model m pure) t entry locals

theorem attach_denote {t : Term (Ordered P E) (Threaded middle) [] sigs (Threaded outs)}
    (checked : ExplicitRuntime.EntryChecked (a := b) (b := c) t)
    (live : Origin (Threaded args) past runtime) (wires : Wires (Threaded args) past middle)
    (entry : Tuple m.Val (Threaded args)) (locals : Locals m.Val past) :
    (attach (Q := Q) (a := a) checked live wires).1.denoteOpenWith (model m pure) entry locals =
      t.denoteOpenWith m (Wires.read (withRuntime live wires) entry locals) PUnit.unit := by
  rw [attach, lift_denote, append_denote]
  simp only [Term.denoteOpenWith, pure_bind]

/-- A pure binding extends the value environment by a total result.
Its admission passes the same live origin through the extended scope. -/
theorem pure_denote (di : Data ins) (do' : Data out) (op : Q ins out)
    (wires : Wires (Threaded args) past ins)
    (rest : Term (Op P E Q) (Threaded args) (past ++ [out]) sigs (Threaded outs))
    (entry : Tuple m.Val (Threaded args)) (locals : Locals m.Val past) :
    (pureBind di do' op wires rest).denoteOpenWith (model m pure) entry locals =
      rest.denoteOpenWith (model m pure) entry (locals.snoc (pure op (wires.read entry locals))) := by
  simp only [Term.denoteOpenWith, pureNode, Kind.denoteWith, model, Part.bind_eq_bind, Part.bind_some]

theorem primitive_denote (live : Origin (Threaded args) past runtime) (di : Data ins) (do' : Data out)
    (op : Instruction P E ins out) (wires : Wires (Threaded args) past ins)
    (rest : Term (Op P E Q) (Threaded args) (past ++ [Threaded out]) sigs (Threaded outs))
    (entry : Tuple m.Val (Threaded args)) (locals : Locals m.Val past) :
    (orderedBind live di do' op wires rest).denoteOpenWith
      (model m pure) entry locals =
      (m.primitive (.ordered di do' op) (Wires.read (withRuntime live wires) entry locals)).bind
        (fun result => rest.denoteOpenWith (model m pure) entry (locals.snoc result)) := by
  simp only [Term.denoteOpenWith, orderedNode, Kind.denoteWith, model, Part.bind_eq_bind]

/-- The selected mixed child reads its entry tuple, including the current
token. The continuation receives the selected child's entire result. -/
theorem gamma_denote (extra : Nat) (choice : Origin (Threaded args) past (.control (extra + 2)))
    (live : Origin (Threaded args) past runtime) (wires : Wires (Threaded args) past ins)
    (childSigs : Fin (extra + 2) → List (Ports (Ty V)))
    (children : ∀ j, Term (Op P E Q) (Threaded ins) [] (childSigs j) (Threaded out))
    (rest : Term (Op P E Q) (Threaded args) (past ++ [Threaded out]) sigs (Threaded outs))
    (entry : Tuple m.Val (Threaded args)) (locals : Locals m.Val past) :
    (Term.bind (gammaNode (P := P) (E := E) (Q := Q) (out := out) extra choice live wires childSigs)
      children rest).denoteOpenWith
      (model m pure) entry locals =
      ((children ((Wires.read (.cons choice .nil) entry locals).get .head).down).denoteOpenWith (model m pure)
        (Wires.read (withRuntime live wires) entry locals) PUnit.unit).bind
        (fun result => rest.denoteOpenWith (model m pure) entry (locals.snoc result)) := by
  simp only [Term.denoteOpenWith, gammaNode, Wires.read, Tuple.map, Kind.denoteWith, Part.bind_eq_bind]
  rfl

/-- Both alternatives of a θ body carry its returned token. Feedback uses
the whole carried tuple as the next entry. -/
theorem theta_denote (live : Origin (Threaded args) past runtime) (wires : Wires (Threaded args) past ins)
    (bodySigs : List (Ports (Ty V)))
    (children : Fin 1 → Term (Op P E Q) (Threaded ins) [] bodySigs (Threaded (Theta.BodyResults ins)))
    (rest : Term (Op P E Q) (Threaded args) (past ++ [Threaded ins]) sigs (Threaded outs))
    (entry : Tuple m.Val (Threaded args)) (locals : Locals m.Val past) :
    (Term.bind (ExplicitRuntime.thetaNode (Op := Op P E Q) live wires bodySigs) children rest).denoteOpenWith
      (model m pure) entry locals =
      (Elgot.iter (stepWith (fun x => (children 0).denoteOpenWith (model m pure) x PUnit.unit))
        (Wires.read (withRuntime live wires) entry locals)).bind
        (fun result => rest.denoteOpenWith (model m pure) entry (locals.snoc result)) := by
  simp only [Term.denoteOpenWith, ExplicitRuntime.thetaNode, Kind.denoteWith, Part.bind_eq_bind]
  rfl

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix
