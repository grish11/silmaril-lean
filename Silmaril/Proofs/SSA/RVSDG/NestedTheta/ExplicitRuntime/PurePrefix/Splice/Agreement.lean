module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Thms

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Proofs

open OrderedRuntime.Structured (Ty Data Threaded runtime)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w
variable {V : Type u} {P E Q : Dialect.{u,v} V PUnit.{u+1}}
variable {args middle outs : Ports (Ty V)}
variable {past sigs after : List (Ports (Ty V))}
variable {a : Data args} {b : Data middle} {c : Data outs}

theorem append_denote (m : Partial.Model.{u,max u v,w} (Ordered P E)) (pureValue : Total m Q)
    {first : Term (Op P E Q) (Threaded args) past sigs (Threaded middle)}
    {second : Term (Ordered P E) (Threaded middle) [] after (Threaded outs)}
    {live : Origin (Threaded args) past runtime} (producer : Checked P E Q a b live first)
    (consumer : ExplicitRuntime.EntryChecked (a := b) (b := c) second)
    (entry : Tuple m.Val (Threaded args)) (loc : Locals m.Val past) :
    (appendOrdered consumer producer).1.denoteOpenWith (model m pureValue) entry loc =
      first.denoteOpenWith (model m pureValue) entry loc >>= fun mid =>
        second.denoteOpenWith m mid PUnit.unit := by
  induction producer with
  | ordered producer =>
    rw [appendOrdered, lift_denote, ExplicitRuntime.Splice.append_denote]
    exact congrArg (fun result => result >>= fun mid => second.denoteOpenWith m mid PUnit.unit)
      (lift_denote m pureValue producer entry loc).symm
  | ret live values =>
    simp only [appendOrdered, attach_denote, Term.denoteOpenWith, pure_bind]
  | pure live i o op values rest ih =>
    simp only [appendOrdered, Term.denoteOpenWith, bind_assoc]
    congr 1
    funext result
    exact ih consumer entry (loc.snoc result)
  | primitive live i o op values rest ih =>
    simp only [appendOrdered, Term.denoteOpenWith, bind_assoc]
    congr 1
    funext result
    exact ih consumer entry (loc.snoc result)
  | gamma extra choice live i o values rows arms rest inner outer =>
    simp only [appendOrdered, Term.denoteOpenWith, bind_assoc]
    congr 1
    funext result
    exact outer consumer entry (loc.snoc result)
  | theta live i values rows body rest inner outer =>
    simp only [appendOrdered, Term.denoteOpenWith, bind_assoc]
    congr 1
    funext result
    exact outer consumer entry (loc.snoc result)

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Proofs
