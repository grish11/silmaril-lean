module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice.Agreement

/-! # Partial observations of a checked mixed splice -/

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice

open OrderedRuntime.Structured (Ty Data Threaded runtime)

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
        second.denoteOpenWith m mid PUnit.unit :=
  Proofs.append_denote m pureValue producer consumer entry loc

/-- The continuation only runs after the mixed producer returns, and reads
the producer's complete numbered result including its final token. -/
theorem graph_observe (m : Partial.Model.{u,max u v,w} (Ordered P E)) (pureValue : Total m Q)
    {first : Graph (Op P E Q) (Threaded args) [] sigs (Threaded middle)}
    {second : Graph (Ordered P E) (Threaded middle) [] after (Threaded outs)}
    (producer : EntryChecked (a := a) (b := b) first.toTerm)
    (consumer : ExplicitRuntime.EntryChecked (a := b) (b := c) second.toTerm)
    (entry : Tuple m.Val (Threaded args)) :
    Partial.observe (model m pureValue) (graph producer consumer) entry =
      Partial.observe (model m pureValue) first entry >>= Partial.observe m second := by
  simp only [Partial.observe, graph, Term.toTerm_toGraph]
  exact append_denote m pureValue producer consumer entry PUnit.unit

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice
