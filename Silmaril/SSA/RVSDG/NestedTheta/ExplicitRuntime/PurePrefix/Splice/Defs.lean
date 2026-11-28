module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Defs

/-! # Attach an ordered continuation to a checked mixed producer -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice

open OrderedRuntime.Structured (Ty Data Threaded runtime)

universe u v
variable {V : Type u} {P E Q : Dialect.{u,v} V PUnit.{u+1}}
variable {args middle outs : Ports (Ty V)}
variable {past sigs after : List (Ports (Ty V))}
variable {a : Data args} {b : Data middle} {c : Data outs}

/-- Splice at the mixed producer's return. Child scopes keep their original
numbering, and the continuation reads the sole returned token. -/
def appendOrdered {second : Term (Ordered P E) (Threaded middle) [] after (Threaded outs)}
    (consumer : ExplicitRuntime.EntryChecked (a := b) (b := c) second) :
    {past sigs : List (Ports (Ty V))} → {live : Origin (Threaded args) past runtime} →
    {first : Term (Op P E Q) (Threaded args) past sigs (Threaded middle)} →
    Checked P E Q a b live first → Code P E Q a c live (sigs ++ after)
  | _, _, _, _, .ordered producer => lift (ExplicitRuntime.Splice.append consumer producer).2
  | _, _, _, _, .ret live values => attach consumer live values
  | _, _, _, _, .pure live i o op values rest =>
    ⟨_, .pure live i o op values (appendOrdered consumer rest).2⟩
  | _, _, _, _, .primitive live i o op values rest =>
    ⟨_, .primitive live i o op values (appendOrdered consumer rest).2⟩
  | _, _, _, _, .gamma extra choice live i o values rows arms rest =>
    ⟨_, .gamma extra choice live i o values rows arms (appendOrdered consumer rest).2⟩
  | _, _, _, _, .theta live i values rows body rest =>
    ⟨_, .theta live i values rows body (appendOrdered consumer rest).2⟩

/-- The mixed producer and ordered consumer form one numbered graph. -/
def graph {first : Graph (Op P E Q) (Threaded args) [] sigs (Threaded middle)}
    {second : Graph (Ordered P E) (Threaded middle) [] after (Threaded outs)}
    (producer : EntryChecked (a := a) (b := b) first.toTerm)
    (consumer : ExplicitRuntime.EntryChecked (a := b) (b := c) second.toTerm) :
    Graph (Op P E Q) (Threaded args) [] (sigs ++ after) (Threaded outs) :=
  (appendOrdered consumer producer).1.toGraph

def graphChecked {first : Graph (Op P E Q) (Threaded args) [] sigs (Threaded middle)}
    {second : Graph (Ordered P E) (Threaded middle) [] after (Threaded outs)}
    (producer : EntryChecked (a := a) (b := b) first.toTerm)
    (consumer : ExplicitRuntime.EntryChecked (a := b) (b := c) second.toTerm) :
    EntryChecked (a := a) (b := c) (graph producer consumer).toTerm :=
  (NestedTheta.Term.toTerm_toGraph _).symm ▸ (appendOrdered consumer producer).2

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix.Splice
