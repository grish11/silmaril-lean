module

public import Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.Splice.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Equality.Defs

/-! # Checked data-only bindings before an ordered nested region -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix

open OrderedRuntime.Structured (Ty Data Threaded runtime runtimePort nextRuntime Instruction)
open RVSDG.Institution (OpcodeMap)
open NestedTheta.Institution (mapTerm)
open Splice (weaken)

universe u v w
variable {V : Type u} {P E Q : Dialect.{u,v} V PUnit.{u+1}}
variable {args outs ins out middle : Ports (Ty V)}
variable {past sigs : List (Ports (Ty V))}

abbrev Ordered (P E : Dialect.{u,v} V PUnit.{u+1}) := OrderedRuntime.Structured.Opcode P E

inductive Op (P E Q : Dialect.{u,v} V PUnit.{u+1}) : Dialect.{u,max u v} V PUnit.{u+1} where
  | ordered {ins outs : Ports (Ty V)} : Ordered P E ins outs → Op P E Q ins outs
  | pure {ins outs : Ports (Ty V)} : Data ins → Data outs → Q ins outs → Op P E Q ins outs

def orderedMap : OpcodeMap (Ordered P E) (Op P E Q) := fun op => .ordered op

abbrev pureNode (di : Data ins) (do' : Data out) (op : Q ins out)
    (wires : Wires args past ins) : Node (Op P E Q) args past out :=
  ⟨ins, .base (.simple (.pure di do' op)), wires, fun j => j.elim0⟩

abbrev orderedNode (live : Origin args past runtime) (di : Data ins) (do' : Data out)
    (op : Instruction P E ins out) (wires : Wires args past ins) :
    Node (Op P E Q) args past (Threaded out) :=
  ⟨Threaded ins, .base (.simple (.ordered (.ordered di do' op))),
    OrderedRuntime.Structured.withRuntime live wires, fun j => j.elim0⟩

abbrev pureBind (di : Data ins) (do' : Data out) (op : Q ins out) (wires : Wires args past ins)
    (rest : Term (Op P E Q) args (past ++ [out]) sigs outs) : Term (Op P E Q) args past (out :: sigs) outs :=
  .bind (pureNode di do' op wires) (fun j => j.elim0) rest

abbrev orderedBind (live : Origin args past runtime) (di : Data ins) (do' : Data out)
    (op : Instruction P E ins out) (wires : Wires args past ins)
    (rest : Term (Op P E Q) args (past ++ [Threaded out]) sigs outs) :
    Term (Op P E Q) args past (Threaded out :: sigs) outs :=
  .bind (orderedNode live di do' op wires) (fun j => j.elim0) rest

abbrev gammaNode (extra : Nat) (choice : Origin args past (.control (extra + 2)))
    (live : Origin args past runtime) (wires : Wires args past ins)
    (childSigs : Fin (extra + 2) → List (Ports (Ty V))) : Node (Op P E Q) args past (Threaded out) :=
  ⟨.control (extra + 2) :: Threaded ins, .base (.gamma extra),
    .cons choice (OrderedRuntime.Structured.withRuntime live wires), childSigs⟩

/-- A token-free binding keeps the current live origin in any scope. A γ
or θ child starts from its argument token and returns its own final token.
An all-ordered subtree can still be admitted by the existing checker. -/
inductive Checked (P E Q : Dialect.{u,v} V PUnit.{u+1}) :
    {args outs : Ports (Ty V)} → Data args → Data outs →
    {past sigs : List (Ports (Ty V))} → Origin (Threaded args) past runtime →
    Term (Op P E Q) (Threaded args) past sigs (Threaded outs) → Type (max u v) where
  | ordered {args outs : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past sigs : List (Ports (Ty V))} {live : Origin (Threaded args) past runtime}
      {term : Term (Ordered P E) (Threaded args) past sigs (Threaded outs)} :
      ExplicitRuntime.Checked P E a b live term → Checked P E Q a b live (mapTerm orderedMap term)
  | ret {args outs : Ports (Ty V)} {a : Data args} {b : Data outs} {past : List (Ports (Ty V))}
      (live : Origin (Threaded args) past runtime) (wires : Wires (Threaded args) past outs) :
      Checked P E Q a b live (.ret (OrderedRuntime.Structured.withRuntime live wires))
  | pure {args outs ins out : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past sigs : List (Ports (Ty V))}
      (live : Origin (Threaded args) past runtime) (di : Data ins) (do' : Data out)
      (op : Q ins out) (wires : Wires (Threaded args) past ins)
      {rest : Term (Op P E Q) (Threaded args) (past ++ [out]) sigs (Threaded outs)} :
      Checked P E Q a b (weaken out live) rest →
      Checked P E Q a b live (pureBind di do' op wires rest)
  | primitive {args outs ins out : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past sigs : List (Ports (Ty V))}
      (live : Origin (Threaded args) past runtime) (di : Data ins) (do' : Data out)
      (op : Instruction P E ins out) (wires : Wires (Threaded args) past ins)
      {rest : Term (Op P E Q) (Threaded args) (past ++ [Threaded out]) sigs (Threaded outs)} :
      Checked P E Q a b (nextRuntime past out) rest →
      Checked P E Q a b live (orderedBind live di do' op wires rest)
  | gamma {args outs ins out : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past sigs : List (Ports (Ty V))}
      (extra : Nat) (choice : Origin (Threaded args) past (.control (extra + 2)))
      (live : Origin (Threaded args) past runtime) (i : Data ins) (o : Data out)
      (wires : Wires (Threaded args) past ins) (childSigs : Fin (extra + 2) → List (Ports (Ty V)))
      {children : ∀ j, Term (Op P E Q) (Threaded ins) [] (childSigs j) (Threaded out)}
      {rest : Term (Op P E Q) (Threaded args) (past ++ [Threaded out]) sigs (Threaded outs)} :
      (∀ j, Checked P E Q i o (.arg (runtimePort ins)) (children j)) →
      Checked P E Q a b (nextRuntime past out) rest →
      Checked P E Q a b live (.bind (gammaNode (out := out) extra choice live wires childSigs) children rest)
  | theta {args outs ins : Ports (Ty V)} {a : Data args} {b : Data outs}
      {past sigs : List (Ports (Ty V))}
      (live : Origin (Threaded args) past runtime) (i : Data ins)
      (wires : Wires (Threaded args) past ins) (bodySigs : List (Ports (Ty V)))
      {children : Fin 1 → Term (Op P E Q) (Threaded ins) [] bodySigs (Threaded (Theta.BodyResults ins))}
      {rest : Term (Op P E Q) (Threaded args) (past ++ [Threaded ins]) sigs (Threaded outs)} :
      (∀ j, Checked P E Q i (.control i) (.arg (runtimePort ins)) (children j)) →
      Checked P E Q a b (nextRuntime past ins) rest →
      Checked P E Q a b live (.bind (ExplicitRuntime.thetaNode live wires bodySigs) children rest)

variable {a : Data args} {b : Data middle} {c : Data outs}

abbrev Code (P E Q : Dialect.{u,v} V PUnit.{u+1}) (a : Data args) (b : Data outs)
    (live : Origin (Threaded args) past runtime) (sigs : List (Ports (Ty V))) :=
  Σ t : Term (Op P E Q) (Threaded args) past sigs (Threaded outs), Checked P E Q a b live t

abbrev EntryChecked {a : Data args} {b : Data outs}
    (t : Term (Op P E Q) (Threaded args) [] sigs (Threaded outs)) :=
  Checked P E Q a b (.arg (runtimePort args)) t

def lift {t : Term (Ordered P E) (Threaded args) past sigs (Threaded outs)}
    {live : Origin (Threaded args) past runtime} (h : ExplicitRuntime.Checked P E a c live t) :
    Code P E Q a c live sigs := ⟨_, .ordered h⟩

/-- Connect an ordered continuation using the current data and live token. -/
def attach {t : Term (Ordered P E) (Threaded middle) [] sigs (Threaded outs)}
    (h : ExplicitRuntime.EntryChecked (a := b) (b := c) t)
    (live : Origin (Threaded args) past runtime) (wires : Wires (Threaded args) past middle) :
    Code P E Q a c live sigs :=
  lift (Splice.append h (.ret live wires : ExplicitRuntime.Checked P E a b live
    (.ret (OrderedRuntime.Structured.withRuntime live wires)))).2

variable (m : Partial.Model.{u,max u v,w} (Ordered P E))

abbrev Total (m : Partial.Model.{u,max u v,w} (Ordered P E)) (Q : Dialect.{u,v} V PUnit.{u+1}) :=
  {ins outs : Ports (Ty V)} → Q ins outs → Tuple m.Val ins → Tuple m.Val outs

def model (pure : Total m Q) : Partial.Model.{u,max u v,w} (Op P E Q) where
  value := m.value
  snapshot := m.snapshot
  primitive
    | .ordered op, input => m.primitive op input
    | .pure _ _ op, input => Part.some (pure op input)

def actions (pure : Total m Q) (base : Partial.Executable.Actions m) :
    Partial.Executable.Actions (model m pure) where
  primitive
    | .ordered op, input => base.primitive op input
    | .pure _ _ op, input => some (pure op input)
  agrees
    | .ordered op, input => base.agrees op input
    | .pure _ _ _, _ => rfl

def opcodeCode (ordered : Equality.OpcodeCode (Ordered P E)) (pure : Equality.OpcodeCode Q) :
    Equality.OpcodeCode (Op P E Q) where
  Key := Sum ordered.Key pure.Key
  encode
    | .ordered op => .inl (ordered.encode op)
    | .pure _ _ op => .inr (pure.encode op)
  injective := by
    intro ins outs x y same
    cases x with
    | ordered op =>
      cases y with
      | ordered op' => exact congrArg Op.ordered (ordered.injective op op' (Sum.inl.inj same))
      | pure _ _ _ => cases same
    | pure di do' op =>
      cases y with
      | ordered _ => cases same
      | pure _ _ op' => exact congrArg (Op.pure di do') (pure.injective op op' (Sum.inr.inj same))

end Silmaril.SSA.RVSDG.NestedTheta.ExplicitRuntime.PurePrefix
