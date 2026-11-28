module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Defs

/-! A typed observation cut of an existing firing region. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri

universe u v w

open RVSDG.Petri (Tokens)
open Relation (ReflTransGen)

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args head bank outs : Ports (PortType V S)}
variable {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))}

/-- The prefix and the whole term share their vertices and child terms.
The prefix reads selected wires where the whole term continues. -/
inductive Cut {Op : Dialect.{u, v} V S} {args bank outs : Ports (PortType V S)} :
    {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))} →
    Term Op args past frontSigs bank → Term Op args past wholeSigs outs →
    Term Op args (extend past frontSigs) tailSigs outs → Type (max u v)
  | stop {past sigs : List (Ports (PortType V S))} (wires : Wires args past bank)
      (tail : Term Op args past sigs outs) : Cut (.ret wires) tail tail
  | bind {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))}
      {head : Ports (PortType V S)} (node : Node Op args past head) (children : Children (Term Op) node)
      {front : Term Op args (past ++ [head]) frontSigs bank} {whole : Term Op args (past ++ [head]) wholeSigs outs}
      {tail : Term Op args (extend (past ++ [head]) frontSigs) tailSigs outs}
      (cut : Cut front whole tail) : Cut (.bind node children front) (.bind node children whole) tail

variable (m : Model.{u, v, w} Op)

/-- Assemble a whole marking from the actual prefix and continuation places. -/
def Cut.attach :
    {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))} →
    {front : Term Op args past frontSigs bank} → {whole : Term Op args past wholeSigs outs} →
    {tail : Term Op args (extend past frontSigs) tailSigs outs} →
    Cut front whole tail → Marking m front → Marking m tail → Marking m whole
  | _, _, _, _, _, _, _, .stop .., _, rest => rest
  | _, _, _, _, _, _, _, .bind _ _ cut, mark, rest => (mark.1, cut.attach mark.2 rest)

/-- Read the prefix marking from the original whole term. -/
def Cut.observe :
    {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))} →
    {front : Term Op args past frontSigs bank} → {whole : Term Op args past wholeSigs outs} →
    {tail : Term Op args (extend past frontSigs) tailSigs outs} →
    Cut front whole tail → Marking m whole → Marking m front
  | _, _, _, _, _, _, _, .stop .., _ => PUnit.unit
  | _, _, _, _, _, _, _, .bind _ _ cut, mark => (mark.1, cut.observe mark.2)

/-- The continuation sees just the colours marked by the prefix. -/
def Cut.tokens :
    {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))} →
    {front : Term Op args past frontSigs bank} → {whole : Term Op args past wholeSigs outs} →
    {tail : Term Op args (extend past frontSigs) tailSigs outs} →
    Cut front whole tail → Tokens m.Val past → Marking m front → Tokens m.Val (extend past frontSigs)
  | _, _, _, _, _, _, _, .stop .., tokens, _ => tokens
  | _, _, _, _, _, _, _, .bind _ _ cut, tokens, mark => cut.tokens (tokens.snoc mark.1.outputs) mark.2

def Cut.wires :
    {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))} →
    {front : Term Op args past frontSigs bank} → {whole : Term Op args past wholeSigs outs} →
    {tail : Term Op args (extend past frontSigs) tailSigs outs} →
    Cut front whole tail → Wires args (extend past frontSigs) bank
  | _, _, _, _, _, _, _, .stop wires _ => wires
  | _, _, _, _, _, _, _, .bind _ _ cut => cut.wires

/-- A finite legal firing of the whole term exposes all the prefix's
result colours at the designated cut. -/
def Cut.Reads {front : Term Op args [] frontSigs bank} {whole : Term Op args [] wholeSigs outs}
    {tail : Term Op args (extend [] frontSigs) tailSigs outs} (cut : Cut front whole tail)
    (entry : Tuple m.Val args) (output : Tuple m.Val bank) : Prop :=
  ∃ mark, ReflTransGen (Fire m whole entry PUnit.unit) (pending m whole) mark ∧
    finished m front entry PUnit.unit (cut.observe m mark) = some output

end Silmaril.SSA.RVSDG.NestedTheta.Petri
