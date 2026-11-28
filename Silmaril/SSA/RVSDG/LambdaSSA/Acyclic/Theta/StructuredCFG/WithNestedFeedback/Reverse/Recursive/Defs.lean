module

public import Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Defs

/-! # Graph-only recovery of canonical mixed structured regions -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive

open Sequential
open Sequential.Flat.Serial (Joined WirePorts)
open Sequential.Flat.Serial.Recognize (Mark Output mark)
open Sequential.Flat.Numbered.Recognize (RightAssociated)
open NestedFeedback.Reverse (Key readTheta readOuterWith)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {τ Φ : Type u} [TypeFormers τ] [HasTy Φ τ]
variable {A B K X Z U V M Y I J L E D : τ}
variable {ps qs ts sigs : List (Ports (OrderedRuntime.Structured.Ty τ))}

/-- An ordinary leaf contains a loop with an acyclic instruction body.
A feedback leaf contains the existing two-header nested loop. -/
inductive LeafView (Φ : Type u) [HasTy Φ τ] :
    τ → τ → τ → List (Ports (OrderedRuntime.Structured.Ty τ)) → Type u where
  | localLoop {A B K E D : τ} (s : Loop Φ A B K E D) : LeafView Φ A E D [WirePorts A E D]
  | feedback {A B K M : τ} (s : NestedFeedback.Loop Φ A B K M) : LeafView Φ A M M (Leaf.Sigs A M)

def LeafView.toSyntax : {A X Z : τ} → {ps : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    LeafView Φ A X Z ps → Syntax Φ A X Z A X Z ps
  | _, _, _, _, .localLoop s => .structured (.loop s)
  | _, _, _, _, .feedback s => .nested s

/-- Serials associate to the right and each fork owns its entire suffix.
Both arms and the suffix independently use this same grammar. -/
inductive Normal (Φ : Type u) [HasTy Φ τ] :
    τ → τ → τ → τ → τ → τ → List (Ports (OrderedRuntime.Structured.Ty τ)) → Type u where
  | leaf {A X Z : τ} {ps : List (Ports (OrderedRuntime.Structured.Ty τ))} (p : LeafView Φ A X Z ps) : Normal Φ A X Z A X Z ps
  | seq {A M I J L E D : τ} {ps qs : List (Ports (OrderedRuntime.Structured.Ty τ))}
      (p : LeafView Φ A M M ps) (q : Normal Φ M I J L E D qs) :
      Normal Φ A M M L E D (Joined M I J ps qs)
  | fork {A X Z U V M Y I J L E D : τ} {ps qs ts : List (Ports (OrderedRuntime.Structured.Ty τ))}
      (gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y))
      (p : Normal Φ M M M U M M ps) (q : Normal Φ Y M M V M M qs)
      (k : Normal Φ M I J L E D ts) : Normal Φ A X Z L E D (Selection M Y I J ++ ts)

def Normal.toSyntax : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Normal Φ A X Z L E D sigs → Syntax Φ A X Z L E D sigs
  | _, _, _, _, _, _, _, .leaf p => p.toSyntax
  | _, _, _, _, _, _, _, .seq p q => .link p.toSyntax q.toSyntax
  | _, _, _, _, _, _, _, .fork gate p q k => .branch gate p.toSyntax q.toSyntax k.toSyntax

def LeafView.Supported : {A X Z : τ} → {ps : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    LeafView Φ A X Z ps → Prop
  | _, _, _, _, .localLoop s => RightAssociated s.body
  | _, _, _, _, .feedback _ => True

/-- Local instruction sequences use the shared body's right association. -/
def Normal.Supported : {A X Z L E D : τ} → {sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    Normal Φ A X Z L E D sigs → Prop
  | _, _, _, _, _, _, _, .leaf p => p.Supported
  | _, _, _, _, _, _, _, .seq p q => p.Supported ∧ q.Supported
  | _, _, _, _, _, _, _, .fork _ p q k => p.Supported ∧ q.Supported ∧ k.Supported

inductive Entry (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] where
  | atom (mark : Mark τ Φ)
  | enter (input join : τ)
  | feedback (keys : Key τ Φ × Key τ Φ × Key τ Φ)
  | leave (input join : τ)
  | route (carry bypass handoff result : τ)
  | classifier {A X Y : τ} (op : TwoBlock.Instruction Φ A (Silmaril.coprod X Y))
  | fork (left right : List (Entry τ Φ))

abbrev Layout (τ Φ : Type u) [TypeFormers τ] [HasTy Φ τ] := List (Entry τ Φ)

def readEntry : {ins outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    (kind : NestedTheta.Kind (Wires.Op Φ) ins outs) →
    {children : Fin kind.arity → List (Ports (OrderedRuntime.Structured.Ty τ))} →
    ((j : Fin kind.arity) → NestedTheta.Term (Wires.Op Φ) kind.entry [] (children j) kind.exit) →
    (Fin kind.arity → Option (Layout τ Φ)) → Option (Entry τ Φ)
  | _, _, .base (.gamma 0), _, _, scopes => do
    return .fork (← scopes (0 : Fin 2)) (← scopes (1 : Fin 2))
  | _, _, (.base (.simple opcode)), sigs, children, _ =>
    match readOpcode (.base (.simple opcode)) with
    | some (.enterNested a m) => some (.enter a m)
    | some (.exitNested a m) => some (.leave a m)
    | some (.routeExit h e m d) => some (.route h e m d)
    | _ =>
      match Wires.Reverse.readKind (.base (.simple opcode)) (fun _ => none) with
      | some (.classifier op) => some (.classifier op)
      | _ => .atom <$> mark (.base (.simple opcode)) (childSigs := sigs) children
  | _, _, kind, sigs, children, _ =>
    match readTheta kind (sigs := sigs) children (readOuterWith readNested) with
    | some labels => some (.feedback labels)
    | none => .atom <$> mark kind (childSigs := sigs) children

/-- Follow actual child scopes. The label scan leaves addresses to the one
whole-graph comparison at certification. -/
def scan : {args outs : Ports (OrderedRuntime.Structured.Ty τ)} →
    {past sigs : List (Ports (OrderedRuntime.Structured.Ty τ))} →
    NestedTheta.Term (Wires.Op Φ) args past sigs outs → Option (Layout τ Φ)
  | _, _, _, _, .ret _ => some []
  | _, _, _, _, .bind node children rest => do
    let head ← readEntry node.kind children (fun j => scan (children j))
    return head :: (← scan rest)

/-- Termination budget derived from the graph's scanned outer and child tables. -/
def weight : Layout τ Φ → Nat
  | [] => 0
  | .fork left right :: rest => weight left + weight right + weight rest + 1
  | _ :: rest => weight rest + 1
termination_by layout => sizeOf layout
decreasing_by all_goals (simp_wf; omega)

abbrev Parsed (Φ : Type u) [HasTy Φ τ] (A X Z : τ) :=
  Σ out : Output τ, Normal Φ A X Z out.carry out.left out.right out.sigs

def pack (n : Normal Φ A X Z L E D sigs) : Parsed Φ A X Z := ⟨⟨L,E,D,sigs⟩, n⟩

variable [DecidableEq τ]

def expect (parsed : Parsed Φ A X Z) (carry e d : τ) :
    Option (Σ sigs, Normal Φ A X Z carry e d sigs) :=
  let ⟨out,n⟩ := parsed
  if hc : out.carry = carry then
    if he : out.left = e then
      if hd : out.right = d then some ⟨out.sigs, hc ▸ he ▸ hd ▸ n⟩ else none
    else none
  else none

/-- Pop a typed arm's outgoing connector, checking the external payload sort. -/
def splitArm (arm : Layout τ Φ) (m : τ) :
    Option (StructuredCFG.Reverse.CutTag τ × Layout τ Φ) :=
  match arm.reverse with
  | .atom (.cut carry payload i j) :: rest =>
    if payload = m then some (⟨carry,i,j⟩,rest.reverse) else none
  | _ => none

def readLeaf (A X Z : τ) : Layout τ Φ →
    Option ((Σ sigs, LeafView Φ A X Z sigs) × Layout τ Φ)
  | .atom (.loop steps labels) :: rest => do
    let ⟨_, _, s⟩ ← Flat.Numbered.Recognize.loop steps A X Z labels
    return (⟨_, .localLoop s⟩, rest)
  | .enter a m :: .feedback keys :: .leave b n :: rest =>
    if (a, b, n) = (A, A, m) ∧ m = X then
      if hz : X = Z then do
        let ⟨_, _, s⟩ ← NestedFeedback.Reverse.decode (A := A) (D := X) keys
        let leaf := Eq.mp (congrArg (fun z => LeafView Φ A X z (Leaf.Sigs A X)) hz) (.feedback s)
        return (⟨_, leaf⟩, rest)
      else none
    else none
  | _ => none

def parse : Nat → (A X Z : τ) → Layout τ Φ → Option (Parsed Φ A X Z)
  | 0, _, _, _, _ => none
  | fuel + 1, A, _, _,
      .classifier (A := a) (X := x) (Y := y) op ::
        .fork (.atom (.cut Y M x' z') :: left) right :: rest =>
    if ha : a = A then
      if ho : Silmaril.coprod x y = ChoiceCarrier M Y then
        if (x',z') = (M,M) then do
          let (l, leftMarks) ← splitArm left M
          let (r, rightMarks) ← splitArm right M
          if (l.left,l.right) = (r.left,r.right) then
            let ⟨_, p⟩ ← expect (← parse fuel M M M leftMarks) l.carry M M
            let ⟨_, q⟩ ← expect (← parse fuel Y M M rightMarks) r.carry M M
            let ⟨_, k⟩ ← parse fuel M l.left l.right rest
            let gate : TwoBlock.Instruction Φ A (ChoiceCarrier M Y) := ha ▸ ho ▸ op
            return pack (.fork gate p q k)
          else none
        else none
      else none
    else none
  | fuel + 1, A, X, Z, layout => do
    let (⟨_, leaf⟩, rest) ← readLeaf A X Z layout
    match rest with
    | [] => return pack (.leaf leaf)
    | .atom (.cut h m i j) :: tail =>
      if h = A then
        if hx : X = m then
          if hz : Z = m then do
            let ⟨_, next⟩ ← parse fuel m i j tail
            let joined : Parsed Φ A m m := pack (.seq (hx ▸ hz ▸ leaf) next)
            return hx.symm ▸ hz.symm ▸ joined
          else none
        else none
      else none
    | _ => none

def decodeLayout (labels : Layout τ Φ) : Option (Normal Φ A X Z L E D sigs) := do
  let ⟨out, n⟩ ← parse (weight labels) A X Z labels
  if eq : out = (⟨L,E,D,sigs⟩ : Output τ) then
    some (Eq.mp (congrArg (fun ix => Normal Φ A X Z ix.carry ix.left ix.right ix.sigs) eq) n)
  else none

def candidate (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (Normal Φ A X Z L E D sigs) :=
  (scan g.toTerm).bind decodeLayout

variable [DecidableEq Φ]

/-- Certify every operand, result, capture and token wire under the original numbering. -/
def recognize (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (Decomposition g) :=
  candidate g >>= fun n => certify g n.toSyntax

/-- Recover the actual flat CFG and its checked relation to the input graph. -/
def recover (g : Flat.Serial.Graph Φ A X Z L E D sigs) : Option (Fibre g) :=
  (recognize g).map Decomposition.raise

end Silmaril.SSA.RVSDG.LambdaSSA.Acyclic.Theta.StructuredCFG.WithNestedFeedback.Reverse.Recursive
