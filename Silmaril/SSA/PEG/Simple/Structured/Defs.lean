module

public import Silmaril.SSA.PEG.Simple.While.Defs

/-! # Compositional SIMPLE to PEG lowering

Code extends a typed node context. A loop reserves its carried θ slots at
the body's entry, then emits a shared pass and an eval for every exit slot.
A loop ID is the number of its pass row. All other numbers are unused IDs.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Structured

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params before after vars inside ins all : List (Ty Data)} {t : Ty Data}

/-- A structured extension of a node table. Every constructor retains the old
context. Inside a loop the carried slots precede the old context. -/
inductive Code (P : InstructionSet.{u,v} Data) (params : List (Ty Data)) :
    List (Ty Data) → List (Ty Data) → Type (max u v) where
  | straight {before after : List (Ty Data)} (code : Simple.Code P params before after) : Code P params before after
  | seq {before mid after : List (Ty Data)} (a : Code P params before mid) (b : Code P params mid after) :
      Code P params before after
  | loop {before vars inside : List (Ty Data)} (init : Tuple (Port before) vars)
      (body : Code P params (vars ++ before) inside)
      (guard : Port inside .bool) (next : Tuple (Port inside) vars) (neg : P [.bool] .bool) :
      Code P params before (vars ++ .count :: .bool :: inside)

def insideRef (vars : List (Ty Data)) (p : Port inside t) :
    Port (vars ++ .count :: .bool :: inside) t :=
  portRight vars (.tail (.tail p))

def Code.lift : {before after : List (Ty Data)} → Code P params before after →
    Port before t → Port after t
  | _, _, .straight code, r => code.lift r
  | _, _, .seq a b, r => b.lift (a.lift r)
  | _, _, .loop (vars := vars) _ body _ _ _, r => insideRef vars (body.lift (portRight vars r))

def Code.liftRefs (code : Code P params before after) (refs : Tuple (Port before) ins) :
    Tuple (Port after) ins :=
  refs.map fun _ r => code.lift r

structure Build (P : InstructionSet.{u,v} Data) (params before outs : List (Ty Data)) where
  nodes : List (Ty Data)
  code : Code P params before nodes
  refs : Tuple (Port nodes) outs

def Build.straight (b : Simple.Build P params before vars) : Build P params before vars :=
  ⟨b.nodes, .straight b.code, b.refs⟩

def Build.thenBuild (a : Build P params before vars) (b : Build P params a.nodes ins) :
    Build P params before ins :=
  ⟨b.nodes, .seq a.code b.code, b.refs⟩

def expr (e : Expr P vars t) (ctx : Tuple (Port before) vars) : Build P params before [t] :=
  .straight (e.lower ctx)

/-- Lower all structured statements, with the interpreted Boolean negation
opcode supplied explicitly. -/
def lower (neg : P [.bool] .bool) :
    {vars outs : List (Ty Data)} → Stmt P true vars outs →
    {before : List (Ty Data)} → Tuple (Port before) vars → Build P params before outs
  | _, _, .assign e, _, ctx =>
    let b := expr (params := params) e ctx
    ⟨b.nodes, b.code, .cons (b.refs.get .head) (b.code.liftRefs ctx)⟩
  | _, _, .project refs, _, ctx => .straight (.keep (select ctx refs))
  | _, _, .seq first second, _, ctx =>
    let a := lower neg first ctx
    a.thenBuild (lower neg second a.refs)
  | _, _, .branch guard yes no, _, ctx =>
    let c := expr (params := params) guard ctx
    let entry := c.code.liftRefs ctx
    let y := lower neg yes entry
    let n := lower neg no (y.code.liftRefs entry)
    let selected := phiNodes (n.code.lift (y.code.lift (c.refs.get .head)))
      (n.code.liftRefs y.refs) n.refs
    c.thenBuild (y.thenBuild (n.thenBuild (.straight selected)))
  | vars, _, .while _ guard body, _, ctx =>
    let slots := (ports vars).map fun _ r => portLeft r
    let c := expr (params := params) guard slots
    let a := lower neg body (c.code.liftRefs slots)
    ⟨_, .loop ctx (.seq c.code a.code) (a.code.lift (c.refs.get .head)) a.refs neg,
      (ports vars).map fun _ r => portLeft r⟩

/-- A top-level while whose body may itself contain structured loops. -/
def whileProgram (guard : Expr P vars .bool) (body : Stmt P true vars vars)
    (ret : Port vars t) : Program P true vars t :=
  ⟨vars, .while rfl guard body, ret⟩

def program (p : Program P true params t) (neg : P [.bool] .bool) : Build P params [] [t] :=
  let init := Build.straight (paramNodes (ports params))
  let body := lower neg p.body init.refs
  init.thenBuild ⟨body.nodes, body.code, .cons (body.refs.get p.retvar) .nil⟩

/-- The references in a row address the final node table. Only pass rows
record a parent, which is the pass address of the enclosing loop. -/
structure Row (P : InstructionSet.{u,v} Data) (params nodes : List (Ty Data)) (t : Ty Data) where
  inputs : List (Ty Data)
  label : Label P params (Fin nodes.length) inputs t
  refs : Tuple (Port nodes) inputs
  parent : Option (Fin nodes.length) := none

def passLoop {L : Type} : Label P params L ins t → Option L
  | .pass l => some l
  | _ => none

abbrev Embed (nodes all : List (Ty Data)) := ∀ {t}, Port nodes t → Port all t
abbrev Rows (P : InstructionSet.{u,v} Data) (params nodes all : List (Ty Data)) :=
  ∀ {t}, Port nodes t → Row P params all t

def straightRows (holes : Rows P params before all) :
    {after : List (Ty Data)} → Simple.Code P params before after → Embed after all → Rows P params after all
  | _, .empty, _ => holes
  | _, .emit code label refs, embed =>
    portConsCases
      ⟨_, label.map (fun op => op) Fin.elim0, refs.map fun _ r => embed (.tail r), none⟩
      (straightRows holes code (fun r => embed (.tail r)))

def passRef (vars : List (Ty Data)) : Port (vars ++ .count :: .bool :: inside) .count :=
  portRight vars .head

def negRef (vars : List (Ty Data)) : Port (vars ++ .count :: .bool :: inside) .bool :=
  portRight vars (.tail .head)

def loopHoles (body : Code P params (vars ++ before) inside)
    (init : Tuple (Port before) vars) (next : Tuple (Port inside) vars)
    (holes : Rows P params before all) (embed : Embed (vars ++ .count :: .bool :: inside) all) :
    Rows P params (vars ++ before) all :=
  fun r => match portSplit vars r with
    | .inl slot =>
      ⟨_, .theta (numberPort (embed (passRef vars))).id,
        .cons (embed (insideRef vars (body.lift (portRight vars (init.get slot)))))
          (.cons (embed (insideRef vars (next.get slot))) .nil), none⟩
    | .inr old => holes old

def loopRows (body : Code P params (vars ++ before) inside)
    (guard : Port inside .bool) (neg : P [.bool] .bool)
    (parent : Option (Fin all.length)) (embed : Embed (vars ++ .count :: .bool :: inside) all)
    (inner : Rows P params inside all) : Rows P params (vars ++ .count :: .bool :: inside) all :=
  let pass := numberPort (embed (passRef vars))
  fun r => match portSplit vars r with
    | .inl slot =>
      ⟨_, .eval pass.id,
        .cons (embed (insideRef vars (body.lift (portLeft slot))))
          (.cons (embed (passRef vars)) .nil), none⟩
    | .inr r =>
      portConsCases ⟨_, .pass pass.id, .cons (embed (negRef vars)) .nil, parent⟩
        (portConsCases ⟨_, .op neg, .cons (embed (insideRef vars guard)) .nil, none⟩ inner) r

def Code.rows :
    {before after : List (Ty Data)} → Code P params before after → Rows P params before all →
    Embed after all → Option (Fin all.length) → Rows P params after all
  | _, _, .straight code, holes, embed, _ => straightRows holes code embed
  | _, _, .seq a b, holes, embed, parent =>
    b.rows (a.rows holes (fun r => embed (b.lift r)) parent) embed parent
  | _, _, .loop (vars := vars) init body guard next neg, holes, embed, parent =>
    let pass := (numberPort (embed (passRef vars))).id
    loopRows body guard neg parent embed
      (body.rows (loopHoles body init next holes embed) (fun r => embed (insideRef vars r)) (some pass))

def Code.toGraph {outs : List (Ty Data)} (code : Code P params [] after)
    (outputs : Tuple (Port after) outs) : Graph P params outs after.length after.length :=
  let rows : Rows P params after after := code.rows (fun r => nomatch r) (fun r => r) none
  { forest := ⟨fun i => (rows (portAt after i)).parent⟩
    sort := fun i => after[i]
    node := fun i =>
      let row : Row P params after after[i] := rows (portAt after i)
      .ofLabel row.label (row.refs.map fun _ r => numberPort r)
    roots := outputs.map fun _ r => numberPort r }

/-- At each row boundary, compare the side of the cut before its loop
counter. Only pass addresses can label feedback or sampling edges. -/
def rank (n : Nat) : DemandRank n n :=
  (List.finRange n).flatMap fun j =>
    [.phase (fun i => if i.val ≤ j.val then 1 else 0), .counter j]

def translate (p : Program P true params t) (neg : P [.bool] .bool) :
    Graph P params [t] (program p neg).nodes.length (program p neg).nodes.length :=
  (program p neg).code.toGraph (program p neg).refs

end Silmaril.SSA.PEG.Simple.Structured
