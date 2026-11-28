module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Inversion.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Inversion.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Replay.Defs

/-! A checked scanner over the original numbered θ markings.
The initial pending marking is implicit in the input log. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG (Tuple)
open RVSDG.NestedTheta (Term)
open RVSDG.NestedTheta.Petri (Fire Marking finished pending)
open RVSDG.NestedTheta.Petri.Replay (checkFire markingDecEq tupleDecEq)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

abbrev RootMark := Marking semantics (emitted p)
abbrev BodyMark := Marking semantics (thetaBody p)
abbrev preheader (_p : Program src entry) := Term.ofBase (entryCode (src := src) (entry := entry))
abbrev PreMark := Marking semantics (preheader p)
abbrev RootFire := Fire semantics (emitted p) input PUnit.unit
abbrev BodyFire (old : Bank (regs := regs) model) := Fire semantics (thetaBody p) old PUnit.unit

def colourEq : (t : SeaOfNodes.Diamond.Ty Width) → DecidableEq (semantics.Val t)
  | .value .predicate => inferInstanceAs (DecidableEq (ULift Bool))
  | .value (.data _) => inferInstanceAs (DecidableEq (BitVec _))
  | .control _ => inferInstanceAs (DecidableEq (ULift (Fin _)))
  | .state impossible => nomatch impossible

def entryBank := (src entry).body.eval model input

/-- The exact prefix of the supplied log up to the checked θ entry,
with the real preheader complete and the body freshly pending. -/
structure Entered (start : RootMark p) (roots : List (RootMark p)) where
  pre : PreMark p
  earlier : List (RootMark p)
  remaining : List (RootMark p)
  split : roots =
    earlier ++ atBody p pre (entryBank (src := src) (entry := entry) input) (pending semantics (thetaBody p)) :: remaining
  legal : List.IsChain (RootFire p input)
    (start :: (earlier ++ [atBody p pre (entryBank (src := src) (entry := entry) input) (pending semantics (thetaBody p))]))
  complete : finished semantics (preheader p) input PUnit.unit pre = some (entryBank (src := src) (entry := entry) input)

def enter? (start : RootMark p) : (roots : List (RootMark p)) → Option (Entered p input start roots)
  | [] => none
  | after :: rest => do
    let checked ← checkFire semantics colourEq (emitted p) input PUnit.unit start after
    match ((entryCut p).rest semantics after).1 with
    | .done _ => none
    | .pending =>
      let entered ← enter? after rest
      some ⟨entered.pre, after :: entered.earlier, entered.remaining,
        congrArg (List.cons after) entered.split, List.isChain_cons_cons.mpr ⟨checked.down, entered.legal⟩,
        entered.complete⟩
    | .waiting _ _ =>
      let pre := (entryCut p).observe semantics after
      letI := markingDecEq semantics colourEq (emitted p)
      letI := tupleDecEq colourEq (dataPorts regs)
      if complete : finished semantics (preheader p) input PUnit.unit pre =
          some (entryBank (src := src) (entry := entry) input) then
        if fresh : after =
            atBody p pre (entryBank (src := src) (entry := entry) input) (pending semantics (thetaBody p)) then
          some ⟨pre, [], rest, congrArg (fun mark => mark :: rest) fresh,
            List.isChain_cons_cons.mpr ⟨fresh ▸ checked.down, .singleton _⟩, complete⟩
        else none
      else none

abbrev Packet (regs : List (ValueSort Width)) := Tuple semantics.Val (RVSDG.Theta.BodyResults (dataPorts regs))

def feedback : Packet regs → Bool
  | .cons tag _ => tag.down.val == 1

def nextBankOf : Packet regs → Bank (regs := regs) model
  | .cons _ bank => bank

/-- An activation slice consumes exactly one root restart or commit.
Its body markings are an ordered prefix of the actual input log. -/
structure Slice (pre : PreMark p) (old : Bank (regs := regs) model)
    (start : BodyMark p) (roots : List (RootMark p)) where
  body : List (BodyMark p)
  after : RootMark p
  remaining : List (RootMark p)
  packet : Packet regs
  split : roots = body.map (atBody p pre old) ++ after :: remaining
  legal : List.IsChain (BodyFire p old) (start :: body)
  complete : finished semantics (thetaBody p) old PUnit.unit (body.getLastD start) = some packet
  consumes : RootFire p input (atBody p pre old (body.getLastD start)) after
  destination : after = afterLatch p pre (feedback packet) (nextBankOf packet)

def slice? (pre : PreMark p) (old : Bank (regs := regs) model) (start : BodyMark p) :
    (roots : List (RootMark p)) → Option (Slice p input pre old start roots)
  | [] => none
  | after :: rest =>
    letI := markingDecEq semantics colourEq (emitted p)
    match done : finished semantics (thetaBody p) old PUnit.unit start with
    | some packet => do
      let take ← checkFire semantics colourEq (emitted p) input PUnit.unit (atBody p pre old start) after
      if agrees : after = afterLatch p pre (feedback packet) (nextBankOf packet) then
        some ⟨[], after, rest, packet, rfl, .singleton _, done, take.down, agrees⟩
      else none
    | none =>
      match ((entryCut p).rest semantics after).1 with
      | .pending | .done _ => none
      | .waiting _ (_, child) => do
        if saved : after = atBody p pre old child then
          let step ← checkFire semantics colourEq (thetaBody p) old PUnit.unit start child
          let slice ← slice? pre old child rest
          let last := List.getLastD_cons (a := start) (b := child) (l := slice.body)
          some ⟨child :: slice.body, slice.after, slice.remaining, slice.packet,
            (congrArg (List.cons after) slice.split).trans (congrArg (fun mark => mark :: _) saved),
            List.isChain_cons_cons.mpr ⟨step.down, slice.legal⟩,
            (congrArg (finished semantics (thetaBody p) old PUnit.unit) last).trans slice.complete,
            last.symm ▸ slice.consumes, slice.destination⟩
        else none

def Slice.firstOuter {pre : PreMark p} {old : Bank (regs := regs) model}
    {roots : List (RootMark p)} (slice : Slice p input pre old (pending semantics (thetaBody p)) roots) :
    Option (Bank (regs := regs) model) :=
  (pending semantics (thetaBody p) :: slice.body).findSome? (readOuter p old)

abbrev Output (out : ValueSort Width) := Tuple semantics.Val [.value out]

inductive Recovered (pre : PreMark p) : Bank (regs := regs) model → List (RootMark p) → Type where
  | stop {old : Bank (regs := regs) model} {roots : List (RootMark p)}
      (slice : Slice p input pre old (pending semantics (thetaBody p)) roots)
      (outer : Bank (regs := regs) model) (read : slice.firstOuter = some outer)
      (exit : feedback slice.packet = false) (empty : slice.remaining = [])
      (result : Output out) (returned : finished semantics (emitted p) input PUnit.unit slice.after = some result) :
      Recovered pre old roots
  | again {old : Bank (regs := regs) model} {roots : List (RootMark p)}
      (slice : Slice p input pre old (pending semantics (thetaBody p)) roots)
      (outer : Bank (regs := regs) model) (read : slice.firstOuter = some outer)
      (restarts : feedback slice.packet = true) (tail : Recovered pre (nextBankOf slice.packet) slice.remaining) :
      Recovered pre old roots

def recover? (pre : PreMark p) : Nat → (old : Bank (regs := regs) model) →
    (roots : List (RootMark p)) → Option (Recovered p input pre old roots)
  | 0, _, _ => none
  | budget + 1, old, roots => do
    let s ← slice? p input pre old (pending semantics (thetaBody p)) roots
    match read : s.firstOuter with
    | none => none
    | some outer =>
      if restarts : feedback s.packet = true then
        (recover? pre budget (nextBankOf s.packet) s.remaining).map (.again s outer read restarts)
      else if done : s.remaining = [] then
        match returned : finished semantics (emitted p) input PUnit.unit s.after with
        | some result => some (.stop s outer read (Bool.eq_false_iff.mpr restarts) done result returned)
        | none => none
      else none

structure Complete (roots : List (RootMark p)) where
  started : Entered p input (pending semantics (emitted p)) roots
  recovery : Recovered p input started.pre (entryBank (src := src) (entry := entry) input) started.remaining

/-- Check a complete log whose preheader is fully marked at θ entry.
Log length bounds the number of recovered activations. -/
def scan (roots : List (RootMark p)) : Option (Complete p input roots) := do
  let started ← enter? p input (pending semantics (emitted p)) roots
  let recovery ← recover? p input started.pre roots.length (entryBank (src := src) (entry := entry) input) started.remaining
  return ⟨started, recovery⟩

/-- Full banks read from one recorded activation. The occurrence retains
the source predecessor block and successor slot. -/
structure Observation (regs : List (ValueSort Width)) (size : Nat) where
  old : Bank (regs := regs) model
  occurrence : Fin size × Fin 2
  outer : Bank (regs := regs) model
  restarts : Bool
  next : Bank (regs := regs) model

def Observation.Agrees (inner : Shared.MLIR.CF.InnerPhi.Rows p.toRoutes) (outer : MLIR.CF.Phi.Rows p)
    (seen : Observation regs size) : Prop :=
  (seen.occurrence, SeaOfNodes.MLIR.Lowering.encodeValues seen.outer) = (cfPacketsAt p inner outer input seen.old).2 ∧
    seen.next = nextBank p model seen.old ∧
    seen.restarts = (seen.next.get p.again).down ∧
    MLIR.CF.latchSuccessor p input seen.old =
      .inl (if seen.restarts then Diamond.MLIR.CF.siteFrame p.header seen.next
        else Diamond.MLIR.CF.exitFrame (seen.next.get p.result))

def Slice.observation {pre : PreMark p} {old : Bank (regs := regs) model}
    {roots : List (RootMark p)} (slice : Slice p input pre old (pending semantics (thetaBody p)) roots)
    (outer : Bank (regs := regs) model) : Observation regs size :=
  ⟨old, p.outerEdgeOccurrence (MLIR.CF.Phi.arrivalSide (p := p) old), outer,
    feedback slice.packet, nextBankOf slice.packet⟩

def Recovered.observations {pre : PreMark p} :
    {old : Bank (regs := regs) model} → {roots : List (RootMark p)} →
    Recovered p input pre old roots → List (Observation regs size)
  | _, _, .stop slice outer _ _ _ _ _ => [slice.observation p input outer]
  | _, _, .again slice outer _ _ tail => slice.observation p input outer :: observations tail

def Recovered.result {pre : PreMark p} :
    {old : Bank (regs := regs) model} → {roots : List (RootMark p)} →
    Recovered p input pre old roots → Output out
  | _, _, .stop _ _ _ _ _ result _ => result
  | _, _, .again _ _ _ _ tail => result tail

def Complete.observations {roots : List (RootMark p)} (checked : Complete p input roots) :
    List (Observation regs size) :=
  checked.recovery.observations p input

def Complete.result {roots : List (RootMark p)} (checked : Complete p input roots) : Output out :=
  checked.recovery.result p input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log
