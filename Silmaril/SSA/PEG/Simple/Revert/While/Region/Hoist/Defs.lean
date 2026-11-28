module

public import Silmaril.SSA.PEG.Figure19.Placement.MustEval.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Automatic.Defs

/-! # Guarded loop-invariant placement

The supported loop has primitive guard and update slices. One update
primitive reads only parameter rows already available in the old
store. The entry guard runs in the original scope. Its true arm
computes the invariant once and carries the resulting slot around the
loop. The false arm returns the initial store directly.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist

open RVSDG (Port Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {carried vars larger ins outs : List (Ty Data)} {result t : Ty Data} {n : Nat}
variable {g : Graph P carried [result] n 1}

abbrev Embedding (vars larger : List (Ty Data)) :=
  ∀ {s}, Port vars s → Port larger s

def Reads.rebasedArgs {scope : Tuple (Ref g.sort) vars} (embed : Embedding vars larger) :
    {ins : List (Ty Data)} → {refs : Tuple (Ref g.sort) ins} →
    Region.Reads scope refs → Args P larger ins
  | _, _, .nil => .nil
  | _, _, .cons p _ tail => .cons (.var (embed p)) (rebasedArgs embed tail)

/-- Lower a primitive schedule into a larger context and retain one
unchanged local slot in front of its ordinary result tuple. -/
def retain :
    {outs : List (Ty Data)} → {roots : Tuple (Ref g.sort) outs} →
    {vars : List (Ty Data)} → {scope : Tuple (Ref g.sort) vars} →
    Schedule g false roots scope → {larger : List (Ty Data)} →
    Embedding vars larger → Port larger t → Stmt P false larger (t :: outs)
  | _, _, _, _, .done reads, _, embed, cache =>
    .project (.cons cache (reads.slots.map fun _ p => embed p))
  | _, _, _, _, .bind _ op _ _ _ reads tail, _, embed, cache =>
    .seq (.assign (.op op (Reads.rebasedArgs embed reads)))
      (retain tail (fun p => match p with | .head => .head | .tail q => .tail (embed q))
        (.tail cache))
  | _, _, _, _, .branch impossible .., _, _, _ => nomatch impossible

def isParam {sort : Fin n → Ty Data} (node : Node P carried (Fin 1) sort t) : Bool :=
  match node with
  | ⟨_, .param _, _⟩ => true
  | _ => false

/-- Checked wiring for a proposed invariant binding. The MustEval witness
justifies demand at the same old state as the specified update root. -/
structure Site (d : Descriptor g) (i : Fin n) where
  inputs : List (Ty Data)
  instr : P inputs (g.sort i)
  operands : Tuple (Ref g.sort) inputs
  row : g.node i = .ofLabel (.op instr) operands
  params : ∀ p : Fin inputs.length, isParam (g.node (operands.get (portAt inputs p)).id)
  reads : Region.Reads d.theta operands
  fresh : i.val ∉ refNumbers d.theta
  updateSlot : Fin carried.length
  demanded : i ∈ (Figure19.MustEval.analyze g)[(d.next.get (portAt carried updateSlot)).id.val]

structure Accepted (g : Graph P carried [result] n 1) where
  descriptor : Descriptor g
  boundary : Boundary g descriptor true
  rank : DemandRank n 1
  ranked : rank.check g = true
  guard : Schedule g false descriptor.guardRoots descriptor.theta
  shared : Fin n
  site : Site descriptor shared
  rest : Schedule g false descriptor.next (.cons (Ref.ofId g.sort shared) descriptor.theta)

/-- Check the boundary and both slices, placing the selected required
binding first in the reference (unhoisted) update. The guard's order
may not include it. Parameters must be available in the old store. -/
def check [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P carried [result] n 1) (d : Descriptor g) (i : Fin n) : Option (Accepted g) := do
  let some boundary := checkBoundary g d true | none
  let rank := Automatic.inferDemandRank g
  let some guardOrder := scopedOrder g d.theta d.guardRoots | none
  let scope := Tuple.cons (Ref.ofId g.sort i) d.theta
  let some updateOrder := scopedOrder g scope d.next | none
  if ranked : rank.check g = true then
    if i ∈ guardOrder then none
    else if fresh : i.val ∉ refNumbers d.theta then
      match row : g.node i with
      | ⟨ins, .op op, args⟩ =>
        if params : ∀ p : Fin ins.length, isParam (g.node (args.get (portAt ins p)).id) then
          let table := Figure19.MustEval.analyze g
          let some slot := (List.finRange carried.length).find? (fun p =>
            decide (i ∈ table[(d.next.get (portAt carried p)).id.val])) | none
          if demanded : i ∈ table[(d.next.get (portAt carried slot)).id.val] then
            let some reads := Region.Reads.check d.theta args | none
            let guard ← Schedule.check g d.guardRoots guardOrder d.theta
            let rest ← Schedule.check g d.next updateOrder scope
            return ⟨d, boundary.valid, rank, ranked, guard, i,
              ⟨ins, op, args, row, params, reads, fresh, slot, demanded⟩, rest⟩
          else none
        else none
      | _ => none
    else none
  else none

def Accepted.base (a : Accepted g) : Certificate g true :=
  ⟨a.descriptor, a.boundary, a.rank, a.ranked, a.guard,
    .bind a.shared a.site.instr a.site.operands a.site.fresh a.site.row a.site.reads a.rest⟩

def Accepted.initialize (a : Accepted g) :
    Stmt P false (.bool :: carried) (g.sort a.shared :: .bool :: carried) :=
  .assign (.op a.site.instr (Reads.rebasedArgs (fun p => .tail p) a.site.reads))

/-- The leading slot carries the invariant. The next slot is the
continuation flag, and the remaining vector is the old carried store. -/
def Accepted.body (a : Accepted g) :
    Stmt P false (g.sort a.shared :: .bool :: carried) (g.sort a.shared :: .bool :: carried) :=
  .seq (.project (.cons .head ((ports carried).map fun _ p => .tail (.tail p))))
    (.seq (retain a.rest (fun p => p) .head) (retain a.guard (fun p => .tail p) .head))

def Accepted.revert (a : Accepted g) : Program P true carried result :=
  ⟨carried,
    .seq a.guard.lower.enableWhile
      (.branch (.var .head)
        (.seq a.initialize.enableWhile
          (.seq (.while rfl (.var (.tail .head)) a.body.enableWhile)
            (.project ((ports carried).map fun _ p => .tail (.tail p)))))
        (.project ((ports carried).map fun _ p => .tail p))),
    a.descriptor.returnSlot⟩

def Accepted.runCached (a : Accepted g) (m : Interpretation.{u,v,w} P) :
    Nat → Tuple m.Value (g.sort a.shared :: .bool :: carried) → Option (m.Value result)
  | fuel, .cons cache (.cons flag store) =>
    if flag.down then
      match fuel with
      | 0 => none
      | k + 1 => (a.body.runLoopFree m (.cons cache (.cons flag store))).bind (a.runCached m k)
    else some (store.get a.descriptor.returnSlot)
termination_by structural fuel _ => fuel

/-- Bounded execution uses the same initializer, cache body and
branch guard as the emitted SIMPLE program. -/
def Accepted.runFuel (a : Accepted g) (m : Interpretation.{u,v,w} P)
    (fuel : Nat) (input : Tuple m.Value carried) : Option (m.Value result) := do
  let some tagged := a.guard.lower.runLoopFree m input | none
  if (tagged.get .head).down then
    let some cached := a.initialize.runLoopFree m tagged | none
    a.runCached m fuel cached
  else some (tagged.get (.tail a.descriptor.returnSlot))

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Hoist
