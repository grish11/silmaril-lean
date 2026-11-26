module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Defs
public import Init.Data.List.Sort
public import Init.Data.Vector.OfFn

/-! # Automatic two-level reversion in the structured compiler layout

Discovery follows the designated eval, finds its unique child in the
parent table, and reads both shared eval bundles. The ordered bundles
and primitive assignments use the structured compiler's row order.
The supplied-form checker validates the inferred form against the input.
-/

@[expose] public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Nested.Automatic

open RVSDG (Port Tuple)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {outer vars outs ins : List (Ty Data)} {result t : Ty Data} {n : Nat}

structure Slot (g : Graph P outer [result] n n) (t : Ty Data) where
  exit : Ref g.sort t
  theta : Ref g.sort t
  initial : Ref g.sort t
  next : Ref g.sort t

def evalLoop : {ins : List (Ty Data)} → {t : Ty Data} →
    Label P outer (Fin n) ins t → Option (Fin n)
  | _, _, .eval loop => some loop
  | _, _, _ => none

/-- All carried slots have an eval row using the same pass. -/
def readSlot (g : Graph P outer [result] n n) (pass : Ref g.sort .count)
    (exit : Ref g.sort t) : Option (Slot g t) := do
  let ⟨_, .eval loop, args⟩ := Region.nodeAt g exit | none
  let theta := args.get .head
  let ⟨_, .theta owner, thetaArgs⟩ := Region.nodeAt g theta | none
  if loop = pass.id ∧ owner = loop ∧ (args.get (.tail .head)).id = pass.id then
    return ⟨exit, theta, thetaArgs.get .head, thetaArgs.get (.tail .head)⟩
  else none

def readSlots (g : Graph P outer [result] n n) (pass : Ref g.sort .count) :
    List (Fin n) → Option (Σ profile, Tuple (Slot g) profile)
  | [] => some ⟨[], .nil⟩
  | i :: rest => do
    let some head := readSlot g pass (Ref.ofId g.sort i) | none
    let ⟨profile, tail⟩ ← readSlots g pass rest
    return ⟨g.sort i :: profile, .cons head tail⟩

def bundle (g : Graph P outer [result] n n) (pass : Ref g.sort .count) :
    Option (Σ profile, Tuple (Slot g) profile) := do
  let ⟨profile, slots⟩ ← readSlots g pass ((List.finRange n).filter fun i =>
    evalLoop (g.node i).label == some pass.id)
  if (refNumbers (slots.map fun _ slot => slot.theta)).Nodup then some ⟨profile, slots⟩ else none

structure Test (g : Graph P outer [result] n n) where
  guard : Ref g.sort .bool
  negate : P [.bool] .bool

def readTest (g : Graph P outer [result] n n) (pass : Ref g.sort .count) : Option (Test g) := do
  let ⟨_, .pass loop, args⟩ := Region.nodeAt g pass | none
  let ⟨[.bool], .op negate, operands⟩ := Region.nodeAt g (args.get .head) | none
  if loop = pass.id then some ⟨operands.get .head, negate⟩ else none

/-- A continuation test is a carried Boolean or a single primitive
whose operands are carried values. -/
def readGuard (g : Graph P outer [result] n n) (scope : Tuple (Ref g.sort) vars)
    (guard : Ref g.sort .bool) : Option (Expr P vars .bool) :=
  match Region.lookup guard scope with
  | some slot => some (.var slot.val)
  | none =>
    match Region.nodeAt g guard with
    | ⟨_, .op instr, refs⟩ =>
      match Region.Reads.check scope refs with
      | some reads => some (.op instr reads.args)
      | none => none
    | _ => none

/-- Discover the dependency slice, then use reverse row order to recover
the compiler's assignment order. The checked schedule validates every read. -/
def readSlice (g : Graph P outer [result] n n) (scope : Tuple (Ref g.sort) vars)
    (roots : Tuple (Ref g.sort) outs) : Option (Stmt P false vars outs) := do
  let some ids := Region.scopedOrder g scope roots | none
  let order := ids.mergeSort (fun a b => b.val ≤ a.val)
  (Region.Schedule.check g roots order scope).map Region.Schedule.lower

/-- Cache the finite row and parent tables for discovery, which may
read a row repeatedly while finding scopes and scheduling dependencies. -/
def cacheRows (g : Graph P outer [result] n n) : Graph P outer [result] n n :=
  let rows := Vector.ofFn fun (i : Fin n) =>
    (⟨i, g.node i⟩ : Σ j, Node P outer (Fin n) g.sort (g.sort j))
  let parents := Vector.ofFn g.forest.parent
  { g with
    forest := ⟨parents.get⟩
    node := fun i =>
      let row := rows.get i
      have address : row.1 = i := by simp [row, rows, Vector.get, Fin.cast]
      address ▸ row.2 }

/-- Infer a form from labelled rows and typed wires. Duplicate child
captures are allowed. The chosen child must be the only direct child of
the outer pass. -/
def probe [DecidableEq Data] (g : Graph P outer [result] n n) :
    Option (Σ inner, Form P outer inner result) := do
  let g := cacheRows g
  let root := g.roots.get .head
  let ⟨_, .eval _, refs⟩ := Region.nodeAt g root | none
  let outerPass := refs.get (.tail .head)
  if (g.forest.parent outerPass.id).isSome then none else
    let [child] := (List.finRange n).filter (fun i => g.forest.parent i == some outerPass.id) | none
    let some childPass := Ref.check g.sort .count child.val | none
    let some outerTest := readTest g outerPass | none
    let some childTest := readTest g childPass | none
    let some ⟨outerProfile, outerSlots⟩ := bundle g outerPass | none
    let some ⟨innerProfile, childSlots⟩ := bundle g childPass | none
    if same : outerProfile = outer then
      let outerSlots : Tuple (Slot g) outer := same ▸ outerSlots
      let old := outerSlots.map fun _ slot => slot.theta
      let childOld := childSlots.map fun _ slot => slot.theta
      let some captures := Region.Reads.check old (childSlots.map fun _ slot => slot.initial) | none
      let some returned := Region.lookup root (outerSlots.map fun _ slot => slot.exit) | none
      let outerGuard ← readGuard g old outerTest.guard
      let innerGuard ← readGuard g childOld childTest.guard
      let innerStep ← readSlice g childOld (childSlots.map fun _ slot => slot.next)
      let commit ← readSlice g (childSlots.map fun _ slot => slot.exit)
        (outerSlots.map fun _ slot => slot.next)
      return ⟨innerProfile,
        ⟨outerGuard, captures.slots, innerGuard, innerStep, commit, returned.val, outerTest.negate⟩⟩
    else none

/-- An accepted inference contains the existing checked reversion
certificate for the input table at the recovered size. -/
structure Accepted (g : Graph P outer [result] n n) where
  inner : List (Ty Data)
  form : Form P outer inner result
  size : n = form.size
  certificate : Certificate form (size ▸ g)

def extract [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]
    (g : Graph P outer [result] n n) : Option (Accepted g) := do
  let ⟨inner, form⟩ ← probe g
  if size : n = form.size then
    let some cert := Nested.check form (size ▸ g) | none
    return ⟨inner, form, size, cert⟩
  else none

variable {g : Graph P outer [result] n n}

def Accepted.revert (a : Accepted g) : Program P true outer result :=
  a.certificate.revert

end Silmaril.SSA.PEG.Simple.Revert.While.Nested.Automatic
