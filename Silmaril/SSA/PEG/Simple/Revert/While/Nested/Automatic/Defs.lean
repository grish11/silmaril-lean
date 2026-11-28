module

public import Silmaril.SSA.PEG.Simple.Revert.While.Nested.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Defs
public import Init.Data.List.Sort
public import Silmaril.SSA.PEG.Reindex.Automatic.Defs

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
variable {outer vars outs ins : List (Ty Data)} {result t : Ty Data} {n l : Nat}

structure Slot (g : Graph P outer [result] n l) (t : Ty Data) where
  exit : Ref g.sort t
  theta : Ref g.sort t
  initial : Ref g.sort t
  next : Ref g.sort t

def evalLoop : {ins : List (Ty Data)} → {t : Ty Data} →
    Label P outer (Fin l) ins t → Option (Fin l)
  | _, _, .eval loop => some loop
  | _, _, _ => none

/-- All carried slots have an eval row using the same pass. -/
def readSlotAt (g : Graph P outer [result] n l) (key : Fin l) (pass : Ref g.sort .count)
    (exit : Ref g.sort t) : Option (Slot g t) := do
  let ⟨_, .eval loop, args⟩ := Region.nodeAt g exit | none
  let theta := args.get .head
  let ⟨_, .theta owner, thetaArgs⟩ := Region.nodeAt g theta | none
  if loop = key ∧ owner = key ∧ (args.get (.tail .head)).id = pass.id then
    return ⟨exit, theta, thetaArgs.get .head, thetaArgs.get (.tail .head)⟩
  else none

def readSlot (g : Graph P outer [result] n n) (pass : Ref g.sort .count)
    (exit : Ref g.sort t) : Option (Slot g t) :=
  readSlotAt g pass.id pass exit

def readSlotsAt (g : Graph P outer [result] n l) (key : Fin l) (pass : Ref g.sort .count) :
    List (Fin n) → Option (Σ profile, Tuple (Slot g) profile)
  | [] => some ⟨[], .nil⟩
  | i :: rest => do
    let some head := readSlotAt g key pass (Ref.ofId g.sort i) | none
    let ⟨profile, tail⟩ ← readSlotsAt g key pass rest
    return ⟨g.sort i :: profile, .cons head tail⟩

def readSlots (g : Graph P outer [result] n n) (pass : Ref g.sort .count) :
    List (Fin n) → Option (Σ profile, Tuple (Slot g) profile) :=
  readSlotsAt g pass.id pass

def bundleIds (g : Graph P outer [result] n l) (key : Fin l) : List (Fin n) :=
  (List.finRange n).filter fun i => evalLoop (g.node i).label == some key

def bundleAt (g : Graph P outer [result] n l) (key : Fin l) (pass : Ref g.sort .count)
    (exits : List (Fin n)) : Option (Σ profile, Tuple (Slot g) profile) := do
  let ⟨profile, slots⟩ ← readSlotsAt g key pass exits
  if (refNumbers (slots.map fun _ slot => slot.theta)).Nodup then some ⟨profile, slots⟩ else none

def bundle (g : Graph P outer [result] n n) (pass : Ref g.sort .count) :
    Option (Σ profile, Tuple (Slot g) profile) :=
  bundleAt g pass.id pass (bundleIds g pass.id)

structure Test (g : Graph P outer [result] n l) where
  guard : Ref g.sort .bool
  negate : P [.bool] .bool

def readTestAt (g : Graph P outer [result] n l) (key : Fin l)
    (pass : Ref g.sort .count) : Option (Test g) := do
  let ⟨_, .pass loop, args⟩ := Region.nodeAt g pass | none
  let ⟨[.bool], .op negate, operands⟩ := Region.nodeAt g (args.get .head) | none
  if loop = key then some ⟨operands.get .head, negate⟩ else none

def readTest (g : Graph P outer [result] n n) (pass : Ref g.sort .count) : Option (Test g) :=
  readTestAt g pass.id pass

/-- A continuation test is a carried Boolean or a single primitive
whose operands are carried values. -/
def readGuard (g : Graph P outer [result] n l) (scope : Tuple (Ref g.sort) vars)
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

/-- The exact-numbered path recovers the compiler's emission order.
For a reference program up to renaming, the scoped dependency order
already suffices. -/
def readSliceAt (g : Graph P outer [result] n l) (scope : Tuple (Ref g.sort) vars)
    (roots : Tuple (Ref g.sort) outs) (numbered : Bool) : Option (Stmt P false vars outs) := do
  let some ids := Region.scopedOrder g scope roots | none
  let order := if numbered then ids.mergeSort (fun a b => b.val ≤ a.val) else ids
  (Region.Schedule.check g roots order scope).map Region.Schedule.lower

def readSlice (g : Graph P outer [result] n l) (scope : Tuple (Ref g.sort) vars)
    (roots : Tuple (Ref g.sort) outs) : Option (Stmt P false vars outs) :=
  readSliceAt g scope roots true

def cacheRows (g : Graph P outer [result] n l) : Graph P outer [result] n l :=
  Silmaril.SSA.PEG.Reindex.Automatic.cacheRows g

structure Headers (g : Graph P outer [result] n l) where
  outerKey : Fin l
  outerPass : Ref g.sort .count
  childKey : Fin l
  childPass : Ref g.sort .count

def soleChild (forest : LoopForest l) (outerKey : Fin l) : Option (Fin l) := do
  if (forest.parent outerKey).isSome then none else
    let [child] := (List.finRange l).filter (fun i => forest.parent i == some outerKey) | none
    return child

/-- Read the designated outer eval and find its sole direct child. The
graph's pass label identifies a loop independently of the pass address. -/
def locate [DecidableEq Data] (g : Graph P outer [result] n l) : Option (Headers g) := do
  let ⟨_, .eval outerKey, refs⟩ := Region.nodeAt g (g.roots.get .head) | none
  let outerPass := refs.get (.tail .head)
  let some childKey := soleChild g.forest outerKey | none
  let [childRow] := (List.finRange n).filter
    (fun i => Structured.passLoop (g.node i).label == some childKey) | none
  let some childPass := Ref.check g.sort .count childRow.val | none
  return ⟨outerKey, outerPass, childKey, childPass⟩

/-- Recover outer bundle order from distinct ordered input parameters. -/
def parameterOrder (g : Graph P outer [result] n l) (header : Headers g)
    (exits : List (Fin n)) : Option (List (Fin n)) := do
  let keyed ← exits.mapM fun i => do
    let some slot := readSlotAt g header.outerKey header.outerPass (Ref.ofId g.sort i) | none
    let ⟨_, .param port, _⟩ := Region.nodeAt g slot.initial | none
    return ((numberPort port).id.val, i)
  let sorted := keyed.mergeSort (fun a b => a.1 ≤ b.1)
  if sorted.map Prod.fst = List.range outer.length then some (sorted.map Prod.snd) else none

structure Description (P : InstructionSet.{u,v} Data) (outer : List (Ty Data))
    (result : Ty Data) (n : Nat) where
  inner : List (Ty Data)
  form : Form P outer inner result
  outerExits : List (Fin n)
  childExits : List (Fin n)

/-- Recover the form and the ordered exit bundles. The graph-local path
orders outer slots by parameter, child slots by input eval address, and
primitive bindings by dependency. -/
def describe [DecidableEq Data] (input : Graph P outer [result] n l)
    (numbered : Bool) : Option (Description P outer result n) := do
  let g := cacheRows input
  let some header := locate g | none
  if numbered && (header.outerKey.val != header.outerPass.id.val ||
      header.childKey.val != header.childPass.id.val) then none else
    let some outerTest := readTestAt g header.outerKey header.outerPass | none
    let some childTest := readTestAt g header.childKey header.childPass | none
    let outerIds := bundleIds g header.outerKey
    let childIds := bundleIds g header.childKey
    let some outerExits := if numbered then some outerIds else parameterOrder g header outerIds | none
    let some ⟨outerProfile, outerSlots⟩ := bundleAt g header.outerKey header.outerPass outerExits | none
    let some ⟨innerProfile, childSlots⟩ := bundleAt g header.childKey header.childPass childIds | none
    if same : outerProfile = outer then
      let outerSlots : Tuple (Slot g) outer := same ▸ outerSlots
      let old := outerSlots.map fun _ slot => slot.theta
      let childOld := childSlots.map fun _ slot => slot.theta
      let some captures := Region.Reads.check old (childSlots.map fun _ slot => slot.initial) | none
      let some returned := Region.lookup (g.roots.get .head)
        (outerSlots.map fun _ slot => slot.exit) | none
      let outerGuard ← readGuard g old outerTest.guard
      let innerGuard ← readGuard g childOld childTest.guard
      let innerStep ← readSliceAt g childOld (childSlots.map fun _ slot => slot.next) numbered
      let commit ← readSliceAt g (childSlots.map fun _ slot => slot.exit)
        (outerSlots.map fun _ slot => slot.next) numbered
      return ⟨innerProfile,
        ⟨outerGuard, captures.slots, innerGuard, innerStep, commit, returned.val, outerTest.negate⟩,
        outerExits, childIds⟩
    else none

/-- Infer a form for the exact numbered checker. -/
def probe [DecidableEq Data] (g : Graph P outer [result] n n) :
    Option (Σ inner, Form P outer inner result) :=
  (describe g true).map fun d => ⟨d.inner, d.form⟩

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
