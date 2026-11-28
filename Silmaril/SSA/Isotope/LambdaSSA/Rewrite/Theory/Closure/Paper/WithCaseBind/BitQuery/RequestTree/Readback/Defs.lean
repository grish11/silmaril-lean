module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Default.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Decision.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Reflection.Defs

/-! # Read back a typed outward Bit region as a selected request tree -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback

open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload.Finite (Expr)

abbrev Live (n : Nat) := List.replicate n Bit

def slots (n : Nat) : Slots (Live n) n where
  index := Fin.val
  typed i := by simp [At, Live, i.isLt]
  distinct := Fin.val_injective

/-- Decode the physical binder after CFG entry has substituted its incoming
argument. The live scope is the newest-first list of typed Bit replies. -/
def readQuery (written : Bool) (n : Nat) : Tm signature.Instr → Option (Expr n)
  | .var j => if h : written = true ∧ j < n then some (.read ⟨j, h.2⟩) else none
  | a => (literalQuery a).map Expr.literal

/-- Each request uses a literal or a single live binder. The fixed-order
truth-table key is injective on these operands. -/
inductive Direct : {n : Nat} → Tree n → Prop
  | ret {n : Nat} (right : Bool) (i : Fin n) : Direct (.ret right i)
  | literal {n : Nat} (label b : Bool) {l r : Tree (n + 1)} :
      Direct l → Direct r → Direct (.ask label (.literal b) l r)
  | var {n : Nat} (label : Bool) (i : Fin n) {l r : Tree (n + 1)} :
      Direct l → Direct r → Direct (.ask label (.read i) l r)

def forwarding : Region signature.Instr → Option (Nat × Nat)
  | .br i (.var j) => some (i, j)
  | _ => none

/-- At multi-block arities, enter a written local branch with a variable
argument. A one-block table additionally admits literal entry substitution. -/
def enter? (k : Nat) (entry : Region signature.Instr) (rows : Fin k → Region signature.Instr) :
    Option (Region signature.Instr) :=
  match forwarding entry with
  | some (i, j) =>
    if hi : i < k then
      some (.cfg ((rows ⟨i, hi⟩).substVars (Tm.singleSubst (.var j))) k rows)
    else none
  | none =>
    if hk : k = 1 then some (entry.lsubst (cfgEntryContinuations (hk ▸ rows))) else none

inductive QueryMode where
  | literals
  | forwarded
  | decisions

def QueryMode.allowVariables : QueryMode → Bool
  | .forwarded => true
  | _ => false

/-- Follow tagged requests, typed variable returns and variable lets.
A table can leave directly at either outward exit, follow a local branch,
or use one-block entry substitution. Fuel bounds local unfolding. -/
def readMode (mode : QueryMode) : Nat → (n : Nat) → Nat → Region signature.Instr → Option (Tree n)
  | 0, _, _, _ => none
  | _fuel + 1, n, offset, .br i (.var j) => do
    let slot ← if h : j < n then some (⟨j, h⟩ : Fin n) else none
    if i = offset then some (.ret false slot)
    else if i = offset + 1 then some (.ret true slot)
    else none
  | fuel + 1, n, offset, .case (.op (.ask label) arg) left right => do
    let query ← readQuery mode.allowVariables n arg
    let l ← readMode mode fuel (n + 1) offset left
    let r ← readMode mode fuel (n + 1) offset right
    some (.ask label query l r)
  | fuel + 1, n, offset, .let₁ (.var j) body =>
    readMode mode fuel n offset (body.substVars (Tm.singleSubst (.var j)))
  | fuel + 1, n, offset, .cfg entry k rows =>
    (readMode mode fuel n (k + offset) entry).orElse fun _ =>
      (enter? k entry rows).bind (readMode mode fuel n offset)
  | fuel + 1, n, offset, raw@(.case (.var _) _ _) => do
    let .decisions := mode | none
    let d ← readDecision n raw
    let l ← readMode mode fuel (n + 1) offset d.left
    let r ← readMode mode fuel (n + 1) offset d.right
    some (.ask d.label d.query l r)
  | _, _, _, _ => none

def readWith (written : Bool) := readMode (if written then .forwarded else .literals)

abbrev read := readMode .literals

/-- The original outward region with its exact typing, before literal exit packing. -/
abbrev Candidate := {r : Region signature.Instr // ValueBranches [Bit] r Exits}

def Candidate.packed (p : Candidate) :=
  Paper.TypeCategory.ofRegion p.property.packExits

noncomputable def Candidate.observations (p : Candidate) (guard : Bool) : Set Observation :=
  ((denote.map ((Paper.Extension.Singleton.projection Seed).map p.packed)).of (bit guard)).outcomes

def Candidate.read (p : Candidate) (fuel : Nat) : Option (Tree 1) :=
  Readback.read fuel 1 0 p.val

/-- Read a forwarded variable directly; its selected syntax keeps the same
argument, including the payload hidden by the Boolean trace observation. -/
def Candidate.readWithVariables (p : Candidate) (fuel : Nat) : Option (Tree 1) :=
  readWith true fuel 1 0 p.val

/-- Read a staged pure query decision before the effectful request. -/
def Candidate.readWithDecisions (p : Candidate) (fuel : Nat) : Option (Tree 1) :=
  readMode .decisions fuel 1 0 p.val

/-- A table or constructor outside the recognized scope, or insufficient fuel,
is reported as unknown. A difference uses a reachable all-replies history. -/
inductive Verdict where
  | unknown
  | equal
  | different (witness : Difference)
deriving DecidableEq

def compareTrees : Option (Tree 1) → Option (Tree 1) → Verdict
  | some t, some u =>
    match t.separate? u with
    | none => .equal
    | some w => .different w
  | _, _ => .unknown

def compare (fuel : Nat) (p q : Candidate) : Verdict :=
  compareTrees (p.read fuel) (q.read fuel)

def compareWithVariables (fuel : Nat) (p q : Candidate) : Verdict :=
  compareTrees (p.readWithVariables fuel) (q.readWithVariables fuel)

def compareWithDecisions (fuel : Nat) (p q : Candidate) : Verdict :=
  compareTrees (p.readWithDecisions fuel) (q.readWithDecisions fuel)

namespace Example

/-- Both reply tags transfer their actual payload to the same written block. -/
def joined (right : Bool) (offset : Nat) : Region signature.Instr :=
  .cfg (.case (.op (.ask false) (literal false)) (.br 0 (.var 0)) (.br 0 (.var 0))) 1
    (fun _ => .br (1 + (offset + if right then 1 else 0)) (.var 0))

/-- The first layout enters zero and forwards to one. -/
def forward (right : Bool) : Region signature.Instr :=
  .cfg (.br 0 (.var 0)) 2 (Fin.cases (.br 1 (.var 0)) (fun _ => joined right 2))

/-- This layout enters one and forwards to zero. -/
def backward (right : Bool) : Region signature.Instr :=
  .cfg (.br 1 (.var 0)) 2 (Fin.cases (joined right 2) (fun _ => .br 0 (.var 0)))

/-- This well-typed request has a live variable query outside this readback. -/
def variableQuery : Region signature.Instr := call false (.var 0)

def expected (right : Bool) : Tree 1 :=
  .ask false (.literal false) (.ret right 0) (.ret right 0)

def witness : Difference := ⟨false, false, ⟨[event false false (false, false)], false, false⟩⟩

end Example

namespace VariableExample

/-- Both tags share one written join. Only the second tag may pass the
original guard instead of the latest reply. The join's alias shifts its
incoming bit one binder before the second request reads it. -/
def shared (altered : Bool) (offset : Nat) : Region signature.Instr :=
  .cfg (.case (.op (.ask false) (literal false)) (.br 0 (.var 0))
      (.br 0 (.var (if altered then 1 else 0)))) 1
    (fun _ => .let₁ (.var 0) (.case (.op (.ask true) (.var 1))
      (.br (1 + (offset + 1)) (.var 0)) (.br (1 + (offset + 1)) (.var 0))))

def numbered (renumbered altered : Bool) : Region signature.Instr :=
  if renumbered then
    .cfg (.br 1 (.var 0)) 2 (Fin.cases (shared altered 2) (fun _ => .br 0 (.var 0)))
  else
    .cfg (.br 0 (.var 0)) 2 (Fin.cases (.br 1 (.var 0)) (fun _ => shared altered 2))

/-- This query itself makes a request. The recognizer leaves this syntax
unknown instead of duplicating, moving or interpreting its effects. -/
def effectfulQuery : Region signature.Instr :=
  call true (.case (.op (.ask false) (literal false)) (.var 0) (.var 0))

def next (slot : Fin 2) : Tree 2 :=
  .ask true (.read slot) (.ret true 0) (.ret true 0)

def querySlot (altered tag : Bool) : Fin 2 := if altered && tag then 1 else 0

def expected (altered : Bool) : Tree 1 :=
  .ask false (.literal false) (next (querySlot altered false)) (next (querySlot altered true))

def witness : Difference :=
  ⟨false, false, ⟨[event false false (true, true), event true true (false, false)], true, false⟩⟩

end VariableExample

namespace DecisionExample

inductive Shape where
  | plain
  | redundant
  | changed

def request (query : Bool) (offset : Nat) : Region signature.Instr :=
  requestRegion true query (.br (offset + 1) (.var 0)) (.br (offset + 1) (.var 0))

/-- The most recent reply is the first test. A second test uses the caller
Bit after weakening through the most recent test's unit payload. -/
def staged (shape : Shape) (offset : Nat) : Region signature.Instr :=
  let low := request false offset
  let high := request true offset
  .case (.var 0) low
    (match shape with
     | .plain => high
     | .redundant => .case (.var 2) high high
     | .changed => .case (.var 2) low high)

def entry (shape : Shape) : Region signature.Instr :=
  requestRegion false false (request false 2) (staged shape 2)

def numbered (renumbered : Bool) (shape : Shape) : Region signature.Instr :=
  if renumbered then
    .cfg (.br 1 (.var 0)) 2 (Fin.cases (entry shape) (fun _ => .br 0 (.var 0)))
  else
    .cfg (.br 0 (.var 0)) 2 (Fin.cases (.br 1 (.var 0)) (fun _ => entry shape))

def rightQuery (shape : Shape) : Expr 2 :=
  .split (.literal false)
    (match shape with
     | .plain => .literal true
     | .redundant => .split (.literal true) (.literal true)
     | .changed => .split (.literal false) (.literal true))

def selectedQuery (shape : Shape) (tag : Bool) : Expr 2 :=
  if tag then rightQuery shape else .literal false

def expected (shape : Shape) : Tree 1 :=
  .ask false (.literal false)
    (.ask true (selectedQuery shape false) (.ret true 0) (.ret true 0))
    (.ask true (selectedQuery shape true) (.ret true 0) (.ret true 0))

def witness : Difference :=
  ⟨false, false, ⟨[event false false (true, true), event true true (false, false)], true, false⟩⟩

/-- The term-level spelling puts the pure test inside the opcode operand. -/
def termCase : Region signature.Instr :=
  call false (caseOperand (.var 0))

def quotedTermCase : Tree 1 :=
  .ask false (.read 0) (.ret false 0) (.ret true 0)

end DecisionExample

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree.Readback
