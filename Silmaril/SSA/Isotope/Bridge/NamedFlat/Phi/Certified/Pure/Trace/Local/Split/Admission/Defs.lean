module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Trace.Local.Split.Defs
public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Pure.Thms

/-! # Generating the checked admission of a split φ graph -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split

open Silmaril.SSA.LambdaRTL
open Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Phi.Split (Plan Checked)

universe u v
variable {V W K J Base : Type u} {F : Type v} {n : Nat}
variable (plan : Plan V W K J)

/-- Extend the renamed capture list at the older end so that all original
positions and types are preserved. New slots are read from the renamed store. -/
def extendedNames (names : Fin n → Option V) (extra : List (Option W × Ty Base)) :
    Fin (n + extra.length) → Option W :=
  Fin.addCases (fun i => (names i).map plan.register) (fun i => extra[i].1)

def extendedTypes (β : BoundCtx (Ty Base) n) (extra : List (Option W × Ty Base)) :
    BoundCtx (Ty Base) (n + extra.length) :=
  .ofFin (Fin.addCases β.get fun i => extra[i].2)

variable [DecidableEq V] [DecidableEq K] [DecidableEq W] [DecidableEq J]
  [HasTy F (Ty Base)]

/-- Carry over the old arrival claims. A forwarding block whose destination
has a claim needs that claim and exactly the old φ reads on the selected edge.
Omit the forwarding claim when the destination was outside the certificate. -/
def splitCertificate (source : Phi.Graph V K F) (certificate : Phi.GlobalSSA.Certificate V K) :
    Phi.GlobalSSA.Certificate W J :=
  let renamed := certificate.map fun (key, names) => (plan.label key, names.map plan.register)
  match certificate.lookup plan.header with
  | none => renamed
  | some required =>
    (plan.forward,
      (required ++ Phi.GlobalSSA.edgeReads source plan.predecessor plan.header).map plan.register) :: renamed

/-- The generated profile and the actual checked, purely closed split graph.
The new slots and block types are outputs of synthesis. -/
structure Generated (source : Phi.Graph V K F) (inputs : List V)
    (names : Fin n → Option V) (β : BoundCtx (Ty Base) n) (exits : Fin 1 → Ty Base) where
  extra : List (Option W × Ty Base)
  blocks : Fin (blockCount (plan.rewrite source)) → Ty Base
  checked : Checked plan source (plan.rewrite source)
  admitted : Certified.Admission (plan.rewrite source) (inputs.map plan.register)
    (extendedNames plan names extra) (extendedTypes β extra) blocks exits
  closed : Closed admitted

/-- Associate the cells of a right-nested packet type with its names. -/
def packetTypes {A : Type u} : List A → Ty Base → Option (List (A × Ty Base))
  | [], _ => some []
  | name :: names, .product ty tail => (packetTypes names tail).map ((name, ty) :: ·)
  | _, _ => none

/-- Recover the types read by a φ operand from its checked packet-cell type. -/
def operandTypes : Val V → Ty Base → Option (List (V × Ty Base))
  | .var name, ty => some [(name, ty)]
  | .unit, .unit => some []
  | .pair left right, .product a b => do
    let leftTypes ← operandTypes left a
    let rightTypes ← operandTypes right b
    return leftTypes ++ rightTypes
  | _, _ => none

def packetProfile (support : List V) (newSupport : List W)
    (added : List (V × Ty Base)) (old : Ty Base) : Option (Ty Base) := do
  let .product payload tuple := old | none
  let registerTypes ← packetTypes support tuple
  let newTypes ← newSupport.mapM fun name => (registerTypes ++ added).lookup (plan.register.symm name)
  return .product payload (newTypes.foldr .product .unit)

/-- Types reconstructed before running the checker. The retained slots
recorded here are newly free register reads whose type comes from the moved φ column. -/
structure ProfileCandidate (source : Phi.Graph V K F) (n : Nat) (Base : Type u) where
  extra : List (Option W × Ty Base)
  blocks : Fin (blockCount (plan.rewrite source)) → Ty Base
  movedSlots : List (Fin n × Ty Base)

/-- Build the candidate profiles in the actual versioner's register and block
orders. Keep each old block's φ payload type. The forwarding block has a
unit payload and uses the old destination's register types, extended with
types recovered from the selected φ column. -/
def profileCandidate (source : Phi.Graph V K F)
    (names : Fin n → Option V) (blocks : Fin (blockCount source) → Ty Base) :
    Option (ProfileCandidate plan source n Base) := do
  let lowered := Phi.lower source
  let target := Phi.lower (plan.rewrite source)
  let lexical := Versioning.compile lowered
  let splitLexical := Versioning.compile target
  let oldSupport := (Versioning.registers lowered).filterMap id
  let newSupport := (Versioning.registers target).filterMap id
  let oldBlocks := (List.finRange lexical.blocks.length).map fun i => (lexical.blocks[i].1, blocks i)
  let .product headerPayload headerTuple ← oldBlocks.lookup (some plan.header) | none
  let rows ← (source.blocks.lookup plan.header).map Phi.Block.rows
  let cells ← packetTypes (Phi.arguments plan.predecessor rows) headerPayload
  let movedTypes ← cells.mapM fun (operand, ty) => operandTypes operand ty
  let added := movedTypes.flatten
  let oldRegisterTypes ← packetTypes oldSupport headerTuple
  let allTypes := oldRegisterTypes ++ added
  let oldNames := fun i => (names i).map plan.register
  let free := (splitLexical.entry.toRegion.fvList.filterMap fun (name, version) =>
    if version = 0 then some name else none).dedup
  let extra ← (free.filter fun name => (NamedFlat.first oldNames name).isNone).mapM fun name => do
    let ty ← name.elim (some .unit) (fun reg => allTypes.lookup (plan.register.symm reg))
    return (name, ty)
  let movedSlots := free.filterMap fun name =>
    match name with
    | none => none
    | some key =>
      let reg := plan.register.symm key
      if reg ∈ oldSupport then none else
        (NamedFlat.first oldNames name).bind fun slot => (added.lookup reg).map (slot, ·)
  let renamedBlocks := oldBlocks.map fun (label, ty) => (label.map plan.label, ty)
  let profiles ← NamedFlat.tabulate splitLexical.blocks.length fun i => do
    let label := splitLexical.blocks[i].1
    let old ← if label = some plan.forward then some (.product .unit headerTuple)
      else renamedBlocks.lookup label
    packetProfile plan oldSupport newSupport added old
  return ⟨extra, profiles, movedSlots⟩

def splitProfiles (source : Phi.Graph V K F)
    (names : Fin n → Option V) (blocks : Fin (blockCount source) → Ty Base) :
    Option (List (Option W × Ty Base) × (Fin (blockCount (plan.rewrite source)) → Ty Base)) :=
  (profileCandidate plan source names blocks).map fun candidate => (candidate.extra, candidate.blocks)

/-- Failure stages of the checked split path. Slot numbers are newest-first,
as in `BoundCtx.get`. A retained slot is reported only when the actual type
checker accepts the same graph after just the reported slot types are changed. -/
inductive Failure where
  | missingEdge
  | targetNormalization
  | arrivalClaims
  | packetProfile
  | lexicalScope
  | oldCaptureTypes (slots : List Nat)
  | typing
  | pureClosure
  deriving DecidableEq, Repr

/-- Candidate type changes for a diagnostic recheck of retained slots. -/
def oldCaptureRepairs [DecidableEq Base] (β : BoundCtx (Ty Base) n)
    (moved : List (Fin n × Ty Base)) : List (Fin n × Ty Base) :=
  moved.filter fun (slot, ty) => decide (β.get slot ≠ ty)

def revisedOldTypes (β : BoundCtx (Ty Base) n) (repairs : List (Fin n × Ty Base)) :
    BoundCtx (Ty Base) n :=
  .ofFin fun i => (repairs.lookup i).getD (β.get i)

/-- Explain a rejected typed admission after the arrival check has passed.
The second type check diagnoses old types. The suggested types are never
used to admit the graph or change the caller's original slots. -/
def explainTyping [DecidableEq Base] {source : Phi.Graph V K F} (names : Fin n → Option V)
    (β : BoundCtx (Ty Base) n) (exits : Fin 1 → Ty Base) (candidate : ProfileCandidate plan source n Base) :
    Failure :=
  match NamedFlat.compile (Phi.lower (plan.rewrite source)) [none] (extendedNames plan names candidate.extra) with
  | none => .lexicalScope
  | some graph =>
    let repairs := oldCaptureRepairs β candidate.movedSlots
    let revised := revisedOldTypes β repairs
    if !repairs.isEmpty && NamedFlat.check graph (extendedTypes revised candidate.extra) candidate.blocks exits
    then .oldCaptureTypes (repairs.map fun (slot, _) => slot.val)
    else .typing

/-- On already accepted arrival claims, run the actual named elaborator and
exact type checker on the reconstructed interface. -/
def admitProfile [DecidableEq Base] {source : Phi.Graph V K F} {inputs : List V}
    (names : Fin n → Option V) (β : BoundCtx (Ty Base) n) (exits : Fin 1 → Ty Base)
    (candidate : ProfileCandidate plan source n Base) (certificate : Phi.GlobalSSA.Certificate V K)
    (arrived : Phi.GlobalSSA.check (plan.rewrite source) (inputs.map plan.register)
      (splitCertificate plan source certificate) = true) :
    Option (Certified.Admission (plan.rewrite source) (inputs.map plan.register)
      (extendedNames plan names candidate.extra) (extendedTypes β candidate.extra) candidate.blocks exits) :=
  (NamedFlat.compileTyped (Phi.lower (plan.rewrite source)) [none]
    (extendedNames plan names candidate.extra) (extendedTypes β candidate.extra) candidate.blocks exits).map
    fun checked => ⟨Phi.GlobalSSA.check_sound arrived, checked.val, checked.property.1, checked.property.2⟩

/-- Generate a split admission with a stage-specific error. The source
admission already certifies normalization. The target checks use the
reconstructed claims and the exact generated interfaces. -/
def generateDetailed [DecidableEq Base] {source : Phi.Graph V K F} {inputs : List V}
    {names : Fin n → Option V} {β : BoundCtx (Ty Base) n}
    {blocks : Fin (blockCount source) → Ty Base} {exits : Fin 1 → Ty Base}
    (original : Certified.Admission source inputs names β blocks exits)
    (certificate : Phi.GlobalSSA.Certificate V K) :
    Except Failure (Generated plan source inputs names β exits) :=
  let target := plan.rewrite source
  let renamedInputs := inputs.map plan.register
  let claims := splitCertificate plan source certificate
  if edge : plan.hasEdge source = true then
    if normalized : target.check = true then
      if arrived : Phi.GlobalSSA.check target renamedInputs claims = true then
        match profileCandidate plan source names blocks with
        | none => .error .packetProfile
        | some candidate =>
          match admitProfile plan names β exits candidate certificate arrived with
          | none => .error (explainTyping plan names β exits candidate)
          | some admitted =>
            match PureCapture.close admitted with
            | none => .error .pureClosure
            | some closed =>
              .ok ⟨candidate.extra, candidate.blocks,
                ⟨original.wellFormed.normalized, edge, normalized, rfl⟩, admitted, closed⟩
      else .error .arrivalClaims
    else .error .targetNormalization
  else .error .missingEdge

/-- The original optional API forgets the failure stage. -/
def generate [DecidableEq Base] {source : Phi.Graph V K F} {inputs : List V}
    {names : Fin n → Option V} {β : BoundCtx (Ty Base) n}
    {blocks : Fin (blockCount source) → Ty Base} {exits : Fin 1 → Ty Base}
    (original : Certified.Admission source inputs names β blocks exits)
    (certificate : Phi.GlobalSSA.Certificate V K) : Option (Generated plan source inputs names β exits) :=
  (generateDetailed plan original certificate).toOption

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.PureCapture.Local.Split
