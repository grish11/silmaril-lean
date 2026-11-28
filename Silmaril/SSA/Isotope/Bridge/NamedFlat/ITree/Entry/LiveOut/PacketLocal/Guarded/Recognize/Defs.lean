module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Defs

/-! # Exact recognition of a constructor-bit request loop -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize

open Silmaril.Elgot.ITree (Tree)
open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA (FiniteCFG Flat Region)
open LambdaSSA.Semantics.Interaction (Primitive Transfer)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet pack)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Table Row)

abbrev Bit : Syntax.Ty := .coprod .unit .unit
abbrev Packets : List Syntax.Ty := [Bit, .unit, .unit]

/-- Every recognized request consumes a constructor bit. Reply position zero
carries a new bit, and positions one and two carry unit. -/
abbrev requestTypes (Φ : Type) : HasTy Φ Syntax.Ty :=
  ⟨fun _ => Bit, fun _ => Region.packedExitType Packets⟩

attribute [local instance] requestTypes

abbrev signature (Φ : Type) : RequestSignature Φ :=
  ⟨fun _ => Packets, fun _ => rfl⟩

/-- Every reply carries the original payload to a block with that exact packet type. -/
structure TypedRoutes (incoming : Fin 3 → Syntax.Ty) where
  destination : Fin 3 → Fin 3
  packet : ∀ i, incoming (destination i) = Packets.get i

/-- Routes for the original guarded layout, which has two unit destinations. -/
structure Routes where
  destination : Fin 3 → Fin 3
  packet : ∀ i, Packets.get (destination i) = Packets.get i

/-- Read the three occupied reply destinations from the written case spine.
The reconstructed graph is checked separately for its operands and shape. -/
def readTypedRoutes {Φ : Type} (incoming : Fin 3 → Syntax.Ty) (row : Flat Φ 5 2) :
    Option (TypedRoutes incoming) :=
  match row with
  | .let₂ _ (.case _ (.br bit _) (.case _ (.br first _) (.case _ (.br second _) _))) => do
    let block (label : Fin 5) : Option (Fin 3) :=
      if bound : label.val < 3 then some ⟨label.val, bound⟩ else none
    let bitBlock ← block bit
    let firstBlock ← block first
    let secondBlock ← block second
    let route : Fin 3 → Fin 3 := Fin.cases bitBlock (Fin.cases firstBlock (fun _ => secondBlock))
    if typed : (List.finRange 3).all
        (fun i => decide (incoming (route i) = Packets.get i)) = true then
      some ⟨route, fun i => of_decide_eq_true (List.all_eq_true.mp typed i (List.mem_finRange i))⟩
    else none
  | _ => none

def readRoutes {Φ : Type} (row : Flat Φ 5 2) : Option Routes :=
  (readTypedRoutes Packets.get row).map fun routes => ⟨routes.destination, routes.packet⟩

/-- The ordinary guarded table associated with this exact row shape. -/
abbrev guardedTable {Φ : Type} (opcode : Φ) (routes : Routes) : Table (signature Φ) Packets where
  entry := 0
  row := Fin.cases (motive := fun i : Fin 3 => Row (signature Φ) Packets [Packets.get i, Bit])
    (.request opcode (.var 0) routes.destination routes.packet)
    (Fin.cases (motive := fun i : Fin 2 => Row (signature Φ) Packets [Packets.get i.succ, Bit])
      (.exit 0) (fun _ => .exit 1))
  selected := fun _ => false

/-- A terminal assignment of a constructor bit to the sole projected field. -/
def exitRow {Φ : Type} (label : Fin 5) : Option Φ → Flat Φ 5 2
  | none => .let₂ (.bv 0) (.br label (.pair .unit .unit))
  | some f => .let₂ (.bv 0)
      (.let₁ (.op f .unit)
        (.br label (.pair .unit (.pair (.bv 0) .unit))))

/-- The exact leading decoder and typed request dispatch shared by both profiles. -/
def requestAt {Φ : Type} {d : Nat} (opcode : Φ) (destination : Fin 3 → Fin d) (fallback : Fin d) :
    Flat Φ (d + 2) 2 :=
  .let₂ (.bv 0) (.case (.op opcode (.bv 1))
    (.br ((destination 0).castAdd 2) (.pair (.bv 0) .unit))
    (.case (.bv 0)
      (.br ((destination 1).castAdd 2) (.pair (.bv 0) .unit))
      (.case (.bv 0)
        (.br ((destination 2).castAdd 2) (.pair (.bv 0) .unit))
        (.br (fallback.castAdd 2) (.pair .unit .unit)))))

abbrev requestRow {Φ : Type} (opcode : Φ) (destination : Fin 3 → Fin 3) : Flat Φ 5 2 :=
  requestAt opcode destination 2

/-- Literal lexical readback of the argument-plus-unit entry, the request
with three replies, and its two ordered exit rows. -/
def expected {Φ : Type} (opcode : Φ) (routes : Routes)
    (live : TwoRequest.Tag → Option Φ := fun _ => none) : FiniteCFG Φ 3 2 1 :=
  ⟨.br 0 (.pair (.bv 0) .unit), Fin.cases (motive := fun _ : Fin 3 => Flat Φ 5 2)
    (requestRow opcode routes.destination)
    (Fin.cases (motive := fun _ : Fin 2 => Flat Φ 5 2)
      (exitRow 3 (live 0)) (fun _ => exitRow 4 (live 1)))⟩

variable {κ V K α : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {E : Type → Type}

/-- Number internal labels first, followed by the two original ordered exits. -/
abbrev numberedInterface {d : Nat} (seed : V) (names : Fin (d + 2) ≃ K) : Interface κ V K :=
  ⟨1, .snoc .nil (.coprod .unit .unit), fun _ => seed, fun _ _ _ => Subsingleton.elim _ _,
    [names ((0 : Fin 2).natAdd d), names ((1 : Fin 2).natAdd d)], fun _ => .unit⟩

/-- The fixed three-row profile uses the same numbered interface. -/
abbrev interface (seed : V) (names : Fin 5 ≃ K) : Interface κ V K :=
  numberedInterface seed names

variable {seed : V} {names : Fin 5 ≃ K} {source : CFG V K P.Instr}

local notation "I" => (interface (κ := κ) seed names)

variable {fields : K → List (V × Ty κ)}
variable (a : Admission P (interface (κ := κ) seed names) fields source)

local notation "lexical" => a.versioned.source

/-- A checked numbered lexical table at the public bit entry and two exits. -/
structure NumberedReadback {d : Nat} {names : Fin (d + 2) ≃ K}
    (a : Admission P (numberedInterface seed names) fields source) (code : FiniteCFG P.Instr d 2 1) : Type where
  count : a.versioned.source.blocks.length = d
  accepted : elaborateAt a.versioned.source (numberedInterface (κ := κ) seed names).exits
    (numberedInterface (κ := κ) seed names).version.names d count = some code
  numbered : ∀ i : Fin (d + 2), (labelIndex a.versioned.source.blocks
    (numberedInterface (κ := κ) seed names).exits (names i)).map Fin.val = some i.val

abbrev Readback (code : FiniteCFG P.Instr 3 2 1) := NumberedReadback a code

/-- Success records the extracted routes and certifies the exact admitted lexical
readback and first-match numbering of all five labels, independent of reachable rank. -/
structure Checked (opcode : P.Instr) (live : TwoRequest.Tag → Option P.Instr := fun _ => none) : Type where
  routes : Routes
  count : (lexical).blocks.length = 3
  accepted : elaborateAt lexical (I).exits (I).version.names 3 count = some (expected opcode routes live)
  numbered : ∀ i : Fin 5, (labelIndex (lexical).blocks (I).exits (names i)).map Fin.val = some i.val

/-- Transport literal readback across the checked written row count. -/
theorem recover_readback {source : CFG V K P.Instr} {d n : Nat} {exits : List K}
    {captures : Fin n → V} {code : FiniteCFG P.Instr d exits.length n}
    (count : source.blocks.length = d) {e : Nat} (changeCount : d = e)
    (read : elaborateAt source exits captures d count = some code) :
    elaborateAt source exits captures e (count.trans changeCount) =
      some (cast (congrArg (fun x => FiniteCFG P.Instr x exits.length n) changeCount) code) := by
  cases changeCount
  exact read

/-- Read a profile from the admitted code and verify its reconstruction and numbering. -/
def checkNumberedReadback [DecidableEq P.Instr] {Profile : Type} {d : Nat}
    {names : Fin (d + 2) ≃ K} (a : Admission P (numberedInterface seed names) fields source)
    (read : FiniteCFG P.Instr d 2 1 → Option Profile)
    (expected : Profile → FiniteCFG P.Instr d 2 1) :
    Option (Σ profile, NumberedReadback a (expected profile)) :=
  if h : a.versioned.table.blocks = d then do
    let code : FiniteCFG P.Instr d 2 1 :=
      cast (congrArg (fun x => FiniteCFG P.Instr x 2 1) h) a.versioned.table.code
    let profile ← read code
    let want := expected profile
    if rows : code.entry = want.entry ∧ ∀ i, code.block i = want.block i then
      have same : code = want := congrArg₂ FiniteCFG.mk rows.1 (funext rows.2)
      let count := a.versioned.count.trans h
      if numbered : (List.finRange (d + 2)).all (fun i =>
          decide ((labelIndex a.versioned.source.blocks (numberedInterface (κ := κ) seed names).exits (names i)).map Fin.val = some i.val)) = true then
        some ⟨profile, ⟨count, (recover_readback a.versioned.count h a.versioned.accepted).trans
          (congrArg some same),
          fun i => of_decide_eq_true (List.all_eq_true.mp numbered i (List.mem_finRange i))⟩⟩
      else none
    else none
  else none

/-- Read a profile from the admitted code and verify its reconstruction and numbering. -/
def checkReadback [DecidableEq P.Instr] {Profile : Type}
    (read : FiniteCFG P.Instr 3 2 1 → Option Profile)
    (expected : Profile → FiniteCFG P.Instr 3 2 1) :
    Option (Σ profile, Readback a (expected profile)) :=
  checkNumberedReadback a read expected

/-- Extract routes and check the existing admitted code against the reconstructed
entry, row shapes, and label numbering. -/
def recognize [DecidableEq P.Instr] (opcode : P.Instr)
    (live : TwoRequest.Tag → Option P.Instr := fun _ => none) : Option (Checked a opcode live) :=
  (checkReadback a (fun code => readRoutes (code.block 0)) (fun routes => expected opcode routes live)).map
    fun ⟨routes, readback⟩ => ⟨routes, readback.count, readback.accepted, readback.numbered⟩

def Checked.readback {opcode : P.Instr} {live : TwoRequest.Tag → Option P.Instr}
    (checked : Checked a opcode live) : Readback a (expected opcode checked.routes live) :=
  ⟨checked.count, checked.accepted, checked.numbered⟩

def restoreAt {d : Nat} (names : Fin (d + 2) ≃ K) (p : Transfer α) : K × Value α :=
  (names (if h : p.1 < d + 2 then ⟨p.1, h⟩ else 0), p.2)

/-- Re-encode constructor values in the named runtime. The atom arm completes
the function on raw values. No typed packet in this fragment can take it. -/
abbrev restore (names : Fin 5 ≃ K) (p : Transfer α) : K × Value α :=
  restoreAt names p

def encodeValue {β : Type*} {γ : Type*} (atom : β → γ) : Value β → Value γ
  | .atom a => .atom (atom a)
  | .unit => .unit
  | .pair a b => .pair (encodeValue atom a) (encodeValue atom b)
  | .inl a => .inl (encodeValue atom a)
  | .inr a => .inr (encodeValue atom a)

/-- Pack the typed reply using the guarded native signature's existing codec. -/
def replyValue (atom : Unit → α) (reply : Packet Packets) : Value α :=
  encodeValue atom (pack reply).val

def bitValue {α : Type*} (bit : Bool) : Value α :=
  if bit then .inr .unit else .inl .unit

def exitPayload {α : Type*} : Option Bool → Value α
  | none => .pair .unit .unit
  | some bit => .pair .unit (.pair (bitValue bit) .unit)

/-- The optional terminal instruction and its exact constructor result.
Every terminal instruction here is interpreted purely on unit. -/
abbrev LiveProfile (Φ : Type) := TwoRequest.Tag → Option (Φ × Bool)

def liveOpcodes {Φ : Type} (profile : LiveProfile Φ) (i : TwoRequest.Tag) : Option Φ :=
  (profile i).map Prod.fst

def liveValues {Φ : Type} (profile : LiveProfile Φ) (i : TwoRequest.Tag) : Option Bool :=
  (profile i).map Prod.snd

def LiveAgreement {Φ : Type} (profile : LiveProfile Φ) (instr : Primitive E Φ α) : Prop :=
  ∀ i f bit, profile i = some (f, bit) → instr f .unit = pure (bitValue bit)

def exitResult (live : TwoRequest.Tag → Option Bool) (i : TwoRequest.Tag) : Transfer α :=
  LambdaSSA.FiniteCFG.packedTreeOutput (i.val, exitPayload (live i))

def encodeCursorWith (live : TwoRequest.Tag → Option Bool) (names : Fin 5 ≃ K)
    (atom : Unit → α) (c : Cursor Packets) : K × Value α :=
  match c.down with
  | .inl i => (names (i.natAdd 3), exitPayload (live i))
  | .inr p => (names (p.1.castAdd 2), .pair (encodeValue atom p.2.val) .unit)

abbrev encodeCursor (names : Fin 5 ≃ K) (atom : Unit → α) :=
  encodeCursorWith (fun _ => none) names atom

/-- The shared query evaluator returns the same tagged replies as the raw
named primitive at every typed bit argument. -/
def QueryAgreement (opcode : P.Instr) (atom : Unit → α) (query : Query (signature P.Instr) E)
    (instr : Primitive E P.Instr α) : Prop :=
  ∀ x : Syntax.Payload Bit,
    instr opcode (encodeValue atom x.val) =
      (query opcode x >>= fun p => pure (replyValue atom p.down))

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize
