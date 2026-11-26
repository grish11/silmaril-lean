module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.HandledTrace.Readback.Construction.RequestPrefix.EffectfulEntry.Multiple.Defs

/-! # Schedule the effects in a written request operand -/

@[expose] public section

namespace Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed

open LambdaSSA (FiniteCFG Flat Region Tm)
open Morphism.CaseSSA (erase)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
  (Expr PacketType PrimitiveSignature Slot elaborateExpr)

variable {F : Type} {blocks exits captures labels : Nat} {Γ Δ Θ : List PacketType}
  {sig : PrimitiveSignature F} {ty : PacketType}

/-- The checked operand grammar shares structural leaves with the public
dispatcher. A primitive's argument is checked recursively at its input type. -/
inductive Operand (sig : PrimitiveSignature F) : List PacketType → PacketType → Type
  | pure {Γ : List PacketType} {a : PacketType} (value : Expr Γ a) : Operand sig Γ a
  | pair {Γ : List PacketType} {a b : PacketType} (left : Operand sig Γ a) (right : Operand sig Γ b) :
      Operand sig Γ (.product a b)
  | call {Γ : List PacketType} (op : F) (arg : Operand sig Γ (sig.argument op)) : Operand sig Γ (sig.reply op)
  | let₁ {Γ : List PacketType} {a b : PacketType} (value : Operand sig Γ a) (body : Operand sig (a :: Γ) b) :
      Operand sig Γ b
  | let₂ {Γ : List PacketType} {a b c : PacketType} (value : Operand sig Γ (.product a b))
      (body : Operand sig (b :: a :: Γ) c) : Operand sig Γ c

def Operand.written : {Γ : List PacketType} → {ty : PacketType} → Operand sig Γ ty → Tm F
  | _, _, .pure value => operand position value
  | _, _, .pair left right => .pair left.written right.written
  | _, _, .call op arg => .op op arg.written
  | _, _, .let₁ value body => .let₁ value.written body.written
  | _, _, .let₂ value body => .let₂ value.written body.written

abbrev SlotMap (Γ Δ : List PacketType) := ∀ {a}, Slot Γ a → Slot Δ a

abbrev Substitution (Γ Δ : List PacketType) := ∀ {a}, Slot Γ a → Expr Δ a

def substExpr (values : Substitution Γ Δ) : {ty : PacketType} → Expr Γ ty → Expr Δ ty
  | _, .var slot => values slot
  | _, .unit => .unit
  | _, .pair left right => .pair (substExpr values left) (substExpr values right)

def renameExpr (slots : SlotMap Γ Δ) (value : Expr Γ ty) : Expr Δ ty :=
  substExpr (fun slot => .var (slots slot)) value

/-- Only the body gets the initializer's residual value at slot zero. -/
def bindSubstitution (value : Expr Δ ty) (older : Substitution Γ Δ) : Substitution (ty :: Γ) Δ :=
  fun {_} slot => match slot with
  | .here => value
  | .there slot => older slot

/-- Each application adds its reply to the scope. A silent product
destructuring adds the right field at slot zero and the left at slot one. -/
inductive Requests (sig : PrimitiveSignature F) : List PacketType → List PacketType → Type
  | done {Γ : List PacketType} : Requests sig Γ Γ
  | request {Γ Δ : List PacketType} (op : F) (arg : Expr Γ (sig.argument op))
      (next : Requests sig (sig.reply op :: Γ) Δ) : Requests sig Γ Δ
  | unpack {Γ Δ : List PacketType} {a b : PacketType} (value : Expr Γ (.product a b))
      (next : Requests sig (b :: a :: Γ) Δ) : Requests sig Γ Δ

def Requests.append : {Γ Δ : List PacketType} → Requests sig Γ Δ → Requests sig Δ Θ → Requests sig Γ Θ
  | _, _, .done, next => next
  | _, _, .request op arg rest, next => .request op arg (rest.append next)
  | _, _, .unpack value rest, next => .unpack value (rest.append next)

/-- Embed an older typed slot through the reply and product binders. -/
def Requests.slots : {Γ Δ : List PacketType} → Requests sig Γ Δ → SlotMap Γ Δ
  | _, _, .done, _, slot => slot
  | _, _, .request _ _ next, _, slot => next.slots (.there slot)
  | _, _, .unpack _ next, _, slot => next.slots (.there (.there slot))

/-- Carry substituted values through all slots added by a schedule. -/
def Requests.weaken (requests : Requests sig Δ Θ) (values : Substitution Γ Δ) : Substitution Γ Θ :=
  fun {_} slot => renameExpr requests.slots (values slot)

/-- The same embedding for raw lexical indices, including the caller's
ambient environment beyond the checked slots. -/
def Requests.shift : {Γ Δ : List PacketType} → Requests sig Γ Δ → Nat → Nat
  | _, _, .done, i => i
  | _, _, .request _ _ next, i => next.shift (i + 1)
  | _, _, .unpack _ next, i => next.shift (i + 2)

/-- Insert the schedule as ordinary written lets. -/
def Requests.wrap {A : Type} (bind unpack : Tm F → A → A) :
    {Γ Δ : List PacketType} → Requests sig Γ Δ → A → A
  | _, _, .done, body => body
  | _, _, .request op arg next, body => bind (.op op (operand position arg)) (next.wrap bind unpack body)
  | _, _, .unpack value next, body => unpack (operand position value) (next.wrap bind unpack body)

structure Scheduled (sig : PrimitiveSignature F) (Γ : List PacketType) (ty : PacketType) where
  scope : List PacketType
  requests : Requests sig Γ scope
  value : Expr scope ty

/-- Compose effects in written order. Each let schedules its initializer
once, then substitutes the residual value or binds its two fields. -/
def Operand.scheduleWith : {Γ : List PacketType} → {ty : PacketType} → Operand sig Γ ty →
    {Δ : List PacketType} → Substitution Γ Δ → Scheduled sig Δ ty
  | _, _, .pure value, Δ, values => ⟨Δ, .done, substExpr values value⟩
  | _, _, .pair left right, _, values =>
    let l := left.scheduleWith values
    let r := right.scheduleWith (l.requests.weaken values)
    ⟨r.scope, l.requests.append r.requests, .pair (renameExpr r.requests.slots l.value) r.value⟩
  | _, _, .call op arg, _, values =>
    let result := arg.scheduleWith values
    ⟨sig.reply op :: result.scope, result.requests.append (.request op result.value .done), .var .here⟩
  | _, _, .let₁ value body, _, values =>
    let init := value.scheduleWith values
    let body := body.scheduleWith (bindSubstitution init.value (init.requests.weaken values))
    ⟨body.scope, init.requests.append body.requests, body.value⟩
  | _, _, .let₂ (a := a) (b := b) value body, _, values =>
    let init := value.scheduleWith values
    let unpack : Requests sig init.scope (b :: a :: init.scope) := .unpack init.value .done
    let initialized := init.requests.append unpack
    let body := body.scheduleWith
      (bindSubstitution (.var .here) (bindSubstitution (.var (.there .here)) (initialized.weaken values)))
    ⟨body.scope, initialized.append body.requests, body.value⟩

def Operand.scheduleAt (arg : Operand sig Γ ty) (slots : SlotMap Γ Δ) : Scheduled sig Δ ty :=
  arg.scheduleWith (fun slot => .var (slots slot))

def Operand.schedule (arg : Operand sig Γ ty) : Scheduled sig Γ ty :=
  arg.scheduleAt (fun slot => slot)

def Scheduled.term (scheduled : Scheduled sig Γ ty) : Tm F :=
  scheduled.requests.wrap Tm.let₁ Tm.let₂ (operand position scheduled.value)

def readOperand (sig : PrimitiveSignature F) :
    (Γ : List PacketType) → Tm F → Option (Σ ty : PacketType, Operand sig Γ ty)
  | Γ, .op op arg => do
    let ⟨ty, arg⟩ ← readOperand sig Γ arg
    if typed : ty = sig.argument op then
      some ⟨sig.reply op, .call op (typed ▸ arg)⟩
    else none
  | Γ, .pair left right => do
    let ⟨a, left⟩ ← readOperand sig Γ left
    let ⟨b, right⟩ ← readOperand sig Γ right
    return ⟨.product a b, .pair left right⟩
  | Γ, .let₁ value body => do
    let ⟨a, value⟩ ← readOperand sig Γ value
    let ⟨b, body⟩ ← readOperand sig (a :: Γ) body
    return ⟨b, .let₁ value body⟩
  | Γ, .let₂ value body => do
    let ⟨.product a b, value⟩ ← readOperand sig Γ value | none
    let ⟨c, body⟩ ← readOperand sig (b :: a :: Γ) body
    return ⟨c, .let₂ value body⟩
  | Γ, raw => do
    let ⟨ty, value⟩ ← elaborateExpr Γ raw
    return ⟨ty, .pure value⟩

/-- Execute the schedule before the outer request. Shift the older
slots in its continuation while keeping the outer reply at slot zero. -/
def hoist (outer : F) (arg : Operand sig Γ (sig.argument outer)) (tail : Region F) : Region F :=
  let scheduled := arg.schedule
  scheduled.requests.wrap Region.let₁ Region.let₂
    (.let₁ (.op outer (operand position scheduled.value))
      (tail.renameVars (Silmaril.DeBruijn.lift scheduled.requests.shift)))

/-- An exact written entry boundary and its operand type. Jumps use the
same positional block and exit profile as the shared CFG checker. -/
inductive Boundary (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (types : Fin labels → PacketType)
  | request (outer : F) (arg : Operand sig context.toList (sig.argument outer))
      (tail : Flat F labels (captures + 1))
  | jump (label : Fin labels) (arg : Operand sig context.toList (types label))

def Boundary.written {labels : Nat} {context : BoundCtx PacketType captures}
    {types : Fin labels → PacketType} : Boundary sig context types → Region F
  | .request outer arg tail => .let₁ (.op outer arg.written) tail.erase
  | .jump label arg => .br label.val arg.written

/-- A jump consumes the structural residual directly at its original
target. A request still shifts the older slots beneath its own reply. -/
def Boundary.lower {labels : Nat} {context : BoundCtx PacketType captures}
    {types : Fin labels → PacketType} : Boundary sig context types → Region F
  | .request outer arg tail => hoist outer arg tail.erase
  | .jump label arg =>
    let scheduled := arg.schedule
    scheduled.requests.wrap Region.let₁ Region.let₂ (.br label.val (operand position scheduled.value))

/-- Check both the operand's synthesized type and its exact written syntax. -/
def readArgument [DecidableEq F] (sig : PrimitiveSignature F) (Γ : List PacketType)
    (expected : PacketType) (original : Tm F) :
    Option {arg : Operand sig Γ expected // original = arg.written} := do
  let ⟨ty, arg⟩ ← readOperand sig Γ original
  if typed : ty = expected then
    let arg := typed ▸ arg
    if exactArg : original = arg.written then some ⟨arg, exactArg⟩ else none
  else none

def Boundary.read [DecidableEq F] (sig : PrimitiveSignature F)
    (context : BoundCtx PacketType captures) (types : Fin labels → PacketType) :
    (original : Flat F labels captures) → Option {b : Boundary sig context types // original.erase = b.written}
  | .let₁ (.op outer original) tail => do
    let ⟨arg, exactArg⟩ ← readArgument sig context.toList (sig.argument outer) (erase original)
    return ⟨.request outer arg tail, by
      change Region.let₁ (.op outer (erase original)) tail.erase = _
      rw [exactArg]
      rfl⟩
  | .br label original => do
    let ⟨arg, exactArg⟩ ← readArgument sig context.toList (types label) (erase original)
    return ⟨.jump label arg, by
      change Region.br label.val (erase original) = _
      rw [exactArg]
      rfl⟩
  | _ => none

structure Lifted (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  boundary : Boundary sig context (SSA.FiniteSum.append packets outputs)
  source_eq : source.entry.erase = boundary.written
  entry : Flat F (blocks + exits) captures
  entry_eq : entry.erase = boundary.lower

def Lifted.code {context : BoundCtx PacketType captures} {packets : Fin blocks → PacketType}
    {outputs : Fin exits → PacketType} {source : FiniteCFG F blocks exits captures}
    (lifted : Lifted sig context packets outputs source) : FiniteCFG F blocks exits captures :=
  ⟨lifted.entry, source.block⟩

/-- Check an operand at a written request or jump, including outward
jumps. Require its exact erased syntax and the boundary's expected type
before reifying the scheduled entry. -/
def lift [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Lifted sig context packets outputs source) := do
  let ⟨boundary, sourceEq⟩ ← Boundary.read sig context (SSA.FiniteSum.append packets outputs) source.entry
  let entry ← scopedRow (blocks + exits) captures boundary.lower
  return ⟨boundary, sourceEq, entry.val, entry.property⟩

structure Compiled (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) where
  lifted : Lifted sig context packets outputs source
  sourceTyped : letI := sig.typing; source.HasType context packets outputs
  checked : Multiple.Compiled sig context packets outputs lifted.code

/-- Check the original CFG and lower its operand schedule through the
existing recursive continuation compiler. The old block table is shared.
The continuation compiler requires a nonempty frame at each scheduled
request or unpack. -/
def compile [DecidableEq F] (sig : PrimitiveSignature F) (context : BoundCtx PacketType captures)
    (packets : Fin blocks → PacketType) (outputs : Fin exits → PacketType)
    (source : FiniteCFG F blocks exits captures) : Option (Compiled sig context packets outputs source) :=
  letI := sig.typing;
  if original : NamedFlat.check source context packets outputs = true then
    match lift sig context packets outputs source with
    | none => none
    | some lifted =>
      (Multiple.compile sig context packets outputs lifted.code).map fun checked =>
        ⟨lifted, NamedFlat.check_sound _ _ _ _ original, checked⟩
  else none

end Silmaril.Isotope.Bridge.NamedFlat.Phi.Certified.Entry.OrderedExits.Readback.RequestPrefix.EffectfulEntry.Multiple.Computed
