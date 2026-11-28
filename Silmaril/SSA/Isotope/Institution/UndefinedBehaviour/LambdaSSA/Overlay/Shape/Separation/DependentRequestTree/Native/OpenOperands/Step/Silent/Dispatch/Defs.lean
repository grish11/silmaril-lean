module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Silent.Defs

/-! # Packet-dependent silent dispatch in exact packed LambdaSSA CFGs -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch

open Category (splitPayload)
open Category.FiniteIteration hiding Row Table
open CFG.Dependent (Packet internal_type)
open TwoRequest (Exits Tag)
open Syntax (Expr Payload Bindings StatePrimitives model)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R Γ : List Syntax.Ty} {A B : Syntax.Ty} {σ : Type v}

/-- The case arms bind the selected sum payload. Their pure constructor
operands may also refer to the incoming packet and the fixed caller. -/
inductive Row (S : RequestSignature Φ) (R Γ : List Syntax.Ty) where
  | jump (target : Fin R.length) (arg : Expr Γ (R.get target))
  | dispatch {A B : Syntax.Ty} (arg : Expr Γ (.coprod A B)) (left right : Fin R.length)
      (onLeft : Expr (A :: Γ) (R.get left)) (onRight : Expr (B :: Γ) (R.get right))
  | guarded (row : OpenOperands.Row S R Γ)

def jumpArms (left right : Fin R.length)
    (onLeft : Expr (A :: Γ) (R.get left)) (onRight : Expr (B :: Γ) (R.get right)) :
    (i : Fin [A, B].length) → CFG.Dependent.Native.Typed Φ ([A, B].get i :: Γ) (R ++ Exits) :=
  Fin.cases (motive := fun i => CFG.Dependent.Native.Typed Φ ([A, B].get i :: Γ) (R ++ Exits))
    (CFG.Dependent.Native.jump (Feedback.internal R Exits left) (internal_type left) onLeft)
    (fun i => by
      obtain rfl := Fin.eq_zero i
      exact CFG.Dependent.Native.jump (Feedback.internal R Exits right) (internal_type right) onRight)

def Row.native : Row S R Γ → CFG.Dependent.Native.Typed Φ Γ (R ++ Exits)
  | .jump i arg => CFG.Dependent.Native.jump (Feedback.internal R Exits i) (internal_type i) arg
  | .dispatch arg left right onLeft onRight =>
    let scrutinee := Syntax.Program.caseRegion (Φ := Φ) arg
    let arms := jumpArms left right onLeft onRight
    ⟨nativeLsubst scrutinee arms, nativeLsubst_hasType scrutinee arms⟩
  | .guarded row => row.native

def Row.step (selected : Tag → Bool) (env : Bindings Γ) : Row S R Γ → Packet R ⊕ Head S R
  | .jump target arg => .inl ⟨target, arg.eval env⟩
  | .dispatch arg left right onLeft onRight =>
    match splitPayload (arg.eval env) with
    | .inl a => .inl ⟨left, onLeft.eval (env.push a)⟩
    | .inr b => .inl ⟨right, onRight.eval (env.push b)⟩
  | .guarded row => .inr (evalHead selected env row)

structure Table (S : RequestSignature Φ) (R : List Syntax.Ty) where
  entry : Fin R.length
  row : (i : Fin R.length) → Row S R [R.get i, R.get entry]
  selected : Tag → Bool

/-- The existing guarded table supplies the common entry and bindings.
Only this table's guarded rows are interpreted through the view. -/
abbrev Table.visible (g : Table S R) : GuardedTable S R where
  entry := g.entry
  row i := match g.row i with
    | .guarded row => row
    | _ => .exit 0
  selected := g.selected

def Table.blocks (g : Table S R) (i : Fin R.length) :
    CFG.Dependent.Native.Typed Φ [R.get i, R.get g.entry] (R ++ Exits) :=
  (g.row i).native

def Table.native (g : Table S R) : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits :=
  ⟨nativeFeedback g.visible.entryRegion g.blocks, nativeFeedback_hasType g.visible.entryRegion g.blocks⟩

def Table.checkNative [DecidableEq Φ] (g : Table S R) (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) : Bool :=
  CFG.Dependent.Native.sameRegion raw.val g.native.val

def Table.step (g : Table S R) (caller : Payload (R.get g.entry)) (p : Packet R) :
    Packet R ⊕ Head S R :=
  (g.row p.1).step g.selected ((g.visible.bindings caller).push p.2)

/-- Inspect at most the supplied number of full typed configurations,
keeping the caller fixed. An absent result means the entire scan stayed silent. -/
def Table.scan (g : Table S R) (caller : Payload (R.get g.entry)) :
    Nat → Packet R → Option (Head S R)
  | 0, _ => none
  | fuel + 1, p =>
    match g.step caller p with
    | .inl q => g.scan caller fuel q
    | .inr head => some head

/-- An exhaustive packet inventory bounds silent exposure, even when a
label is visited with several distinct incoming packets. -/
def Table.head (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (p : Packet R) : Head S R :=
  (g.scan caller configs.configs.length p).getD .diverge

/-- Only a failed exact readback is unknown. An admitted cycle exposes
ordinary divergence, which has no query or successful reply. -/
def Table.head? [DecidableEq Φ] (g : Table S R) (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (configs : ConfigurationEnumeration R) (caller : Payload (R.get g.entry)) (p : Packet R) :
    Option (Head S R) :=
  if g.checkNative raw then some (g.head configs caller p) else none

noncomputable def Table.feedback (g : Table S R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) :
    Feedback.Run R Exits Unit σ :=
  feedbackRun (.native g.visible.entryRegion) (fun i => .native (g.blocks i))
    (model prim (g.visible.bindings caller)).raw

/-- Interpret the computed heads in the original feedback interface.
The correspondence uses typed starts and stays at typed successors. -/
noncomputable def Table.normalizedFeedback (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) : Feedback.Run R Exits Unit σ := by
  classical
  exact fun point => match point with
    | .block i a s =>
      if h : Shape.ValueTyped Syntax.atomType a (R.get i) then
        ((g.head configs caller ⟨i, ⟨a, h⟩⟩).execute prim s).routed
      else (StateTransition.diverge : StateTransition R σ).routed
    | .entry s => (StateTransition.repeat ⟨g.entry, caller⟩ s).routed

/-- The normalized denotation keeps the exact ordered exit continuations. -/
noncomputable def Table.observeAt (g : Table S R) (configs : ConfigurationEnumeration R)
    (caller : Payload (R.get g.entry)) (prim : StatePrimitives Φ σ) (p : Packet R) (s : σ) :
    Behaviour Exits.length Unit σ :=
  (Feedback.close (g.normalizedFeedback configs caller prim) (blockPoint p s)).bind fun i a t =>
    Overlay.denote (CFG.Dependent.Native.exitContinuation (Γ := [R.get g.entry]) (L := Exits) (Φ := Φ) g.selected i)
      (extendModel (model prim (g.visible.bindings caller)).raw a) t

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent.Dispatch
