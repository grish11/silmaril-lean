module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FiniteSupport.Model.Reachable.Defs

/-! # Exact guarded tables with constructor-only internal jumps -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent

open Category.FiniteIteration hiding Row Table
open CFG.Dependent (Packet internal_type)
open TwoRequest (Exits)

universe u v

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}
  {R T Γ Δ : List Syntax.Ty} {A B C : Syntax.Ty} {σ : Type v}

abbrev GuardedTable (S : RequestSignature Φ) (R : List Syntax.Ty) := OpenOperands.Table S R

/-- Constructor substitution is simultaneous and does not issue a request. -/
def substitute (args : (i : Fin Δ.length) → Syntax.Expr Γ (Δ.get i)) :
    {A : Syntax.Ty} → Syntax.Expr Δ A → Syntax.Expr Γ A
  | _, .var i => args i
  | _, .unit => .unit
  | _, .pair a b => .pair (substitute args a) (substitute args b)
  | _, .inl a => .inl (substitute args a)
  | _, .inr a => .inr (substitute args a)

/-- Replace the incoming packet while keeping the exact caller binding. -/
def replacePacket (arg : Syntax.Expr [A, C] B) : (i : Fin 2) → Syntax.Expr [A, C] ([B, C].get i) :=
  Fin.cases (motive := fun i => Syntax.Expr [A, C] ([B, C].get i)) arg (fun i => .var (Γ := [A, C]) i.succ)

def specialize (arg : Syntax.Expr [A, C] B) :
    OpenOperands.Row S R [B, C] → OpenOperands.Row S R [A, C]
  | .exit tag => .exit tag
  | .diverge => .diverge
  | .request f operand next typed => .request f (substitute (Γ := [A, C]) (Δ := [B, C]) (replacePacket arg) operand) next typed

/-- Expose the guarded head in an exact typed environment after resolving
its pure prefix. Exit selection is retained on the exposed head. -/
def evalHead (selected : TwoRequest.Tag → Bool) (env : Syntax.Bindings Γ) :
    OpenOperands.Row S R Γ → Head S R
  | .exit i => .exit i (selected i)
  | .diverge => .diverge
  | .request f arg next typed => .request f (arg.eval env) fun j p =>
    ⟨next j, cast (congrArg Syntax.Payload (typed j).symm) p⟩

inductive HeadResult (S : RequestSignature Φ) (R : List Syntax.Ty) where
  | ready (head : Head S R)
  | diverge

/-- A silent row is one native unconditional jump with a pure constructor
operand. Productive rows are the existing exact guarded rows. -/
inductive Row (S : RequestSignature Φ) (R Γ : List Syntax.Ty) where
  | jump (target : Fin R.length) (arg : Syntax.Expr Γ (R.get target))
  | guarded (row : OpenOperands.Row S R Γ)

def Row.native : Row S R Γ → CFG.Dependent.Native.Typed Φ Γ (R ++ Exits)
  | .jump i arg => CFG.Dependent.Native.jump (Feedback.internal R Exits i) (internal_type i) arg
  | .guarded row => row.native

structure Table (S : RequestSignature Φ) (R : List Syntax.Ty) where
  entry : Fin R.length
  row : (i : Fin R.length) → Row S R [R.get i, R.get entry]
  selected : TwoRequest.Tag → Bool

def Table.ofGuarded (g : GuardedTable S R) : Table S R :=
  ⟨g.entry, fun i => .guarded (g.row i), g.selected⟩

/-- The guarded view is used only to interpret productive rows. -/
abbrev Table.visible (g : Table S R) : GuardedTable S R where
  entry := g.entry
  row i :=
    match g.row i with
    | .guarded row => row
    | .jump .. => .exit 0
  selected := g.selected

def Table.blocks (g : Table S R) (i : Fin R.length) :
    CFG.Dependent.Native.Typed Φ [R.get i, R.get g.entry] (R ++ Exits) :=
  (g.row i).native

def Table.native (g : Table S R) : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits :=
  ⟨nativeFeedback g.visible.entryRegion g.blocks, nativeFeedback_hasType g.visible.entryRegion g.blocks⟩

def Table.checkNative [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) : Bool :=
  CFG.Dependent.Native.sameRegion raw.val g.native.val

/-- Scan just the labels of the silent graph, retaining the origin of a
productive row. The typed resolver can specialize operands separately. -/
def Table.labelRows (g : OpenOperands.Silent.Table S R) (i : Fin R.length) :
    Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Row R.length R.length 1 :=
  match g.row i with
  | .jump j _ => .repeat j
  | .guarded _ => .stop (.ret i 0)

/-- Follow only silent edges, substituting each jump operand into the
productive row's argument. A productive row uses one unit of scan fuel. -/
def Table.resolve (g : Table S R) :
    (fuel : Nat) → (i : Fin R.length) → Option (OpenOperands.Row S R [R.get i, R.get g.entry])
  | 0, _ => none
  | fuel + 1, i =>
    match g.row i with
    | .guarded row => some row
    | .jump j arg => (g.resolve fuel j).map (specialize arg)

/-- Whether every silent scan exposes a row within the label bound. -/
def Table.normalizes (g : Table S R) : Bool :=
  (List.finRange R.length).all fun i => (g.resolve R.length i).isSome

/-- Resolve each silent prefix at its exact label. Exhaustion is an
ordinary-divergence terminal. Request backedges keep their original labels. -/
abbrev Table.normalize (g : Table S R) : GuardedTable S R where
  entry := g.entry
  row i := (g.resolve R.length i).getD .diverge
  selected := g.selected

/-- The total normalization also serves the previous all-resolved profile. -/
abbrev Table.normalized (g : Table S R) (_ok : g.normalizes = true) : GuardedTable S R :=
  g.normalize

noncomputable def Table.feedback (g : Table S R)
    (caller : Syntax.Payload (R.get g.entry)) (prim : Syntax.StatePrimitives Φ σ) :
    Feedback.Run R Exits Unit σ :=
  feedbackRun (.native g.visible.entryRegion) (fun i => .native (g.blocks i))
    (Syntax.model prim (g.visible.bindings caller)).raw

/-- Failed readback is unknown. Exhaustion of the silent scan reports
ordinary divergence, while an exposed head retains its typed replies. -/
def Table.head? [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (caller : Syntax.Payload (R.get g.entry)) (p : Packet R) : Option (HeadResult S R) :=
  if g.checkNative raw then
    some (match g.resolve R.length p.1 with
      | some row => .ready (evalHead g.selected ((g.visible.bindings caller).push p.2) row)
      | none => .diverge)
  else none

/-- Apply the reachable-pair bound after resolving the silent heads.
A divergent head creates no successor pair or interpreter query. -/
def Table.cutoff [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (callers : CallerEnumeration A)
    (decodeLeft : Syntax.Payload A → Syntax.Payload (R.get g.entry))
    (decodeRight : Syntax.Payload A → Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) : Nat :=
  g.normalize.reachableCutoff h.normalize callers decodeLeft decodeRight replies left right

/-- Run the reachable-product comparison after exact native readback.
The finite scan classifies exhausted silent control as ordinary divergence. -/
def Table.checkEntries? [DecidableEq Φ] (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (callers : CallerEnumeration A)
    (decodeLeft : Syntax.Payload A → Syntax.Payload (R.get g.entry))
    (decodeRight : Syntax.Payload A → Syntax.Payload (T.get h.entry))
    (replies : ReplyEnumeration S) (left : ConfigurationEnumeration R) (right : ConfigurationEnumeration T) :
    Option Bool :=
  if g.checkNative raw && h.checkNative raw' then
    g.normalize.checkReachableEntries? h.normalize
      g.normalize.native h.normalize.native callers decodeLeft decodeRight replies left right
  else none

/-- Deterministic refinement of the original decorated endpoints. -/
def Table.DeterministicRefines (g : Table S R) (h : Table S T)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (raw' : CFG.Dependent.Native.Typed Φ [T.get h.entry] Exits)
    (decodeLeft : Syntax.Payload A → Syntax.Payload (R.get g.entry))
    (decodeRight : Syntax.Payload A → Syntax.Payload (T.get h.entry)) : Prop :=
  g.visible.DeterministicRefines.{u,v} h.visible raw raw' decodeLeft decodeRight

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Silent
