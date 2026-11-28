module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.Defs

/-! # Environment-indexed extraction for open constructor operands -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

open LambdaSSA.Acyclic.Positional
open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent (unpack internal_type external_type)
open TwoRequest (Exit Exits Tag exit_type)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ}

/-- A request records the evaluated, exactly typed argument. Its continuation
receives both the reply position and the actual payload at that position. -/
inductive Tree (S : RequestSignature Φ) where
  | stop (exit : Exit)
  | ask (f : Φ) (arg : Syntax.Payload (instrSrc f))
      (next : (i : Fin (S.replies f).length) → Syntax.Payload ((S.replies f).get i) → Tree S)

def Tree.execute {n : Nat} (prim : Syntax.Primitives Φ n) : Tree S → Fin n → Result 2 n
  | .stop e, s => e.result s
  | .ask f arg next, s =>
    match prim f arg s with
    | .ret a t =>
      let p := unpack (cast (congrArg Syntax.Payload (S.target f)) a)
      (next p.1 p.2).execute prim t
    | .fault t => .fault t
    | .diverge => .diverge

/-- Native rows use exact constructor expressions in their written context. -/
inductive Row (S : RequestSignature Φ) (R Γ : List Syntax.Ty) where
  | exit (i : Tag)
  | diverge
  | request (f : Φ) (arg : Syntax.Expr Γ (instrSrc f))
      (next : Fin (S.replies f).length → Fin R.length)
      (packet : ∀ i, R.get (next i) = (S.replies f).get i)

variable {R Γ : List Syntax.Ty}

def Row.targets : Row S R Γ → List (Fin R.length)
  | .exit _ | .diverge => []
  | .request _ _ next _ => List.ofFn next

def Row.native : Row S R Γ → CFG.Dependent.Native.Typed Φ Γ (R ++ Exits)
  | .exit i => CFG.Dependent.Native.jump (CFG.Dependent.exitLabel R Exits i)
      ((external_type (R := R) (L := Exits) i).trans (exit_type i)) .unit
  | .diverge => CFG.Dependent.Native.diverge
  | .request f arg next packet =>
    CFG.Dependent.Native.packedRequestTo f arg (S.target f)
      (fun j => Feedback.internal R Exits (next j))
      (fun j => (internal_type (L := Exits) (next j)).trans (packet j))

/-- The entry reads the caller's packet. A block can inspect its incoming
packet and the unchanged caller packet, at slots zero and one respectively. -/
structure Table (S : RequestSignature Φ) (R : List Syntax.Ty) where
  entry : Fin R.length
  row : (i : Fin R.length) → Row S R [R.get i, R.get entry]
  selected : Tag → Bool

def Table.bindings (g : Table S R) (input : Syntax.Payload (R.get g.entry)) :
    Syntax.Bindings [R.get g.entry] :=
  Syntax.emptyBindings.push input

def Table.entryRegion (g : Table S R) : CFG.Dependent.Native.Typed Φ [R.get g.entry] (R ++ Exits) :=
  CFG.Dependent.Native.jump (Feedback.internal R Exits g.entry) (internal_type g.entry) (.var 0)

def Table.blocks (g : Table S R) (i : Fin R.length) :
    CFG.Dependent.Native.Typed Φ [R.get i, R.get g.entry] (R ++ Exits) :=
  (g.row i).native

def Table.native (g : Table S R) : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits :=
  ⟨nativeFeedback g.entryRegion g.blocks, nativeFeedback_hasType g.entryRegion g.blocks⟩

/-- The acyclic tree extractor has no ordinary-divergence leaf. A
divergent row is treated as a self-cycle by its rank admission check. -/
def Table.targets (g : Table S R) (i : Fin R.length) : List (Fin R.length) :=
  match g.row i with
  | .diverge => [i]
  | row => row.targets

abbrev Table.ranks (g : Table S R) := Rank.rounds g.targets R.length

def Table.entryCheck (g : Table S R) : Bool :=
  Rank.checkFrom g.targets [g.entry]

theorem Table.ranked_not_diverge (g : Table S R) {i : Fin R.length}
    (ranked : (g.ranks.get i).isSome = true) (row : g.row i = .diverge) : False := by
  have edge : i ∈ g.targets i := by simp [Table.targets, row]
  exact (Nat.lt_irrefl _) (Rank.ranked_successor g.targets ranked edge).2

/-- Consume one unit of the decreasing rank budget per local transfer.
The reply creates the next environment only when the continuation is used. -/
def Table.expand (g : Table S R) (input : Syntax.Payload (R.get g.entry)) :
    (fuel : Nat) → (i : Fin R.length) → (g.ranks.get i).isSome = true →
      (g.ranks.get i).getD 0 < fuel → Syntax.Payload (R.get i) → Tree S
  | 0, _, _, bound, _ => (Nat.not_lt_zero _ bound).elim
  | fuel + 1, i, ranked, bound, incoming =>
    match eq : g.row i with
    | .exit j => .stop (if g.selected j then .ub else .ret j)
    | .diverge => (g.ranked_not_diverge ranked eq).elim
    | .request f arg next packet =>
      .ask f (arg.eval ((g.bindings input).push incoming)) fun j a =>
        have edge : next j ∈ g.targets i := by
          rw [Table.targets, eq]
          exact List.mem_ofFn.mpr ⟨j, rfl⟩
        have successor := Rank.ranked_successor g.targets ranked edge
        g.expand input fuel (next j) successor.1
          (successor.2.trans_le (Nat.le_of_lt_succ bound))
          (cast (congrArg Syntax.Payload (packet j).symm) a)

def Table.extract (g : Table S R) (ok : g.entryCheck = true)
    (input : Syntax.Payload (R.get g.entry)) : Tree S :=
  g.expand input ((g.ranks.get g.entry).getD 0 + 1) g.entry
    (Rank.ranked_of_checkFrom g.targets ok (by simp)) (Nat.lt_succ_self _) input

/-- Exact re-emission of the typed table, independent of control-flow rank. -/
def Table.checkNative [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) : Bool :=
  CFG.Dependent.Native.sameRegion raw.val g.native.val

def Table.check [DecidableEq Φ] (g : Table S R) (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits) :
    Bool :=
  g.checkNative raw && g.entryCheck

theorem Table.checked_rank [DecidableEq Φ] {g : Table S R}
    {raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits} (ok : g.check raw = true) :
    g.entryCheck = true := by
  simp only [Table.check, Bool.and_eq_true] at ok
  exact ok.2

/-- The typed witness must re-emit the original source before extraction. -/
def Table.extract? [DecidableEq Φ] (g : Table S R)
    (raw : CFG.Dependent.Native.Typed Φ [R.get g.entry] Exits)
    (input : Syntax.Payload (R.get g.entry)) : Option (Tree S) :=
  if ok : g.check raw = true then some (g.extract (g.checked_rank ok) input) else none

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
