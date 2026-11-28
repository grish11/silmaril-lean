module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Native.ExitUB.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Rank.Thms
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Feedback.Thms

/-! # Rank-certified native tables for typed request-tree extraction -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction

open LambdaSSA.Acyclic.Positional
open Category.FiniteIteration
open Category.FiniteIteration.CFG.Dependent (internal_type)
open TwoRequest (Exits Tag exit_type)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty]

/-- Reply tags can share a destination. Each written edge keeps the exact
incoming type of its destination. -/
inductive Row (S : RequestSignature Φ) (R : List Syntax.Ty) where
  | exit (i : Tag)
  | request (f : Φ) (arg : Syntax.Expr [] (instrSrc f))
      (next : Fin (S.replies f).length → Fin R.length)
      (packet : ∀ i, R.get (next i) = (S.replies f).get i)

variable {S : RequestSignature Φ} {R : List Syntax.Ty}

def Row.targets : Row S R → List (Fin R.length)
  | .exit _ => []
  | .request _ _ next _ => List.ofFn next

def Row.native {A : Syntax.Ty} : Row S R → CFG.Dependent.Native.Typed Φ [A] (R ++ Exits)
  | .exit i => CFG.Dependent.Native.jump (CFG.Dependent.exitLabel R Exits i)
      ((CFG.Dependent.external_type (R := R) (L := Exits) i).trans (exit_type i)) .unit
  | .request f arg next packet =>
    CFG.Dependent.Native.packedRequestTo f (inContext arg) (S.target f)
      (fun j => Feedback.internal R Exits (next j))
      (fun j => (internal_type (L := Exits) (next j)).trans (packet j))

structure Table (S : RequestSignature Φ) (R : List Syntax.Ty) where
  entry : Fin R.length
  input : Syntax.Expr [] (R.get entry)
  row : Fin R.length → Row S R
  selected : Tag → Bool

def Table.entryRegion (g : Table S R) : CFG.Dependent.Native.Typed Φ [] (R ++ Exits) :=
  CFG.Dependent.Native.jump (Feedback.internal R Exits g.entry) (internal_type g.entry) g.input

def Table.blocks (g : Table S R) (i : Fin R.length) : CFG.Dependent.Native.Typed Φ [R.get i] (R ++ Exits) :=
  (g.row i).native

/-- Re-emit the literal typed native table before adding the UB continuations. -/
def Table.native (g : Table S R) : CFG.Dependent.Native.Typed Φ [] Exits :=
  ⟨nativeFeedback g.entryRegion g.blocks, nativeFeedback_hasType g.entryRegion g.blocks⟩

def Table.targets (g : Table S R) (i : Fin R.length) : List (Fin R.length) := (g.row i).targets

abbrev Table.ranks (g : Table S R) := Rank.rounds g.targets R.length

def Table.entryCheck (g : Table S R) : Bool :=
  Rank.checkFrom g.targets [g.entry]

/-- Only the ranked reachable rows are expanded. The source and its syntax
check still include every written row. -/
def Table.extractAt (g : Table S R) (i : Fin R.length) (ranked : (g.ranks.get i).isSome = true) :
    Tree S.replies :=
  match eq : g.row i with
  | .exit j => .stop (if g.selected j then .ub else .ret j)
  | .request f arg next packet =>
    .ask f arg fun j =>
      have edge : next j ∈ g.targets i := by
        rw [Table.targets, eq, Row.targets]
        exact List.mem_ofFn.mpr ⟨j, rfl⟩
      g.extractAt (next j) (Rank.ranked_successor g.targets ranked edge).1
termination_by (g.ranks.get i).getD 0
decreasing_by exact (Rank.ranked_successor g.targets ranked edge).2

def Table.extract (g : Table S R) (ok : g.entryCheck = true) : Tree S.replies :=
  g.extractAt g.entry (Rank.ranked_of_checkFrom g.targets ok (by simp))

/-- Check a proposed typed row witness against the actual native endpoint
and require ranks from the written entry. -/
def Table.check [DecidableEq Φ] (g : Table S R) (raw : CFG.Dependent.Native.Typed Φ [] Exits) : Bool :=
  CFG.Dependent.Native.sameRegion raw.val g.native.val && g.entryCheck

theorem Table.checked_rank [DecidableEq Φ] {g : Table S R} {raw : CFG.Dependent.Native.Typed Φ [] Exits} (ok : g.check raw = true) : g.entryCheck = true := by
  simp only [Table.check, Bool.and_eq_true] at ok
  exact ok.2

/-- Extract only when the typed witness matches the supplied native CFG
and the original entry has a rank. -/
def Table.extract? [DecidableEq Φ] (g : Table S R) (raw : CFG.Dependent.Native.Typed Φ [] Exits) :
    Option (Tree S.replies) :=
  if ok : g.check raw = true then some (g.extract (g.checked_rank ok)) else none

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction
