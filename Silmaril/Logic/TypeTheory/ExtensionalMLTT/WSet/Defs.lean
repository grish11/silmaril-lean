module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.SetUniverse
public import Mathlib.Data.W.Basic

@[expose] public section

/-!
# Set codes for well-founded trees

A tree is represented by its labels at finite paths. Branch positions are
marked with their source shape, so observation is defined even for paths
which do not follow that tree. Codes are subsets of one set of path-label
pairs. This bounds the set of *all* coded trees, including infinitely
branching well-founded trees, without a finite-depth assumption.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

universe u v w

namespace PathCode

/-- A finite path is a list encoded with empty nil and Kuratowski-pair cons. -/
def encode {α : Type v} (e : α → ZFSet.{u}) : List α → ZFSet.{u}
  | [] => ∅
  | a :: xs => ZFSet.pair (e a) (encode e xs)

/-- Sets containing all list codes of depth at most the given natural number. -/
def stage (D : ZFSet.{u}) : ℕ → ZFSet.{u}
  | 0 => {∅}
  | n + 1 => insert ∅ (ZFSet.prod D (stage D n))

noncomputable section

/-- Read the natural number represented by an element of omega. -/
def omegaIndex (n : (ZFSet.omega : ZFSet.{u})) : ℕ :=
  Classical.choose (Silmaril.Logic.SetTheory.mem_omega_iff.mp n.property)

/-- The set of finite list codes with entries in `D`. -/
def lists (D : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.iUnion fun n : (ZFSet.omega : ZFSet.{u}) => stage D (omegaIndex n)

end
end PathCode

namespace WSet

open Classical

/-- All branch positions, tagged by the shape that owns them. -/
abbrev Branch {α : Type v} (β : α → Type w) := Σ a, β a

/-- Observe a tree along a finite sequence of tagged branch positions. -/
noncomputable def observe {α : Type v} {β : α → Type w} :
    WType β → List (Branch β) → Option α
  | .mk a _, [] => some a
  | .mk a f, ⟨a', b⟩ :: xs =>
    if h : a' = a then observe (f (h ▸ b)) xs else none

/-- The ordinary W-type over a set of labels and a set-valued branch family. -/
abbrev Tree (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) := WType (fun a : A => B a.val)

/-- Encode a tagged branch as an ordinary ordered pair of sets. -/
def branchCode {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (b : Branch (fun a : A => B a.val)) : ZFSet.{u} :=
  ZFSet.pair b.1.val b.2.val

/-- A common set containing every possible finite-path and node-label pair. -/
noncomputable def observationBound (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (PathCode.lists (SetSem.sigma A B)) A

/-- The exact observations of a tree, separated from the common observation bound. -/
noncomputable def encode {A : ZFSet.{u}} {B : ZFSet.{u} → ZFSet.{u}}
    (t : Tree A B) : ZFSet.{u} :=
  (observationBound A B).sep fun z =>
    ∃ xs a, observe t xs = some a ∧ ZFSet.pair (PathCode.encode branchCode xs) a.val = z

/-- The whole set of codes of well-founded trees, with no rank or finite-branching restriction. -/
noncomputable def carrier (A : ZFSet.{u}) (B : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.powerset (observationBound A B)).sep fun z => ∃ t : Tree A B, encode t = z

end WSet
end Silmaril.Logic.TypeTheory.ExtensionalMLTT
