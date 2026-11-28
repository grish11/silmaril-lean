module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Defs
public import Silmaril.SSA.Isotope.LetCase.Categorical.Defs

/-! # Ranked positional blocks with an ambient context -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture

open Silmaril.SSA.RVSDG.LambdaSSA.LinearChain (localSite)
open Morphism.CaseSSA (erase erase_hasType)

universe u v

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

/-- A typed target in the local prefix or the external suffix of the native
label context. An exit keeps its original outward position. -/
inductive Target {k : Nat} (R : Fin k → τ) (L : LCtx τ) : τ → Type u where
  | local (i : Fin k) : Target R L (R i)
  | exit {i : Nat} {A : τ} : At L i A → Target R L A

variable {k : Nat} {R : Fin k → τ} {L : LCtx τ} {A : τ}

def Target.index : Target R L A → Nat
  | .local i => i.val
  | .exit (i := i) _ => k + i

omit [TypeFormers τ] in
theorem Target.typing (t : Target R L A) : At (List.ofFn R ++ L) t.index A := by
  cases t with
  | «local» i => exact (localSite R L i).typing
  | @exit i A h =>
    change (List.ofFn R ++ L)[k + i]? = some A
    rw [List.getElem?_append_right (by simp)]
    simpa [At] using h

def Target.locals : Target R L A → List (Fin k)
  | .local i => [i]
  | .exit _ => []

/-- A block reads the shared ambient context and its newest incoming payload.
It can compute a jump argument or compute a sum selecting two typed targets. -/
inductive Block (Φ : Type v) [HasTy Φ τ] {d : Nat} (β : BoundCtx τ d)
    {k : Nat} (R : Fin k → τ) (L : LCtx τ) (A : τ) : Type (max u v) where
  | jump {B : τ} : Operand Φ (β.snoc A) B → Target R L B → Block Φ β R L A
  | case {B D : τ} : Operand Φ (β.snoc A) (coprod B D) →
      Target R L B → Target R L D → Block Φ β R L A

variable {d : Nat} {β : BoundCtx τ d}

def Block.locals : Block Φ β R L A → List (Fin k)
  | .jump _ t => t.locals
  | .case _ l r => l.locals ++ r.locals

def Block.toSSA : Block Φ β R L A → Region Φ
  | .jump a t => .br t.index (erase a.1)
  | .case a l r => .case (erase a.1) (.br l.index (.var 0)) (.br r.index (.var 0))

theorem Block.toSSA_hasType (b : Block Φ β R L A) :
    Region.HasType (β.snoc A).toList b.toSSA (List.ofFn R ++ L) :=
  match b with
  | .jump a t => .br t.typing (erase_hasType a.2.toHasType)
  | .case a l r => .case (erase_hasType a.2.toHasType)
      (.br l.typing (.var rfl)) (.br r.typing (.var rfl))

/-- A nonempty native CFG with a shared ambient context. Any local label can
be chosen as the entry. -/
structure Table (Φ : Type v) [HasTy Φ τ] {d : Nat} (β : BoundCtx τ d)
    (L : LCtx τ) (n : Nat) where
  types : Fin (n + 1) → τ
  block : ∀ i, Block Φ β types L (types i)

variable {n : Nat}

def Table.localTargets (p : Table Φ β L n) (i : Fin (n + 1)) : List (Fin (n + 1)) :=
  (p.block i).locals

/-- Reuse the finite global checker on the local edges. -/
def Table.check (p : Table Φ β L n) : Bool :=
  Rank.check p.localTargets

def Table.rank (p : Table Φ β L n) (i : Fin (n + 1)) : Nat :=
  ((Rank.rounds p.localTargets (n + 1)).get i).getD 0

theorem Table.decreases (p : Table Φ β L n) (ok : p.check = true)
    {i j : Fin (n + 1)} (edge : j ∈ p.localTargets i) : p.rank j < p.rank i :=
  Rank.check_sound p.localTargets ok edge

def Table.entry (p : Table Φ β L n) (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    Region Φ :=
  .br i (erase a.1)

theorem Table.entry_hasType (p : Table Φ β L n) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) : Region.HasType β.toList (p.entry i a) (List.ofFn p.types ++ L) :=
  .br (localSite p.types L i).typing (erase_hasType a.2.toHasType)

def Table.toSSA (p : Table Φ β L n) (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) : Region Φ :=
  .cfg (p.entry i a) (n + 1) (fun j => (p.block j).toSSA)

theorem Table.toSSA_hasType (p : Table Φ β L n) (i : Fin (n + 1)) (a : Operand Φ β (p.types i)) :
    Region.HasType β.toList (p.toSSA i a) L :=
  .cfg p.types (p.entry_hasType i a) (fun j => (p.block j).toSSA_hasType)

/-- The ambient variables are the older part of the current context. New binders
introduced by compilation are skipped, apart from the current packet. -/
inductive Scope (β : BoundCtx τ d) : {m : Nat} → BoundCtx τ m → Type u where
  | base : Scope β β
  | skip {m : Nat} {γ : BoundCtx τ m} (s : Scope β γ) (A : τ) : Scope β (γ.snoc A)

variable {m : Nat} {γ : BoundCtx τ m}

def Scope.indices : {m : Nat} → {γ : BoundCtx τ m} → Scope β γ → Nat → Nat
  | _, _, .base => id
  | _, _, .skip s _ => fun i => (s.indices i).succ

def Scope.renaming : {m : Nat} → {γ : BoundCtx τ m} → Scope β γ → BoundCtx.Renaming β γ
  | _, _, .base => .id β
  | _, _, .skip s A => s.renaming.comp (.succ _ A)

def Scope.operand (s : Scope β γ) {A B : τ} (a : Operand Φ (β.snoc A) B) :
    Operand Φ (γ.snoc A) B :=
  ⟨_, a.2.rename (s.renaming.up A)⟩

/-- The compiler calls local continuations under a context extended with the
old packet. An outward target returns the newest value at its original index. -/
abbrev LocalContinuations (β : BoundCtx τ d) (R : Fin k → τ) (L : LCtx τ)
    (Φ : Type v) [HasTy Φ τ] (targets : List (Fin k)) :=
  ∀ (j : Fin k), j ∈ targets → ∀ {m : Nat} {γ : BoundCtx τ m}, Scope β γ →
    FiniteExit Φ L (γ.snoc (R j))

def Target.compile (t : Target R L A) {labels : List (Fin k)} (edge : ∀ j ∈ t.locals, j ∈ labels)
    (scope : Scope β γ) (next : LocalContinuations β R L Φ labels) : FiniteExit Φ L (γ.snoc A) :=
  match t with
  | .local i => next i (edge i (by simp [Target.locals])) scope
  | .exit h => .br h ⟨.bv 0, .bv⟩

def Block.compile (b : Block Φ β R L A) (scope : Scope β γ)
    (next : LocalContinuations β R L Φ b.locals) : FiniteExit Φ L (γ.snoc A) :=
  match b with
  | .jump a t =>
    .join (.br (scope.operand a)) (t.compile (fun _ h => h) (.skip scope A) next)
  | .case a l r =>
    .case (scope.operand a)
      (l.compile (fun _ h => List.mem_append_left _ h) (.skip scope A) next)
      (r.compile (fun _ h => List.mem_append_right _ h) (.skip scope A) next)

/-- Unfold by the checked local rank, threading the scope of the shared ambient context. -/
def Table.compileAt (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    {m : Nat} {γ : BoundCtx τ m} (scope : Scope β γ) : FiniteExit Φ L (γ.snoc (p.types i)) :=
  (p.block i).compile scope (fun j _ _ _ s => p.compileAt ok j s)
termination_by p.rank i
decreasing_by exact p.decreases ok ‹j ∈ _›

def Table.toFiniteExit (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) : FiniteExit Φ L β :=
  .join (.br a) (p.compileAt ok i .base)

def Table.toLetCase (p : Table Φ β L n) (ok : p.check = true) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) : Operand Φ β (Region.packedExitType L) :=
  (p.toFiniteExit ok i a).encode.toLetCase

/-- Compile a checked captured table to exact LetCase at the original ambient context. -/
def Table.toLetCase? (p : Table Φ β L n) (i : Fin (n + 1))
    (a : Operand Φ β (p.types i)) : Option (Operand Φ β (Region.packedExitType L)) :=
  if h : p.check = true then some (p.toLetCase h i a) else none

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture
