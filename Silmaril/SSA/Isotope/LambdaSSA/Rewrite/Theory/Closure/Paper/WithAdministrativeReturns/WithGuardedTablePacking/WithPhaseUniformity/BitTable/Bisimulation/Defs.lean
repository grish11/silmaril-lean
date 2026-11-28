module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Quotient.Defs

/-! # Streams, disjoint unions and trails of request tables

A table is deterministic: each state has one row program and one
successor. Entered at state `i` it runs the programs
`t.stream i 0, t.stream i 1, …` until one returns.

`Table.append t s` is the disjoint union with the states of `t` in front
and those of `s` at the tail. `Table.minimized` identifies states with
equal streams by sending every successor to a chosen representative.

`Table.canonical` replaces each row by a chosen program with the same
reflected tree key.

`Table.Trail` describes the request words of complete runs of a table of
polls, and `Table.runWord` is the word of the run that repeats `n` times
and then returns.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery (signature Event)
open _root_.Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.BitQuery.RequestTree (event Word)

/-! ## States in front of a table -/

variable {K : Nat}

/-- State `j` of the tail after `P + 1` states were put in front. -/
def tailIdx : (P : Nat) → Fin (K + 1) → Fin (K + (P + 1) + 1)
  | 0, j => j.succ
  | P + 1, j => (tailIdx P j).succ

/-- Front state `i`. -/
def frontIdx : (P : Nat) → Fin (P + 1) → Fin (K + (P + 1) + 1)
  | 0, _ => 0
  | P + 1, i => Fin.cases 0 (fun i => (frontIdx P i).succ) i

/-- Case analysis on front and tail states. -/
def joinIdx {α : Type} : (P : Nat) → (Fin (P + 1) → α) → (Fin (K + 1) → α) → Fin (K + (P + 1) + 1) → α
  | 0, a, b => Fin.cases (a 0) b
  | P + 1, a, b => Fin.cases (a 0) (joinIdx P (fun i => a i.succ) b)

/-- The constructor term of the tail embedding. -/
def tailTm : Nat → Tm signature.Instr → Tm signature.Instr
  | 0, a => .inr a
  | P + 1, a => .inr (tailTm P a)

theorem tailTm_typed {Γ : VCtx (Ty Empty)} {a : Tm signature.Instr} (ha : Tm.BranchValue Γ a (States K)) :
    ∀ P : Nat, Tm.BranchValue Γ (tailTm P a) (States (K + (P + 1)))
  | 0 => .inr ha
  | P + 1 => .inr (tailTm_typed ha P)

theorem tail_typed (K P : Nat) :
    ValueBranches [States K] (.br 0 (tailTm P (.var 0)) : Region signature.Instr) [States (K + (P + 1))] :=
  .br rfl (tailTm_typed (.var rfl) P)

/-- The disjoint union: the states of `t` in front, those of `s` at the tail. -/
def Table.append {P : Nat} (t : Table P) (s : Table K) : Table (K + (P + 1)) where
  prog := joinIdx P t.prog s.prog
  next := joinIdx P (fun i => frontIdx P (t.next i)) (fun j => tailIdx P (s.next j))

/-! ## Streams -/

/-- The program run in round `n` after entering at state `i`. -/
def Table.stream (t : Table K) (i : Fin (K + 1)) (n : Nat) : Program := t.prog (t.next^[n] i)

/-- States with equal streams. -/
def Table.streamSetoid (t : Table K) : Setoid (Fin (K + 1)) where
  r x y := ∀ n, t.stream x n = t.stream y n
  iseqv := ⟨fun _ _ => rfl, fun h n => (h n).symm, fun h h' n => (h n).trans (h' n)⟩

/-- A chosen state with the same stream. States with equal streams get
the same one. -/
noncomputable def Table.rep (t : Table K) (x : Fin (K + 1)) : Fin (K + 1) :=
  (Quotient.mk t.streamSetoid x).out

/-- The same rows, with every successor replaced by its representative. -/
noncomputable def Table.minimized (t : Table K) : Table K := ⟨t.prog, fun x => t.rep (t.next x)⟩

/-! ## Row keys -/

/-- Programs with the same reflected tree key. -/
def keySetoid : Setoid Program where
  r p q := p.tree.key = q.tree.key
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- A chosen program with the same key. Programs with equal keys get the
same one. -/
noncomputable def canonProgram (p : Program) : Program := (Quotient.mk keySetoid p).out

/-- The same wiring, with every row replaced by its chosen program. -/
noncomputable def Table.canonical (t : Table K) : Table K := ⟨fun i => canonProgram (t.prog i), t.next⟩

/-- A table whose rows are written polls. -/
def Table.ofPolls (poll : Fin (K + 1) → Poll) (next : Fin (K + 1) → Fin (K + 1)) : Table K :=
  ⟨fun i => (poll i).program, next⟩

/-! ## Request words of a table of polls -/

/-- The request word of a complete run from state `i`: one event per
round, carrying that round's label. The last event has the returning
reply tag of its poll and every earlier one the repeating tag. -/
def Table.Trail (poll : Fin (K + 1) → Poll) (next : Fin (K + 1) → Fin (K + 1)) :
    Fin (K + 1) → List Event → Prop
  | _, [] => False
  | i, e :: w => e.label = (poll i).label ∧
      ((e.right = (poll i).returnRight ∧ w = []) ∨
        (e.right = !(poll i).returnRight ∧ Table.Trail poll next (next i) w))

/-- The word of the run that repeats `n` times and then returns, with
every reply payload `false`. -/
def Table.runWord (poll : Fin (K + 1) → Poll) (next : Fin (K + 1) → Fin (K + 1)) :
    Nat → Fin (K + 1) → Bool → Word
  | 0, i, g => FreeMonoid.of (event (poll i).label g ((poll i).returnRight, false))
  | n + 1, i, g => FreeMonoid.of (event (poll i).label g (!(poll i).returnRight, false)) *
      Table.runWord poll next n (next i) false

/-! ## Regression tables -/

/-- Four states in a ring `a b a b`. -/
def ringNext (i : Fin 4) : Fin 4 :=
  match i with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 0

def ringPolls (a b : Poll) (i : Fin 4) : Poll :=
  match i with
  | 0 => a
  | 1 => b
  | 2 => a
  | 3 => b

/-- A transient state, a two-state cycle and an unreachable state that
points into them: `a → b ⇄ d`, and `c → a`. -/
def lassoNext (i : Fin 4) : Fin 4 :=
  match i with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | 3 => 0

def lassoPolls (a b c d : Poll) (i : Fin 4) : Poll :=
  match i with
  | 0 => a
  | 1 => b
  | 2 => d
  | 3 => c

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
