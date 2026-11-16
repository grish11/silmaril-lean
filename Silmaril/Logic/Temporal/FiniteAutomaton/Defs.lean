module

public import Silmaril.Logic.Temporal.Buchi.Automaton.Base.Thms

@[expose] public section
noncomputable section
open Classical
namespace Silmaril.Logic.Temporal.FiniteAutomaton
open ModalMu Buchi.Automaton

/-- Finite symbolic guards at edges and endpoints; no semantic oracle fields. -/
structure Symbolic (Atom : Type) (n : Nat) where
  initial : Set (Fin n)
  guard : Fin n → Fin n → Guard Atom
  terminal : Fin n → Guard Atom

def Symbolic.map {A B : Type} {n : Nat} (F : Symbolic A n) (f : A → B) : Symbolic B n where
  initial := F.initial
  guard q r := (F.guard q r).map f
  terminal q := (F.terminal q).map f

/-- A finite synchronous run. Each edge reads the source label; stopping reads
its endpoint label and is permitted only at a genuine original-frame deadlock. -/
inductive RunFrom {Atom W : Type} {n : Nat} (F : Symbolic Atom n)
    (R : W → W → Prop) (label : W → Atom → Prop) : W → Fin n → Prop
  | terminal {w q} : (F.terminal q).Holds (label w) → (∀ v, ¬ R w v) → RunFrom F R label w q
  | step {w q v r} : (F.guard q r).Holds (label w) → R w v →
      RunFrom F R label v r → RunFrom F R label w q

/-- One bounded path and one bounded run, sharing every position. The length
counts edges; zero includes the initial world as the terminal letter. -/
def PathRunFrom {Atom W : Type} {n : Nat} (F : Symbolic Atom n)
    (R : W → W → Prop) (label : W → Atom → Prop) (w : W) (q : Fin n) : Prop :=
  ∃ length : Nat, ∃ path : Nat → W, ∃ run : Nat → Fin n,
    path 0 = w ∧ run 0 = q ∧
    (∀ i, i < length → R (path i) (path (i+1)) ∧
      (F.guard (run i) (run (i+1))).Holds (label (path i))) ∧
    (F.terminal (run length)).Holds (label (path length)) ∧
    ∀ v, ¬ R (path length) v

def AcceptsPath {Atom W : Type} {n : Nat} (F : Symbolic Atom n)
    (R : W → W → Prop) (label : W → Atom → Prop) (w : W) : Prop :=
  ∃ q ∈ F.initial, PathRunFrom F R label w q

/-- Endpoint-or-step equations on original worlds. A terminal guard consumes
its final letter without an additional graph or automaton transition. -/
def system {S : Signature} {n : Nat} (F : Symbolic S.Atom n) (a : S.Action) :
    FiniteVector.System S n 0 where
  body q := .disj (.conj (F.terminal q).toFormula (.box a .bot))
    (Buchi.Automaton.Base.disjoin (fun r =>
      .conj (F.guard q r).toFormula (.diamond a (.var (Fin.castAdd 0 r)))))

def coordinate {S : Signature} {n : Nat} (F : Symbolic S.Atom n) (a : S.Action)
    (q : Fin n) : Formula S 0 := (system F a).compile false q

def formula {S : Signature} {n : Nat} (F : Symbolic S.Atom n) (a : S.Action) : Formula S 0 :=
  Buchi.Automaton.Base.disjoin (fun q => if q ∈ F.initial then coordinate F a q else .bot)

end Silmaril.Logic.Temporal.FiniteAutomaton
