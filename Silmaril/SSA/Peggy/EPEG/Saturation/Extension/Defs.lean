module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Defs

/-! # Append-only transitions for guarded E-PEG saturation -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension

open PEG
open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}

/-- The appended row can refer only to vertices already in the table. -/
structure Row (g : Graph P params results n l) where
  inputs : List (Ty Data)
  out : Ty Data
  label : Label P params (Fin l) inputs out
  args : Tuple (Ref g.sort) inputs

namespace Row

variable {g : Graph P params results n l}

def sort (row : Row g) : Fin (n + 1) → Ty Data :=
  Fin.lastCases row.out g.sort

@[simp] theorem sort_old (row : Row g) (i : Fin n) : row.sort i.castSucc = g.sort i :=
  Fin.lastCases_castSucc i

@[simp] theorem sort_fresh (row : Row g) : row.sort (Fin.last n) = row.out :=
  Fin.lastCases_last

def liftRef (row : Row g) {t : Ty Data} (r : Ref g.sort t) : Ref row.sort t :=
  ⟨r.id.castSucc, (row.sort_old r.id).trans r.typed⟩

def fresh (row : Row g) : Ref row.sort row.out :=
  ⟨Fin.last n, row.sort_fresh⟩

def liftNode (row : Row g) {t : Ty Data} (node : Node P params (Fin l) g.sort t) :
    Node P params (Fin l) row.sort t :=
  Node.ofLabel node.label (node.args.map fun _ => row.liftRef)

/-- Preserve numeric addresses, ordered roots, and the loop frame. -/
def append (row : Row g) : Graph P params results (n + 1) l where
  forest := g.forest
  sort := row.sort
  node := Fin.lastCases
    (row.sort_fresh.symm ▸ Node.ofLabel row.label (row.args.map fun _ => row.liftRef))
    (fun i => (row.sort_old i).symm ▸ row.liftNode (g.node i))
  roots := g.roots.map fun _ => row.liftRef

/-- Old same-class pairs are retained. The new row initially forms a singleton. -/
def liftClasses (classes : Classes n) : Classes (n + 1) :=
  Fin.lastCases (Fin.last n) (fun i => (classes i).castSucc)

end Row

structure State (P : InstructionSet.{u,v} Data) (params results : List (Ty Data)) (n l : Nat) where
  graph : Graph P params results n l
  classes : Classes n

variable {s : State P params results n l}

/-- The finite obligations are checked on the extended table. Their semantic
contracts are separate from the executable receipt. -/
structure Step (s : State P params results n l) where
  row : Row s.graph
  obligations : List (Obligation row.append)
  fuel : Nat

def Step.apply (step : Step s) : State P params results (n + 1) l :=
  ⟨step.row.append, Saturation.run step.fuel step.obligations (Row.liftClasses s.classes)⟩

/-- A typed sequence of generation choices. Later steps can refer to
earlier appended rows and can use their class equalities. -/
inductive Plan : {n : Nat} → State P params results n l → Type (max u v) where
  | stop {n : Nat} {s : State P params results n l} : Plan s
  | next {n : Nat} {s : State P params results n l} (step : Step s) (rest : Plan step.apply) : Plan s

abbrev Output (P : InstructionSet.{u,v} Data) (params results : List (Ty Data)) (l : Nat) :=
  (n : Nat) × State P params results n l

/-- Replay at most the given number of append steps. Every step also has
its own merge fuel. Zero fuel returns the current state. -/
def Plan.run : {n : Nat} → {s : State P params results n l} →
    Nat → Plan s → Output P params results l
  | n, s, 0, _ | n, s, _, .stop => ⟨n, s⟩
  | _, _, fuel + 1, .next _ rest => rest.run fuel

/-- The same numeric address remains available at every replay prefix. -/
def Plan.liftRef {t : Ty Data} : {n : Nat} → {s : State P params results n l} →
    (fuel : Nat) → (plan : Plan s) → Ref s.graph.sort t → Ref (plan.run fuel).2.graph.sort t
  | _, _, 0, _, ref | _, _, _ + 1, .stop, ref => ref
  | _, _, fuel + 1, .next step rest, ref => rest.liftRef fuel (step.row.liftRef ref)

variable {m : Interpretation.{u,v,x} P}

/-- Semantic justification for the receipts, in the specified model and input. -/
def Step.Holds (step : Step s) (env : Tuple m.Value params) : Prop :=
  ∀ values, step.row.append.Solves m env values → ∀ o ∈ step.obligations, o.Holds values

/-- Only the prefix actually replayed needs semantic justification. -/
def Plan.Holds (env : Tuple m.Value params) : {n : Nat} → {s : State P params results n l} →
    Nat → Plan s → Prop
  | _, _, 0, _ | _, _, _ + 1, .stop => True
  | _, _, fuel + 1, .next step rest => step.Holds env ∧ rest.Holds env fuel

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension
