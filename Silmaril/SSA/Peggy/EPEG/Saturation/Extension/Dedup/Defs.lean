module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Defs

/-! # Exact RHS reuse for the zero-sample analysis -/

@[expose] public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup

open PEG
open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {site : Fin n} {zero : P [] .count}

/-- Match the entire result sort, loop identity, and ordered operand references. -/
structure RhsAt (found : ZeroSample g site zero) (i : Fin n) : Prop where
  sort_eq : g.sort i = g.sort site
  shape : HEq (g.node i) (Node.ofLabel found.row.label found.row.args)

def evalKey {t : Ty Data} : Node P params (Fin l) g.sort t → Option (Fin l × Fin n × Fin n)
  | ⟨_, .eval loop, .cons initial (.cons count .nil)⟩ => some (loop, initial.id, count.id)
  | _ => none

def checkRhs [DecidableEq Data] (found : ZeroSample g site zero) (i : Fin n) : Bool :=
  decide (g.sort i = g.sort site) &&
    evalKey (g.node i) == some (found.loop, found.initial.id, found.count.id)

/-- Existence of an exact RHS in the redex class. -/
def Covered (found : ZeroSample g site zero) (classes : Classes n) : Prop :=
  ∃ i, RhsAt found i ∧ classes site = classes i

def checkCovered [DecidableEq Data] (found : ZeroSample g site zero) (classes : Classes n) : Bool :=
  (List.finRange n).any fun i => checkRhs found i && classes site == classes i

inductive Choice (n : Nat) where
  | keep
  | reuse (rhs : Fin n)
  | append

/-- Prefer a same-class match anywhere in the table. Otherwise reuse the
first exact RHS in address order, or append when none exists. -/
def choose [DecidableEq Data] (found : ZeroSample g site zero) (classes : Classes n) : Choice n :=
  if checkCovered found classes then .keep
  else
    match (List.finRange n).find? (checkRhs found) with
    | some i => .reuse i
    | none => .append

variable {s : State P params results n l}

def ensure [DecidableEq Data] (found : ZeroSample s.graph site zero) : Output P params results l :=
  match choose found s.classes with
  | .keep => ⟨n, s⟩
  | .reuse i => ⟨n, ⟨s.graph, s.classes.merge site i⟩⟩
  | .append => ⟨n + 1, found.step.apply⟩

variable [DecidableEq Data] [DecidableEq (P [] .count)]

/-- Visit a numeric site in the current table. Appends preserve earlier addresses. -/
def visit (zero : P [] .count) (s : Output P params results l) (address : Nat) :
    Output P params results l :=
  if bound : address < s.1 then
    match ZeroSample.matchAt (g := s.2.graph) ⟨address, bound⟩ zero with
    | some found => ensure found
    | none => s
  else s

def checkDone (zero : P [] .count) (s : Output P params results l) (address : Nat) : Bool :=
  if bound : address < s.1 then
    match ZeroSample.matchAt (g := s.2.graph) ⟨address, bound⟩ zero with
    | some found => checkCovered found s.2.classes
    | none => false
  else false

def checkClosed (zero : P [] .count) (s : Output P params results l) (sites : List Nat) : Bool :=
  sites.all (checkDone zero s)

/-- One visit per supplied occurrence. The driver never adds sites to the list. -/
def close (zero : P [] .count) (s : Output P params results l) (sites : List Nat) :
    Output P params results l :=
  sites.foldl (visit zero) s

/-- Keep the same numeric addresses in addition to the typed embedding laws. -/
def Prefix (source target : Output P params results l) : Prop :=
  ∃ e : Embedding source.2 target.2, ∀ i, (e.vertices.address i).val = i.val

def EligibleAt (zero : P [] .count) (s : Output P params results l) (address : Nat) : Prop :=
  ∃ site, site.val = address ∧ Nonempty (ZeroSample s.2.graph site zero)

def CompleteAt (zero : P [] .count) (s : Output P params results l) (address : Nat) : Prop :=
  ∃ (site : Fin s.1) (found : ZeroSample s.2.graph site zero),
    site.val = address ∧ Covered found s.2.classes

/-- Class validity and native ordered observations for one interpretation and input. -/
def Preserves (m : Interpretation.{u,v,x} P) (env : Tuple m.Value params)
    (source target : Output P params results l) : Prop :=
  ∀ (wf : WellFounded source.2.graph.Demand),
    source.2.classes.Valid (source.2.graph.denote m env wf) →
    ∃ after : WellFounded target.2.graph.Demand,
      target.2.classes.Valid (target.2.graph.denote m env after) ∧
      ∀ i, target.2.graph.observe m (target.2.graph.denote m env after) i =
        source.2.graph.observe m (source.2.graph.denote m env wf) i

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup
