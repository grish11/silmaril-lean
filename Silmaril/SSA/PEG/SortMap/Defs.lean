module

public import Silmaril.SSA.PEG.Semantics.Defs

/-! # Transport of typed PEGs along a map of data sorts -/

@[expose] public section

namespace Silmaril.SSA.PEG

open RVSDG (Port Tuple)

universe u u' u'' v v' v'' w

variable {D : Type u} {E : Type u'} {F : Type u''}

/-- The structural control and iteration sorts retain their identities. -/
def Ty.mapData (f : D → E) : Ty D → Ty E
  | .bool => .bool
  | .count => .count
  | .data d => .data (f d)

abbrev Ty.mapProfile (f : D → E) (ts : List (Ty D)) := ts.map (Ty.mapData f)

variable {P : InstructionSet.{u,v} D} {Q : InstructionSet.{u',v'} E}
variable {R : InstructionSet.{u'',v''} F}

/-- An opcode map over a prescribed function on data sorts. -/
abbrev ProfileMap (f : D → E) (P : InstructionSet.{u,v} D) (Q : InstructionSet.{u',v'} E) :=
  ∀ {ins out}, P ins out → Q (Ty.mapProfile f ins) (out.mapData f)

@[simp] theorem Ty.mapData_id (t : Ty D) : t.mapData id = t := by cases t <;> rfl

@[simp] theorem Ty.mapData_comp (f : D → E) (g : E → F) (t : Ty D) :
    (t.mapData f).mapData g = t.mapData (g ∘ f) := by cases t <;> rfl

@[simp] theorem Ty.mapProfile_id (ts : List (Ty D)) : Ty.mapProfile id ts = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [Ty.mapProfile, List.map_cons, Ty.mapData_id, ih]

theorem Ty.mapProfile_comp (f : D → E) (g : E → F) (ts : List (Ty D)) :
    Ty.mapProfile g (Ty.mapProfile f ts) = Ty.mapProfile (g ∘ f) ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact congrArg₂ List.cons (Ty.mapData_comp f g t) ih

def ProfileMap.fixed {Q : InstructionSet.{u,v'} D} (op : InstructionMap P Q) :
    ProfileMap id P Q := fun {ins out} instr =>
  cast (congrArg₂ (fun a b => Q a b) (Ty.mapProfile_id ins).symm (Ty.mapData_id out).symm) (op instr)

def ProfileMap.comp {f : D → E} {g : E → F} (p : ProfileMap f P Q) (q : ProfileMap g Q R) :
    ProfileMap (g ∘ f) P R := fun {ins out} instr =>
  cast (congrArg₂ (fun a b => R a b) (Ty.mapProfile_comp f g ins) (Ty.mapData_comp f g out)) (q (p instr))

variable {f : D → E} {n l : Nat} {L : Type}
variable {params ins results : List (Ty D)} {out : Ty D} {sort : Fin n → Ty D}

/-- Translate by position, even when distinct sorts have the same image. -/
def mapDataPort (f : D → E) : {params : List (Ty D)} → Port params out → Port (Ty.mapProfile f params) (out.mapData f)
  | _, .head => .head
  | _, .tail p => .tail (mapDataPort f p)

def mapDataTuple {A : Ty D → Type v} {B : Ty E → Type v'} (f : D → E)
    (each : ∀ t, A t → B (t.mapData f)) :
    {ts : List (Ty D)} → Tuple A ts → Tuple B (Ty.mapProfile f ts)
  | _, .nil => .nil
  | _, .cons head tail => .cons (each _ head) (mapDataTuple f each tail)

def Ref.mapData (f : D → E) (r : Ref sort out) : Ref (Ty.mapData f ∘ sort) (out.mapData f) :=
  ⟨r.id, congrArg (Ty.mapData f) r.typed⟩

def Label.mapData (op : ProfileMap f P Q) : Label P params L ins out →
    Label Q (Ty.mapProfile f params) L (Ty.mapProfile f ins) (out.mapData f)
  | .param p => .param (mapDataPort f p)
  | .op instr => .op (op instr)
  | .phi => .phi
  | .theta key => .theta key
  | .eval key => .eval key
  | .pass key => .pass key

def Node.mapData (op : ProfileMap f P Q) (row : Node P params L sort out) :
    Node Q (Ty.mapProfile f params) L (Ty.mapData f ∘ sort) (out.mapData f) :=
  ⟨Ty.mapProfile f row.inputs, row.label.mapData op, mapDataTuple f (fun _ => Ref.mapData f) row.args⟩

/-- Retain every vertex, loop key and ordered operand/root occurrence. -/
def Graph.mapData (op : ProfileMap f P Q) (g : Graph P params results n l) :
    Graph Q (Ty.mapProfile f params) (Ty.mapProfile f results) n l :=
  ⟨g.forest, Ty.mapData f ∘ g.sort, fun i => (g.node i).mapData op,
    mapDataTuple f (fun _ => Ref.mapData f) g.roots⟩

def Ty.valueMapEquiv (f : D → E) (carrier : E → Type w) (t : Ty D) :
    t.Value (carrier ∘ f) ≃ (t.mapData f).Value carrier := by
  cases t <;> exact Equiv.refl _

/-- Transport values in the reverse direction along the same positions. -/
def unmapDataTuple {A : Ty D → Type v} {B : Ty E → Type v'} (f : D → E)
    (each : ∀ t, B (t.mapData f) → A t) :
    (ts : List (Ty D)) → Tuple B (Ty.mapProfile f ts) → Tuple A ts
  | [], .nil => .nil
  | _ :: ts, .cons head tail => .cons (each _ head) (unmapDataTuple f each ts tail)

/-- Transport of a typed tuple is invertible position by position. It requires
equivalences of the corresponding carriers, even when the sort map identifies sorts. -/
def mapDataTupleEquiv {A : Ty D → Type v} {B : Ty E → Type v'} (f : D → E)
    (each : ∀ t, A t ≃ B (t.mapData f)) (ts : List (Ty D)) :
    Tuple A ts ≃ Tuple B (Ty.mapProfile f ts) where
  toFun := mapDataTuple f (fun t => each t)
  invFun := unmapDataTuple f (fun t => (each t).symm) ts
  left_inv values := by
    induction values with
    | nil => rfl
    | cons x xs ih => exact congrArg₂ Tuple.cons ((each _).symm_apply_apply x) ih
  right_inv values := by
    induction ts with
    | nil => cases values; rfl
    | cons t ts ih =>
      cases values with
      | cons x xs => exact congrArg₂ Tuple.cons ((each t).apply_symm_apply x) (ih xs)

/-- A target interpretation restricts its data carriers along the sort function. -/
def Interpretation.reductData (op : ProfileMap f P Q) (m : Interpretation.{u',v',w} Q) :
    Interpretation.{u,v,w} P where
  carrier := m.carrier ∘ f
  run instr args := (m.run (op instr)
    (mapDataTuple f (Ty.valueMapEquiv f m.carrier ·) args)).map
      (Ty.valueMapEquiv f m.carrier _).symm

/-- Translate every entry of a valuation at the unchanged request. -/
def Graph.mapDataValuation (g : Graph P params results n l) (op : ProfileMap f P Q)
    (m : Interpretation.{u',v',w} Q) (v : g.Valuation (m.reductData op)) :
    (g.mapData op).Valuation m :=
  fun q => (v q).map (Ty.valueMapEquiv f m.carrier (g.sort q.1))

end Silmaril.SSA.PEG
