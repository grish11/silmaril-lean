module

public import Silmaril.SSA.Peggy.Bridge.IR.Defs
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Relabel.Thms
public import Silmaril.SSA.PEG.Bridge.Theta.Region.Tuple.Thms

/-! # The checked single-loop equation family over signatures with negation -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Theta

open CategoryTheory
open Dialect (FixedSortSignature)
open PEG (Graph Index)
open PEG.Bridge (TotalModel ValuePort valuePorts)
open PEG.Bridge.Theta.Region (Opcode encode)
open PEG.Bridge.Theta.Region.Ordered (Bundle)
open RVSDG (Port Tuple)
open RVSDG.Theta.Institution (relabel)

variable {Data : Type}

/-- The exit primitive is marked at the unary Boolean profile. Arrows are
ordinary fixed-sort Peggy opcode maps preserving this mark. -/
structure Signature (Data : Type) where
  dialect : FixedSortSignature.{0,0} Data
  negation : dialect.ops [.bool] .bool

instance : Category.{0} (Signature Data) where
  Hom S T := {f : S.dialect ⟶ T.dialect // FixedSortSignature.opcodeMap f S.negation = T.negation}
  id _ := ⟨𝟙 _, rfl⟩
  comp f g := ⟨f.val ≫ g.val,
    (congrArg (FixedSortSignature.opcodeMap g.val) f.property).trans g.property⟩
  id_comp _ := Subtype.ext rfl
  comp_id _ := Subtype.ext rfl
  assoc _ _ _ := Subtype.ext rfl

variable {S T : Signature Data}

/-- Use the underlying Peggy opcode map at the unchanged profile. -/
abbrev opMap (f : S ⟶ T) : PEG.InstructionMap S.dialect.ops T.dialect.ops :=
  FixedSortSignature.opcodeMap f.val

/-- Real numbered θ signatures. The compiler's adapter for Boolean branch
tags is structural and is fixed by every arrow. -/
def thetaSignature (Data : Type) :
    Signature Data ⥤ RVSDG.Institution.Signature (PEG.Ty Data) PUnit where
  obj S := ⟨Opcode S.dialect.ops⟩
  map f := ⟨PEG.Bridge.Theta.Region.Relabel.opcode (opMap f)⟩
  map_id _ := by
    apply congrArg RVSDG.Institution.Signature.Hom.mk
    funext _ _ op
    cases op <;> rfl
  map_comp _ _ := by
    apply congrArg RVSDG.Institution.Signature.Hom.mk
    funext _ _ op
    cases op <;> rfl

/-- The pinned Boolean carrier and the marked negation law are part of
the restricted model presentation. -/
def Model (S : Signature Data) :=
  {m : TotalModel S.dialect.ops // ∀ b : Bool, m.run S.negation (.cons ⟨b⟩ .nil) = ⟨!b⟩}

abbrev thetaModel (m : Model S) : RVSDG.Model (Opcode S.dialect.ops) :=
  PEG.Bridge.Theta.Region.model m.val

def reduct (f : S ⟶ T) (m : Model T) : Model S :=
  ⟨IR.reduct f.val m.val, fun b =>
    (congrArg (fun (op : T.dialect.ops [.bool] .bool) => m.val.run op (.cons ⟨b⟩ .nil)) f.property).trans (m.property b)⟩

abbrev Lowered (S : Signature Data) (carried : List (PEG.Ty Data)) :=
  Σ sigs, RVSDG.Theta.Graph (Opcode S.dialect.ops) (valuePorts carried) sigs

variable {carried : List (PEG.Ty Data)} {n : Nat} {t : PEG.Ty Data} {g : Graph S.dialect.ops carried carried n 1}
variable {slot : Port carried t} {invariants : Bool}

def bundleCode (b : Bundle g slot invariants) : Lowered S carried :=
  ⟨(PEG.Bridge.Theta.Region.Compiler.body b.scalar).1, b.compile⟩

structure SideData (S : Signature Data) (carried : List (PEG.Ty Data)) where
  nodes : Nat
  peg : Graph S.dialect.ops carried carried nodes 1
  code : Lowered S carried

/-- A checked side retains its chosen numbering and schedule image.
Proof-irrelevant admission allows several legal schedules for a PEG
without making sentence translation depend on a choice of witness. -/
def Side (S : Signature Data) (carried : List (PEG.Ty Data)) :=
  {side : SideData S carried //
    ∃ (t : PEG.Ty Data) (slot : Port carried t) (invariants : Bool)
      (b : Bundle side.peg slot invariants),
      b.scalar.descriptor.negate = S.negation ∧ bundleCode (S := S) b = side.code}

def Side.ofBundle (b : Bundle g slot invariants) (negation : b.scalar.descriptor.negate = S.negation) :
    Side S carried :=
  ⟨⟨n, g, bundleCode (S := S) b⟩, ⟨t, slot, invariants, b, negation, rfl⟩⟩

theorem Side.wf (s : Side S carried) : WellFounded s.val.peg.Demand := by
  obtain ⟨_, _, _, bundle, _, _⟩ := s.property
  exact bundle.demandWellFounded

def mapCode (f : S ⟶ T) (code : Lowered S carried) : Lowered T carried :=
  ⟨code.1, relabel (PEG.Bridge.Theta.Region.Relabel.opcode (opMap f)) code.2⟩

def Side.map (f : S ⟶ T) (s : Side S carried) : Side T carried := by
  refine ⟨⟨s.val.nodes, PEG.Bridge.Theta.Region.Relabel.table (opMap f) s.val.peg, mapCode f s.val.code⟩, ?_⟩
  obtain ⟨t, p, invariant, b, neg, code⟩ := s.property
  refine ⟨t, p, invariant, PEG.Bridge.Theta.Region.Relabel.bundle (opMap f) b, ?_, ?_⟩
  · exact (congrArg (opMap f) neg).trans f.property
  · exact (PEG.Bridge.Theta.Region.Relabel.compile_map (opMap f) b.scalar).trans (congrArg (mapCode f) code)

structure Equation (S : Signature Data) where
  carried : List (PEG.Ty Data)
  lhs : Side S carried
  rhs : Side S carried

def Equation.map (f : S ⟶ T) (e : Equation S) : Equation T :=
  ⟨e.carried, e.lhs.map f, e.rhs.map f⟩

def Equation.translate (e : Equation S) : RVSDG.Theta.Institution.Equation (Opcode S.dialect.ops) :=
  ⟨valuePorts e.carried, e.lhs.val.code.1, e.rhs.val.code.1, e.lhs.val.code.2, e.rhs.val.code.2⟩

/-- Compare only defined ordered observations. A nonreturn supplies no
complete tuple to this relation. -/
def Equation.Holds (e : Equation S) (m : Model S) : Prop :=
  ∀ (input : Tuple m.val.toPEG.Value e.carried) (idx : Index 1)
    (output : Tuple m.val.toPEG.Value e.carried),
    let lhs := e.lhs.val.peg
    let rhs := e.rhs.val.peg
    lhs.observe m.val.toPEG (lhs.denote m.val.toPEG input e.lhs.wf) idx = output.map (fun _ => some) ↔
    rhs.observe m.val.toPEG (rhs.denote m.val.toPEG input e.rhs.wf) idx = output.map (fun _ => some)

end Silmaril.SSA.Peggy.Bridge.Theta
