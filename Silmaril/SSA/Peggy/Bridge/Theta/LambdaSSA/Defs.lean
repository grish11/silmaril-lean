module

public import Silmaril.SSA.Peggy.Bridge.Theta.Thms
public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Relabel.Thms
public import Silmaril.SSA.PEG.Bridge.Theta.Region.LambdaSSA.Thms

/-! # Native finite-return equations and their checked θ presentation -/

@[expose] public section

namespace Silmaril.SSA.Peggy.Bridge.Theta.LambdaSSA

open CategoryTheory
open PEG.Bridge.Theta.Region.LambdaSSA (Primitive Packet instruction pack lower lower_hasType lower_map)
open PEG.Bridge.Theta.Region.Ordered (Bundle)
open RVSDG (Port Tuple)
open Isotope.LambdaSSA (Region)
open Isotope.LambdaSSA.Semantics (extend)
open Isotope.LambdaSSA.Semantics.Region (Eval)

variable {Data : Type} {S T : Signature Data}
variable {carried : List (PEG.Ty Data)}

namespace Native

def opcode (f : S ⟶ T) : Primitive S.dialect.ops → Primitive T.dialect.ops :=
  Primitive.map (opMap f)

/-- The syntax is an actual Isotope region checked at the ordered packet
boundary. A native equation needs no graph, schedule, or compiler witness. -/
def Code (S : Signature Data) (carried : List (PEG.Ty Data)) :=
  {r : Region (Primitive S.dialect.ops) // r.HasType [Packet carried] [Packet carried]}

def Code.map (f : S ⟶ T) (r : Code S carried) : Code T carried :=
  ⟨r.val.mapInstr (opcode f),
    r.property.mapInstr _ (Primitive.map_types (opMap f))⟩

structure Equation (S : Signature Data) where
  carried : List (PEG.Ty Data)
  lhs : Code S carried
  rhs : Code S carried

def Equation.map (f : S ⟶ T) (e : Equation S) : Equation T :=
  ⟨e.carried, e.lhs.map f, e.rhs.map f⟩

/-- Observe a fully defined ordered tuple at the sole external exit.
Pure total primitive models use unit ambient state. -/
def Code.Returns (r : Code S carried) (m : Model S)
    (input output : Tuple m.val.toPEG.Value carried) : Prop :=
  Eval (instruction m.val) (extend (fun _ => .unit) (pack m.val input))
    r.val () 0 (pack m.val output) ()

/-- Compare successful native observations at every typed packet. -/
def Equation.Holds (e : Equation S) (m : Model S) : Prop :=
  ∀ input output : Tuple m.val.toPEG.Value e.carried,
    e.lhs.Returns m input output ↔ e.rhs.Returns m input output

end Native

/-- Keep the two compiler outputs of a single checked side. The admission
witness is proof-irrelevant. It fixes the chosen schedule without selecting
a schedule from an existential during sentence translation. -/
structure Side (S : Signature Data) (carried : List (PEG.Ty Data)) where
  peg : Theta.Side S carried
  native : Native.Code S carried
  checked : ∃ (t : PEG.Ty Data) (slot : Port carried t) (invariants : Bool)
      (b : Bundle peg.val.peg slot invariants),
    b.scalar.descriptor.negate = S.negation ∧
      bundleCode (S := S) b = peg.val.code ∧ lower b = native.val

def Side.ofBundle {n : Nat} {t : PEG.Ty Data} {g : PEG.Graph S.dialect.ops carried carried n 1}
    {slot : Port carried t} {invariants : Bool}
    (b : Bundle g slot invariants) (negation : b.scalar.descriptor.negate = S.negation) :
    Side S carried :=
  ⟨Theta.Side.ofBundle b negation, ⟨lower b, lower_hasType b⟩,
    ⟨t, slot, invariants, b, negation, rfl, rfl⟩⟩

def Side.map (f : S ⟶ T) (r : Side S carried) : Side T carried := by
  refine ⟨r.peg.map f, r.native.map f, ?_⟩
  obtain ⟨t, slot, invariants, b, marked, numbered, native⟩ := r.checked
  refine ⟨t, slot, invariants, PEG.Bridge.Theta.Region.Relabel.bundle (opMap f) b, ?_, ?_, ?_⟩
  · exact (congrArg (opMap f) marked).trans f.property
  · exact (PEG.Bridge.Theta.Region.Relabel.compile_map (opMap f) b.scalar).trans
      (congrArg (mapCode f) numbered)
  · exact (lower_map (opMap f) b).trans (congrArg (Region.mapInstr (Native.opcode f)) native)

structure CheckedEquation (S : Signature Data) where
  carried : List (PEG.Ty Data)
  lhs : Side S carried
  rhs : Side S carried

def CheckedEquation.peg (e : CheckedEquation S) : Theta.Equation S :=
  ⟨e.carried, e.lhs.peg, e.rhs.peg⟩

def CheckedEquation.native (e : CheckedEquation S) : Native.Equation S :=
  ⟨e.carried, e.lhs.native, e.rhs.native⟩

def CheckedEquation.map (f : S ⟶ T) (e : CheckedEquation S) : CheckedEquation T :=
  ⟨e.carried, e.lhs.map f, e.rhs.map f⟩

/-- The restricted θ sentence consists of the actual θ equation and the
native regions emitted with it. The source PEG is needed only in admission. -/
abbrev ThetaImageData (S : Signature Data) :=
  RVSDG.Theta.Institution.Equation (PEG.Bridge.Theta.Region.Opcode S.dialect.ops) × Native.Equation S

def CheckedEquation.imageData (e : CheckedEquation S) : ThetaImageData S :=
  (e.peg.translate, e.native)

def ThetaImage (S : Signature Data) :=
  {d : ThetaImageData S // ∃ e : CheckedEquation S, e.imageData = d}

def CheckedEquation.toTheta (e : CheckedEquation S) : ThetaImage S :=
  ⟨e.imageData, ⟨e, rfl⟩⟩

def ThetaImageData.map (f : S ⟶ T) (d : ThetaImageData S) : ThetaImageData T :=
  ((thetaPlain Data).map f d.1, d.2.map f)

def ThetaImage.map (f : S ⟶ T) (d : ThetaImage S) : ThetaImage T := by
  refine ⟨d.val.map f, ?_⟩
  obtain ⟨e, same⟩ := d.property
  rw [← same]
  exact ⟨e.map f, Prod.ext (e.peg.translate_map f) rfl⟩

end Silmaril.SSA.Peggy.Bridge.Theta.LambdaSSA
