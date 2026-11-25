module

public import Silmaril.SSA.RVSDG.Institution.Categorical.Defs
public import Silmaril.SSA.RVSDG.Institution.Thms
import Silmaril.Proofs.SSA.RVSDG.Institution.Categorical.Reindex

/-! # Categorical change of dialect and deterministic specialization -/

public section

namespace Silmaril.SSA.RVSDG.Institution

open CategoryTheory Silmaril.Logic.Institution

universe u v d h w
variable {V S : Type u} {P Q : Dialect.{u, v} V S}
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D]
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

set_option backward.isDefEq.respectTransparency false

/-- Relabelling preserves the open term arrow at every numbered prefix. -/
theorem mapTerm_denoteOpen (f : OpcodeMap P Q) (m : Categorical.Model Q D)
    (t : Term P args past sigs outs) :
    (mapTerm f t).denoteOpen m = t.denoteOpen (categoricalReduct f m) :=
  CategoricalProofs.term_denoteOpen_map f m t

/-- A graph interpreted after relabelling has the source arrow in the reduct. -/
theorem mapGraph_denote (f : OpcodeMap P Q) (m : Categorical.Model Q D)
    (g : Graph P args [] sigs outs) :
    (mapGraph f g).denote m = g.denote (categoricalReduct f m) :=
  CategoricalProofs.graph_denote_map f m g

theorem Equation.categoricalSatisfaction (f : OpcodeMap P Q) (e : Equation P)
    (m : Categorical.Model Q D) :
    (e.map f).HoldsCategorically m ↔ e.HoldsCategorically (categoricalReduct f m) :=
  CategoricalProofs.satisfaction f e m

@[expose] def categoricalCorridor {P Q : Signature.{u, v} V S} (f : P ⟶ Q) :
    categoricalRoom P D ⟶ categoricalRoom Q D :=
  let op : OpcodeMap P.op Q.op := Signature.opcodeMap f
  ⟨Equation.map op, categoricalReductFunctor op, fun m e =>
    Equation.categoricalSatisfaction (P := P.op) (Q := Q.op) op e m.as⟩

theorem categoricalCorridor_id (P : Signature.{u, v} V S) :
    categoricalCorridor (D := D) (𝟙 P) = 𝟙 (categoricalRoom P D) :=
  Room.hom_ext (funext (Equation.map_id (P := P.op))) (CategoricalProofs.reductFunctor_id P.op)

theorem categoricalCorridor_comp {P Q R : Signature.{u, v} V S} (f : P ⟶ Q) (g : Q ⟶ R) :
    categoricalCorridor (D := D) (f ≫ g) = categoricalCorridor f ≫ categoricalCorridor g :=
  Room.hom_ext (funext (Equation.map_comp (P := P.op) (Q := Q.op) (R := R.op)
    (Signature.opcodeMap f) (Signature.opcodeMap g)))
    (CategoricalProofs.reductFunctor_comp (P := P.op) (Q := Q.op) (R := R.op)
      (Signature.opcodeMap f) (Signature.opcodeMap g))

/-- The RVSDG equation institution in a fixed Cartesian value category. -/
@[expose] def categoricalInst (V S : Type u) (D : Type d)
    [Category.{h} D] [CartesianMonoidalCategory D] :
    Inst.{max u (v + 1), max u v, max u v, max u v d h, max u v d h} where
  Sign := Signature.{u, v} V S
  I :=
    { obj := fun P => categoricalRoom P D
      map := categoricalCorridor
      map_id := categoricalCorridor_id
      map_comp := categoricalCorridor_comp }

/-- The local comparison sends each deterministic model to its categorical
interpretation and acts by the identity on equations. -/
@[expose] def runtimeComparison (P : Signature.{u, v} V S) :
    categoricalRoom P (Type w) ⟶ room.{u, v, w} P :=
  ⟨id, ofRuntimeFunctor P.op, fun m e => Equation.holds_iff_denote (P := P.op) e m.as⟩

theorem runtimeComparison_naturality {P Q : Signature.{u, v} V S} (f : P ⟶ Q) :
    categoricalCorridor (D := Type w) f ≫ runtimeComparison Q =
      runtimeComparison P ≫ corridor.{u, v, w} f :=
  Room.hom_ext rfl (CategoricalProofs.ofRuntime_natural (P := P.op) (Q := Q.op)
    (Signature.opcodeMap f)).symm

/-- Specialize the Cartesian institution in types to deterministic execution.
Signatures and equations are unchanged. Models are mapped contravariantly
by the tuple-encoding adapter `Categorical.Model.ofRuntime`. -/
@[expose] def toRuntime (V S : Type u) :
    Inst.CoHom (categoricalInst.{u, v, w + 1, w} V S (Type w)) (inst.{u, v, w} V S) where
  Φ := 𝟭 _
  ρ :=
    { app := runtimeComparison
      naturality := fun {X Y} f => runtimeComparison_naturality (P := X) (Q := Y) f }

end Silmaril.SSA.RVSDG.Institution
