module

public import Silmaril.SSA.RVSDG.Institution.Categorical.Defs
public import Silmaril.SSA.RVSDG.Institution.Thms

public section

namespace Silmaril.SSA.RVSDG.Institution.CategoricalProofs

open CategoryTheory
open Categorical
open scoped MonoidalCategory

universe u v d h w
variable {V S : Type u} {P Q R : Dialect.{u, v} V S}
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D]
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

set_option backward.isDefEq.respectTransparency false

variable (f : OpcodeMap P Q) (m : Categorical.Model Q D)

private theorem project_reduct {ts : Ports (PortType V S)} {t : PortType V S} (p : Port ts t) :
    project m p = project (categoricalReduct f m) p := by
  induction p with
  | head => rfl
  | tail _ ih => simp only [project, ih]

private theorem projectLocal_reduct (past : List (Ports (PortType V S))) (i : Fin past.length) :
    projectLocal m past i = projectLocal (categoricalReduct f m) past i := by
  induction past with
  | nil => exact i.elim0
  | cons _ _ ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · simp only [projectLocal, Fin.cases_succ, ih]

private theorem readOrigin_reduct {t : PortType V S} (o : Origin args past t) :
    readOrigin m o = readOrigin (categoricalReduct f m) o := by
  cases o <;> simp only [readOrigin, project_reduct f m, projectLocal_reduct f m]

private theorem readWires_reduct (wires : Wires args past outs) :
    readWires m wires = readWires (categoricalReduct f m) wires := by
  induction wires with
  | nil => rfl
  | cons o _ ih => simp only [readWires, readOrigin_reduct f m o, ih]

private theorem appendLocal_reduct (ts : Ports (PortType V S))
    (past : List (Ports (PortType V S))) :
    appendLocal m ts past = appendLocal (categoricalReduct f m) ts past := by
  induction past with
  | nil => rfl
  | cons _ _ ih => simp only [appendLocal, ih]

private theorem extendScope_reduct {ts : Ports (PortType V S)}
    (g : m.scope args past ⟶ m.ports ts) :
    extendScope m g = extendScope (categoricalReduct f m) g := by
  simp only [extendScope, appendScope, appendLocal_reduct f m]

theorem term_denoteOpen_map (f : OpcodeMap P Q) (m : Categorical.Model Q D)
    (t : Term P args past sigs outs) :
    (mapTerm f t).denoteOpen m = t.denoteOpen (categoricalReduct f m) := by
  induction t with
  | ret wires => exact readWires_reduct f m wires
  | bind node children rest ihChildren ihRest =>
    rcases node with ⟨ins, shape, wires, childSigs⟩
    cases shape with
    | simple op =>
      simp only [mapTerm, Term.denoteOpen, denoteShape, ihRest,
        readWires_reduct f m, extendScope_reduct f m]
    | gamma extra =>
      simp only [mapTerm, Term.denoteOpen, denoteShape, ihRest, ihChildren,
        readWires_reduct f m, extendScope_reduct f m]
      rfl

theorem graph_denote_map (f : OpcodeMap P Q) (m : Categorical.Model Q D)
    (g : Graph P args [] sigs outs) :
    (mapGraph f g).denote m = g.denote (categoricalReduct f m) := by
  rw [mapGraph, Term.denote_toGraph, ← Graph.denote_toTerm]
  unfold Term.denote
  rw [term_denoteOpen_map]

theorem satisfaction (f : OpcodeMap P Q) (e : Equation P) (m : Categorical.Model Q D) :
    (e.map f).HoldsCategorically m ↔ e.HoldsCategorically (categoricalReduct f m) := by
  change (mapGraph f e.lhs).denote m = (mapGraph f e.rhs).denote m ↔ _
  rw [graph_denote_map, graph_denote_map]
  rfl

theorem reductFunctor_id (P : Dialect.{u, v} V S) :
    categoricalReductFunctor (D := D) (P := P) (fun f => f) = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun m => by cases m; rfl)

theorem reductFunctor_comp (f : OpcodeMap P Q) (g : OpcodeMap Q R) :
    categoricalReductFunctor (D := D) (P := P) (Q := R) (fun op => g (f op)) =
      categoricalReductFunctor (P := Q) (Q := R) g ⋙ categoricalReductFunctor (P := P) (Q := Q) f :=
  CategoryTheory.Functor.ext (fun _ => rfl)

/-- The specialization commutes strictly on model objects with change of dialect. -/
theorem ofRuntime_natural (f : OpcodeMap P Q) :
    reductFunctor.{u, v, w} (P := P) (Q := Q) f ⋙ ofRuntimeFunctor P =
      ofRuntimeFunctor Q ⋙ categoricalReductFunctor (P := P) (Q := Q) f :=
  CategoryTheory.Functor.ext (fun _ => rfl)

end Silmaril.SSA.RVSDG.Institution.CategoricalProofs
