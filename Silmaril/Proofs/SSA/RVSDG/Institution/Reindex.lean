module

public import Silmaril.SSA.RVSDG.Institution.Defs
public import Silmaril.SSA.RVSDG.Categorical.Thms

public section

namespace Silmaril.SSA.RVSDG.Institution.Proofs

open CategoryTheory Silmaril.Logic.Institution

universe u v w
variable {V S : Type u} {P Q R : Dialect.{u, v} V S}
variable {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

private theorem term_map_id (t : Term P args past sigs outs) :
    mapTerm (fun f => f) t = t := by
  induction t with
  | ret => rfl
  | bind node children rest ihChildren ihRest =>
    rcases node with ⟨ins, shape, wires, childSigs⟩
    cases shape with
    | simple op =>
      rw [mapTerm, ihRest]
      exact congrArg (fun c => Term.bind _ c rest) (funext fun i => i.elim0)
    | gamma extra =>
      rw [mapTerm, ihRest]
      exact congrArg (fun c => Term.bind _ c rest) (funext ihChildren)

private theorem term_map_comp (h : OpcodeMap P Q) (k : OpcodeMap Q R)
    (t : Term P args past sigs outs) :
    mapTerm (fun f => k (h f)) t = mapTerm k (mapTerm h t) := by
  induction t with
  | ret => rfl
  | bind node children rest ihChildren ihRest =>
    rcases node with ⟨ins, shape, wires, childSigs⟩
    cases shape with
    | simple op => simp only [mapTerm, ihRest]
    | gamma extra =>
      simp only [mapTerm, ihRest]
      exact congrArg (fun c => Term.bind _ c _) (funext ihChildren)

theorem graph_map_id (g : Graph P args past sigs outs) :
    mapGraph (fun f => f) g = g := by
  rw [mapGraph, term_map_id, Graph.toGraph_toTerm]

theorem graph_map_comp (h : OpcodeMap P Q) (k : OpcodeMap Q R)
    (g : Graph P args past sigs outs) :
    mapGraph (fun f => k (h f)) g = mapGraph k (mapGraph h g) := by
  simp only [mapGraph, Term.toTerm_toGraph, term_map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem eval_map (h : OpcodeMap P Q) (m : Model.{u, v, w} Q) (t : Term P args past sigs outs)
    (input : Tuple m.Val args) (locals : Locals m.Val past) :
    (mapTerm h t).eval m input locals = t.eval (reduct h m) input locals := by
  induction t with
  | ret => rfl
  | bind node children rest ihChildren ihRest =>
    rcases node with ⟨ins, shape, wires, childSigs⟩
    cases shape with
    | simple op =>
      simp only [mapTerm, Term.eval, Shape.eval, reduct]
      apply ihRest
    | gamma extra =>
      simp only [mapTerm, Term.eval]
      rw [ihRest]
      cases wires.read input locals with
      | cons choice payload =>
        exact congrArg (fun result => Term.eval (reduct h m) input (locals.snoc result) rest)
          (ihChildren choice.down payload PUnit.unit)

set_option backward.isDefEq.respectTransparency false in
theorem graph_run_map (h : OpcodeMap P Q) (m : Model.{u, v, w} Q) (g : Graph P args [] sigs outs)
    (input : Tuple m.Val args) :
    (mapGraph h g).run m input = g.run (reduct h m) input := by
  rw [mapGraph, Term.run_toGraph, ← Graph.run_toTerm]
  exact eval_map h m g.toTerm input PUnit.unit

theorem equation_map_id (e : Equation P) : e.map (fun f => f) = e := by
  cases e
  simp only [Equation.map, graph_map_id]

theorem equation_map_comp (h : OpcodeMap P Q) (k : OpcodeMap Q R) (e : Equation P) :
    e.map (fun f => k (h f)) = (e.map h).map k := by
  cases e
  simp only [Equation.map, graph_map_comp]

theorem reductFunctor_id (P : Dialect.{u, v} V S) :
    reductFunctor.{u, v, w} (P := P) (fun f => f) = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun m => by cases m; rfl)

theorem reductFunctor_comp (h : OpcodeMap P Q) (k : OpcodeMap Q R) :
    reductFunctor.{u, v, w} (P := P) (Q := R) (fun f => k (h f)) =
      reductFunctor (P := Q) (Q := R) k ⋙ reductFunctor (P := P) (Q := Q) h :=
  CategoryTheory.Functor.ext (fun _ => rfl)

set_option backward.isDefEq.respectTransparency false in
theorem satisfaction (h : OpcodeMap P Q) (e : Equation P) (m : Model.{u, v, w} Q) :
    (e.map h).Holds m ↔ e.Holds (reduct h m) := by
  change (∀ input : Tuple m.Val e.args, (mapGraph h e.lhs).run m input =
    (mapGraph h e.rhs).run m input) ↔ _
  simp only [graph_run_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem holds_iff_denote (e : Equation P) (m : Model.{u, v, w} P) :
    e.Holds m ↔ e.lhs.denote (Categorical.Model.ofRuntime m) =
      e.rhs.denote (Categorical.Model.ofRuntime m) := by
  constructor
  · intro hs
    apply ConcreteCategory.coe_ext
    funext input
    let entry : Tuple m.Val e.args := Categorical.unpack e.args input
    have hp : Categorical.pack entry = input := Categorical.pack_unpack e.args input
    rw [← hp]
    exact (Graph.denote_pack m e.lhs entry).trans
      ((congrArg Categorical.pack (hs entry)).trans (Graph.denote_pack m e.rhs entry).symm)
  · intro hs input
    have packed := congrArg (fun f => f (Categorical.pack input)) hs
    rw [Graph.denote_pack, Graph.denote_pack] at packed
    simpa only [Categorical.unpack_pack] using congrArg (Categorical.unpack e.outs) packed

end Silmaril.SSA.RVSDG.Institution.Proofs
