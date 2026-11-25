module

public import Silmaril.SSA.RVSDG.Categorical.Defs
public import Silmaril.SSA.RVSDG.Thms

public section

namespace Silmaril.SSA.RVSDG.Categorical.Proofs

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open scoped MonoidalCategory

universe u v d h w
variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {D : Type d} [Category.{h} D] [CartesianMonoidalCategory D]
variable {args ins outs ts : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}

theorem dispatch_leg (sel : Selectors D) {n : Nat} {X Y : D}
    (arms : Fin n → (X ⟶ Y)) (i : Fin n) :
    selectorLeg (sel.tag i) ≫ dispatch sel arms = arms i :=
  (sel.colimit n X).fac (Cofan.mk Y arms) ⟨i⟩

set_option backward.isDefEq.respectTransparency false in
private theorem denoteFromTable (m : Model Op D)
    (past sigs : List (Ports (PortType V S))) (nodes : Nodes Op args past sigs)
    (children : (i : Fin sigs.length) → Children (Term Op) (nodes i))
    (results : Wires args (extend past sigs) outs) :
    (Term.fromTable past sigs nodes children results).denoteOpen m =
      Graph.denoteTable m past sigs nodes
        (fun i j => (ρ_ _).inv ≫ (children i j).denoteOpen m) results := by
  induction sigs generalizing past with
  | nil => rfl
  | cons head tail ih =>
    simp only [Term.fromTable, Term.denoteOpen, Graph.denoteTable]
    rw [ih]

theorem denoteOpen_toTerm (m : Model Op D) (g : Graph Op args past sigs outs) :
    g.toTerm.denoteOpen m = g.denoteOpen m := by
  induction g with
  | region nodes children results ih =>
    simp only [Graph.toTerm, denoteFromTable, Graph.denoteOpen, ih]

theorem unpack_pack {F : PortType V S → Type w} (input : Tuple F ts) :
    unpack ts (pack input) = input := by
  induction input with
  | nil => rfl
  | cons x xs ih => exact congrArg (Tuple.cons x) ih

theorem pack_unpack {F : PortType V S → Type w} (ts : Ports (PortType V S))
    (input : portsObj F ts) : pack (unpack ts input) = input := by
  induction ts with
  | nil => cases input; rfl
  | cons t ts ih => exact congrArg (fun tail => (input.1, tail)) (ih input.2)

section Types

variable (r : RVSDG.Model.{u, v, w} Op)

private def packLocals : (past : List (Ports (PortType V S))) →
    Locals r.Val past → (Model.ofRuntime r).locals past
  | [], _ => PUnit.unit
  | _ :: tail, (value, rest) => (pack value, packLocals tail rest)

private theorem project_pack {t : PortType V S} (p : Port ts t) (xs : Tuple r.Val ts) :
    project (Model.ofRuntime r) p (pack xs) = xs.get p := by
  induction p with
  | head => cases xs; rfl
  | tail p ih => cases xs with | cons x xs => exact ih xs

private theorem projectLocal_pack (past : List (Ports (PortType V S)))
    (i : Fin past.length) (locals : Locals r.Val past) :
    projectLocal (Model.ofRuntime r) past i (packLocals r past locals) = pack (locals.get i) := by
  induction past with
  | nil => exact i.elim0
  | cons head tail ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih j locals.2

private theorem readOrigin_pack {t : PortType V S} (o : Origin args past t)
    (entry : Tuple r.Val args) (locals : Locals r.Val past) :
    readOrigin (Model.ofRuntime r) o (pack entry, packLocals r past locals) =
      (match o with | .arg p => entry.get p | .output i p => (locals.get i).get p) := by
  cases o with
  | arg p => exact project_pack r p entry
  | output i p =>
    exact (congrArg (fun value => project (Model.ofRuntime r) p value)
      (projectLocal_pack r past i locals)).trans (project_pack r p (locals.get i))

private theorem readWires_pack (wires : Wires args past ts)
    (entry : Tuple r.Val args) (locals : Locals r.Val past) :
    readWires (Model.ofRuntime r) wires (pack entry, packLocals r past locals) =
      pack (wires.read entry locals) := by
  induction wires with
  | nil => rfl
  | cons o rest ih =>
    change (readOrigin (Model.ofRuntime r) o (pack entry, packLocals r past locals),
      readWires (Model.ofRuntime r) rest (pack entry, packLocals r past locals)) = _
    rw [readOrigin_pack, ih]
    cases o <;> rfl

private theorem appendLocal_pack (past : List (Ports (PortType V S))) (locals : Locals r.Val past)
    (result : Tuple r.Val ts) :
    appendLocal (Model.ofRuntime r) ts past (packLocals r past locals, pack result) =
      packLocals r (past ++ [ts]) (locals.snoc result) := by
  induction past with
  | nil => rfl
  | cons head tail ih =>
    change (pack locals.1, appendLocal (Model.ofRuntime r) ts tail
      (packLocals r tail locals.2, pack result)) = _
    rw [ih]
    rfl

private theorem denoteShape_pack (s : Shape Op ins outs)
    (arms : Fin s.regionCount → ((Model.ofRuntime r).ports s.entry ⟶ (Model.ofRuntime r).ports s.exit))
    (evalArms : Fin s.regionCount → Tuple r.Val s.entry → Tuple r.Val s.exit)
    (ih : ∀ i x, arms i (pack x) = pack (evalArms i x)) (input : Tuple r.Val ins) :
    denoteShape (Model.ofRuntime r) s arms (pack input) = pack (s.eval r evalArms input) := by
  cases s with
  | simple opcode =>
    change pack (r.run opcode (unpack _ (pack input))) = pack (r.run opcode input)
    rw [unpack_pack]
  | gamma extra =>
    cases input with
    | cons tag payload => exact ih tag.down payload

set_option backward.isDefEq.respectTransparency false in
private theorem denoteOpen_pack (t : Term Op args past sigs outs)
    (entry : Tuple r.Val args) (locals : Locals r.Val past) :
    t.denoteOpen (Model.ofRuntime r) (pack entry, packLocals r past locals) =
      pack (t.eval r entry locals) := by
  induction t with
  | ret results => exact readWires_pack r results entry locals
  | bind node children rest ihChild ihRest =>
    let arms := fun j => (ρ_ _).inv ≫ (children j).denoteOpen (Model.ofRuntime r)
    let input := node.inputs.read entry locals
    let evalArms (j : Fin node.shape.regionCount) (x : Tuple r.Val node.shape.entry) :=
      (children j).eval r (past := []) x PUnit.unit
    have branch : ∀ j x, arms j (pack x) = pack (evalArms j x) :=
      fun j x => ihChild j x PUnit.unit
    change rest.denoteOpen (Model.ofRuntime r) (pack entry, appendLocal (Model.ofRuntime r) _ _
      (packLocals r _ locals, denoteShape (Model.ofRuntime r) node.shape arms
        (readWires (Model.ofRuntime r) node.inputs (pack entry, packLocals r _ locals)))) = _
    rw [readWires_pack, denoteShape_pack r node.shape arms evalArms branch, appendLocal_pack]
    exact ihRest entry (locals.snoc (node.shape.eval r evalArms input))

theorem denote_pack (t : Term Op args [] sigs outs) (entry : Tuple r.Val args) :
    t.denote (Model.ofRuntime r) (pack entry) = pack (t.run r entry) :=
  denoteOpen_pack r t entry PUnit.unit

end Types

end Silmaril.SSA.RVSDG.Categorical.Proofs
