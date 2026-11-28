module

public import Silmaril.SSA.RVSDG.Defs
import Silmaril.Proofs.SSA.RVSDG.Correspondence

public section

namespace Silmaril.SSA.RVSDG.Proofs

universe u v w
variable {V S : Type u} {P : Dialect.{u,v} V S}
variable {F G : PortType V S → Type w}

private theorem tuple_get_map (f : ∀ t, F t → G t) {ts : Ports (PortType V S)}
    (xs : Tuple F ts) {t : PortType V S} (p : Port ts t) :
    (xs.map f).get p = f t (xs.get p) := by
  induction p with
  | head => cases xs; rfl
  | tail _ ih => cases xs with | cons _ xs => exact ih xs

private def mapLocals (f : ∀ t, F t → G t) :
    (past : List (Ports (PortType V S))) → Locals F past → Locals G past
  | [], _ => PUnit.unit
  | _ :: tail, xs => (xs.1.map f, mapLocals f tail xs.2)

private theorem locals_get_map (f : ∀ t, F t → G t)
    (past : List (Ports (PortType V S))) (xs : Locals F past) (i : Fin past.length) :
    (mapLocals f past xs).get i = (xs.get i).map f := by
  induction past with
  | nil => exact i.elim0
  | cons _ _ ih => exact Fin.cases rfl (fun j => ih xs.2 j) i

private theorem locals_snoc_map (f : ∀ t, F t → G t)
    (past : List (Ports (PortType V S))) (xs : Locals F past)
    {head : Ports (PortType V S)} (x : Tuple F head) :
    mapLocals f (past ++ [head]) (xs.snoc x) = (mapLocals f past xs).snoc (x.map f) := by
  induction past with
  | nil => rfl
  | cons _ _ ih => exact congrArg (Prod.mk _) (ih xs.2)

private theorem read_map (f : ∀ t, F t → G t) {args outs : Ports (PortType V S)}
    {past : List (Ports (PortType V S))} (wires : Wires args past outs)
    (entry : Tuple F args) (locals : Locals F past) :
    (wires.read entry locals).map f = wires.read (entry.map f) (mapLocals f past locals) := by
  induction wires with
  | nil => rfl
  | cons wire rest ih =>
    cases wire with
    | arg p =>
      simp only [Wires.read, Tuple.map, tuple_get_map] at ih ⊢
      rw [ih]
    | output i p =>
      have h : ((mapLocals f past locals).get i).get p = f _ ((locals.get i).get p) := by
        rw [locals_get_map, tuple_get_map]
      simp only [Wires.read, Tuple.map] at ih ⊢
      rw [h, ih]

-- The evaluator transports along maps of values preserving primitive results and selectors.
set_option backward.isDefEq.respectTransparency false in
private theorem eval_map {m n : Model.{u, v, w} P} (f : ∀ t, m.Val t → n.Val t)
    (run : ∀ {ins outs} (op : P ins outs) (input : Tuple m.Val ins),
      (m.run op input).map f = n.run op (input.map f))
    (control : ∀ k (x : ULift (Fin k)), f (.control k) x = x)
    {args outs : Ports (PortType V S)} {past sigs : List (Ports (PortType V S))}
    (term : Term P args past sigs outs) (entry : Tuple m.Val args) (locals : Locals m.Val past) :
    (term.eval m entry locals).map f =
      term.eval n (entry.map f) (mapLocals f past locals) := by
  induction term with
  | ret wires => exact read_map f wires entry locals
  | bind node children rest ihChildren ihRest =>
    rcases node with ⟨ins, shape, wires, childSigs⟩
    simp only [Term.eval, ihRest, locals_snoc_map]
    rw [← read_map f wires entry locals]
    congr 2
    cases shape with
    | simple op => exact run op _
    | gamma extra =>
      cases wires.read entry locals with
      | cons choice payload =>
        simp only [Tuple.map, control, Shape.eval]
        exact ihChildren choice.down payload PUnit.unit

theorem graph_run_map {m n : Model.{u, v, w} P} (f : ∀ t, m.Val t → n.Val t)
    (run : ∀ {ins outs} (op : P ins outs) (input : Tuple m.Val ins),
      (m.run op input).map f = n.run op (input.map f))
    (control : ∀ k (x : ULift (Fin k)), f (.control k) x = x)
    {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}
    (g : Graph P args [] sigs outs) (entry : Tuple m.Val args) :
    (g.run m entry).map f = g.run n (entry.map f) := by
  unfold Graph.run
  rw [← eval_toTerm g m entry PUnit.unit, ← eval_toTerm g n (entry.map f) PUnit.unit]
  exact eval_map f run control g.toTerm entry PUnit.unit

end Silmaril.SSA.RVSDG.Proofs
