module

public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Theta.Defs
public import Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.SSA.RVSDG.NestedTheta.Thms
import Silmaril.SSA.RVSDG.Theta.Thms
import Silmaril.SSA.RVSDG.Theta.Institution.Thms

public section

namespace Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.WholeTheta.Proofs

open NestedTheta.Institution
open OrderedRuntime.Structured (Data Values)

universe u v w
variable {V : Type u} {A : Stateless.Signature.{u,v} V}
variable {args outs carried : Ports (PortSort V)} {past sigs : List (Ports (PortSort V))}

private theorem port_data {t : PortSort V} (p : Port args t) (data : Data args) :
    ∀ {tail}, Data tail → Data (t :: tail) := by
  induction p with
  | head =>
    cases data with
    | value _ => exact fun h => .value h
    | control _ => exact fun h => .control h
  | tail _ ih => cases data <;> exact ih ‹Data _›

private theorem wires_data (wires : Wires args past outs) (entry : Data args)
    (locals : ∀ row ∈ past, Data row) : Data outs := by
  induction wires with
  | nil => exact .nil
  | cons wire _ ih =>
    cases wire with
    | arg p => exact port_data p entry ih
    | output i p => exact port_data p (locals _ (List.getElem_mem i.isLt)) ih

private theorem body_noState (t : Term A.op args past sigs outs) (entry : Data args)
    (locals : ∀ row ∈ past, Data row) : Stateless.NoState (NestedTheta.Term.ofBase t) ∧ Data outs := by
  induction t with
  | ret wires =>
    have result := wires_data wires entry locals
    exact ⟨⟨entry, result⟩, result⟩
  | @bind args head outs past tail node children rest ihChild ihRest =>
    rcases node with ⟨ins, shape, wires, childSigs⟩
    have input := wires_data wires entry locals
    have next {result} (h : Data result) : ∀ row ∈ past ++ [result], Data row := by
      intro row member
      rcases List.mem_append.mp member with old | new
      · exact locals row old
      · obtain rfl := List.mem_singleton.mp new
        exact h
    cases shape with
    | simple op =>
      cases op with
      | pure p =>
        have ⟨admitted, result⟩ := ihRest entry (next (A.ports p).2)
        exact ⟨⟨input, (A.ports p).2, fun i => i.elim0, admitted⟩, result⟩
      | effect op => nomatch op
    | gamma extra =>
      cases input with
      | control params =>
        have arms := fun i => ihChild i params (fun _ h => by simp at h)
        have result := (arms (0 : Fin (extra + 2))).2
        have ⟨admitted, output⟩ := ihRest entry (next result)
        exact ⟨⟨.control params, result, fun i => (arms i).1, admitted⟩, output⟩

theorem embed_noState (g : Theta.Graph A.pure carried sigs) (data : Data carried) :
    Stateless.NoState (embed g).toTerm := by
  rw [embed, NestedTheta.Term.toTerm_toGraph]
  exact ⟨data, data, fun _ => (body_noState _ data (fun _ h => by simp at h)).1, ⟨data, data⟩⟩

private abbrev wrappedRuntime (m : Stateless.Model.{u,v,w} A) : Model.{u,v,max u w} A.op where
  value := m.value
  state _ := PUnit
  run
    | .pure op => m.run op
    | .effect op => nomatch op

set_option backward.isDefEq.respectTransparency false in
theorem embed_observe (m : Stateless.Model.{u,v,w} A) (g : Theta.Graph A.pure carried sigs)
    (input output : Tuple (Values m.value) carried) :
    Stateless.observe m (embed g) input = Part.some output ↔ g.Returns (runtime m) input output := by
  let tagged := Theta.Institution.relabel (Q := A.op) .pure g
  let total := NestedTheta.MonadicModel.ofRuntime (M := Part) (wrappedRuntime m)
  let observeWith (run : ∀ ins outs, A.op ins outs → Tuple (Values m.value) ins →
      Part (Tuple (Values m.value) outs)) : Part (Tuple (Values m.value) carried) :=
    NestedTheta.Partial.observe
      (⟨m.value, fun _ => PUnit, fun {ins outs} => run ins outs⟩ : NestedTheta.Partial.Model.{u,v,max u w} A.op)
      (embed g) input
  have primitiveEq :
      (fun ins outs op (x : Tuple (Values m.value) ins) =>
        (show Part (Tuple (Values m.value) outs) from @total.primitive ins outs op x)) =
      (fun ins outs op x => @m.partial.primitive ins outs op x) := by
    funext ins outs op input
    cases op with
    | pure op => rfl
    | effect op => nomatch op
  have observed : NestedTheta.Partial.observe total (embed g) input =
      Stateless.observe m (embed g) input := by
    change observeWith (fun ins outs op x => @total.primitive ins outs op x) =
      observeWith (fun ins outs op x => @m.partial.primitive ins outs op x)
    exact congrArg observeWith primitiveEq
  rw [← observed]
  have first := NestedTheta.Partial.observe_ofRuntime_eq_some_iff_returns (wrappedRuntime m)
    (embed g) input output
  exact first.trans <| (NestedTheta.Term.returns_toGraph (.ofTheta tagged.toTerm)
    (wrappedRuntime m) input output).trans <| (NestedTheta.Term.returns_ofTheta tagged.toTerm
      (wrappedRuntime m) input output).trans <| by
    have termToGraph := (Theta.Term.returns_toGraph tagged.toTerm (wrappedRuntime m) input output).symm
    rw [Theta.Graph.toGraph_toTerm] at termToGraph
    exact termToGraph.trans (Theta.Institution.relabel_returns .pure g (wrappedRuntime m) input output)

end Silmaril.SSA.RVSDG.MLIR.Graph.Feedback.WholeTheta.Proofs
