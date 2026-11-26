module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Correctness

@[expose] public section

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link

open CategoryTheory
open Comparison
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement (resumeSSA)

variable {V F α : Type} [DecidableEq V] {a b c : Nat}

theorem Graph.table_closed (graph : Graph V F a b) : RoundTrip.PacketClosedTable graph.table :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.table_closed graph

/-- Execution uses the ordinary named cyclic table. The public return
is tagged as external and the base environment can be chosen freely. -/
theorem Graph.denote_eq_resume (model : Model F Part α) (graph : Graph V F a b)
    (external : V → α) (input : Fin a × α) :
    Prod.map Sum.inr id <$> graph.denote model input =
      resumeSSA model graph.table external (graph.entry input.1, input.2) :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.denote_eq_resume model graph external input

/-- Run the ordinary one-table CFG with the input packet in the designated register. -/
theorem Graph.denote_eq_runSSA [Inhabited V] (model : Model F Part α) (graph : Graph V F a b)
    (external : V → α) (port : Fin a) (packet : α) :
    Prod.map Sum.inr id <$> graph.denote model (port, packet) =
      Cyclic.runSSA model (graph.toCFG port) (upd external default packet) := by
  rw [graph.denote_eq_resume model (upd external default packet) (port, packet)]
  simp [Graph.toCFG, Cyclic.runSSA, resumeSSA, Body.evalJump, Body.exec, Term.exec, Val.eval, upd]

@[simp] theorem Graph.denote_identity (model : Model F Part α) (input : Fin a × α) :
    (Graph.identity (V := V) (F := F) a).denote model input = pure input :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.denote_identity model input

/-- Running the linked syntax is staged exit plugging. Only the port and
packet produced by the left stage are passed to the right stage. -/
theorem Graph.denote_link [Inhabited V] (model : Model F Part α) (left : Graph V F a b)
    (right : Graph V F b c) (input : Fin a × α) :
    (left.link right).denote model input = left.denote model input >>= right.denote model :=
  Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.denote_link model left right input

theorem arrow_ext {lhs rhs : Arrow V F α a b}
    (same : ∀ model input, observe model lhs input = observe model rhs input) : lhs = rhs :=
  Quotient.inductionOn₂ lhs rhs (fun _ _ equal => Quotient.sound equal) same

noncomputable def identity (a : Nat) : Arrow V F α a a :=
  Quotient.mk _ (Graph.identity a)

@[simp] theorem observe_identity (model : PairModel F Part α) (input : Fin a × α) :
    observe model (identity (V := V) a) input = pure input :=
  Graph.denote_identity model.val input

variable [Inhabited V]

/-- Composition on classes is induced by the executable one-table linker. -/
noncomputable def compose : Arrow V F α a b → Arrow V F α b c → Arrow V F α a c :=
  Quotient.map₂ (sa := graphSetoid (α := α)) (sb := graphSetoid (α := α))
    (sc := graphSetoid (α := α))
    (fun (left : Graph V F a b) (right : Graph V F b c) => left.link right)
    fun _ _ first _ _ second model input => by
    rw [Graph.denote_link, Graph.denote_link, first model input]
    exact bind_congr (second model)

@[simp] theorem observe_compose (model : PairModel F Part α) (left : Arrow V F α a b)
    (right : Arrow V F α b c) (input : Fin a × α) :
    observe model (compose left right) input =
      observe model left input >>= observe model right :=
  Quotient.inductionOn₂ left right fun first second => Graph.denote_link model.val first second input

/-- Finite packet interfaces and observational classes of executable graphs
form a category under linking. -/
noncomputable instance : Category (Interface V F α) where
  Hom source target := Arrow V F α source.ports target.ports
  id object := identity object.ports
  comp := compose
  id_comp _ := arrow_ext fun model input => by simp only [observe_compose, observe_identity, pure_bind]
  comp_id _ := arrow_ext fun model input => by
    rw [observe_compose]
    exact (bind_congr (observe_identity model)).trans (bind_pure _)
  assoc _ _ _ := arrow_ext fun model input => by
    simp only [observe_compose, bind_assoc]
    exact bind_congr fun packet => (observe_compose model _ _ packet).symm

/-- Replacing either linked graph by one with more terminating results
can only add terminating results of the composite. -/
theorem compose_mono {left left' : Arrow V F α a b} {right right' : Arrow V F α b c}
    (first : Refines left left') (second : Refines right right') :
    Refines (compose left right) (compose left' right') := by
  intro model input
  rw [observe_compose, observe_compose]
  intro output member
  obtain ⟨middle, produced, consumed⟩ := Part.mem_bind_iff.mp member
  exact Part.mem_bind (first model input middle produced) (second model middle output consumed)

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
