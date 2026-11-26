module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Defs
import Silmaril.SSA.LambdaRTL.CFG.Thms

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link

open Silmaril.Elgot
open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG Silmaril.SSA.LambdaRTL.CFG.Cyclic
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Institution.Refinement

private theorem iter_simulation {X Y B C : Type} (source : X → _root_.Part (B ⊕ X))
    (target : Y → _root_.Part (C ⊕ Y)) (result : B → C) (state : X → Y)
    (square : ∀ x, Sum.map result state <$> source x = target (state x)) (x : X) :
    result <$> iter source x = iter target (state x) := by
  let mapped := mapReturn source (pure ∘ result)
  have commute : (mapped >=> liftPure (Sum.map id state)) = (liftPure state >=> target) := by
    funext input
    change (mapped input >>= liftPure (Sum.map id state)) = (pure (state input) >>= target)
    rw [pure_bind, ← square, ← bind_pure_comp]
    simp only [mapped, mapReturn, bind_assoc]
    apply bind_congr
    intro value
    cases value <;> simp [liftPure]
  have natural := congrFun (LawfulElgotMonad.naturality source (pure ∘ result)) x
  have uniform := congrFun (LawfulElgotMonad.uniformity mapped target state commute) x
  have equality := natural.trans uniform
  change (iter source x >>= fun output => pure (result output)) =
    (pure (state x) >>= iter target) at equality
  rwa [bind_pure_comp, pure_bind] at equality

private def phased {X Y B C : Type} (left : X → _root_.Part (B ⊕ X))
    (right : Y → _root_.Part (C ⊕ Y)) (handoff : B → Y) :
    X ⊕ Y → _root_.Part ((C ⊕ (X ⊕ Y)) ⊕ (X ⊕ Y))
  | .inl x => Sum.map (fun b => .inr (.inr (handoff b))) Sum.inl <$> left x
  | .inr y => Sum.map Sum.inl Sum.inr <$> right y

private theorem phased_run {X Y B C : Type} (left : X → _root_.Part (B ⊕ X))
    (right : Y → _root_.Part (C ⊕ Y)) (handoff : B → Y) (x : X) :
    iter (flattenBody (phased left right handoff)) (.inl x) =
      iter left x >>= fun b => iter right (handoff b) := by
  let phase := phased left right handoff
  have runLeft (input : X) :
      iter phase (.inl input) = (fun b => Sum.inr (.inr (handoff b))) <$> iter left input :=
    (iter_simulation left phase _ Sum.inl (fun _ => rfl) input).symm
  have runRight (input : Y) : iter phase (.inr input) = Sum.inl <$> iter right input :=
    (iter_simulation right phase Sum.inl Sum.inr (fun _ => rfl) input).symm
  have finish (input : Y) : iter (iter phase) (.inr input) = iter right input := by
    rw [congrFun (LawfulElgotMonad.fixpoint (iter phase)) (.inr input), runRight, bind_map_left]
    exact bind_pure _
  rw [← LawfulElgotMonad.codiagonal, congrFun (LawfulElgotMonad.fixpoint (iter phase)) (.inl x),
    runLeft, bind_map_left]
  exact bind_congr fun output => finish (handoff output)

variable {V F α : Type} [DecidableEq V] {a b c : Nat}

private theorem evalJump_relabel {K K' : Type} [DecidableEq K]
    (model : Model F Part α) (rename : K → K') (body : Body V K F) (store : V → α) :
    (body.relabel rename).evalJump model store = Prod.map rename id <$> body.evalJump model store := by
  rw [Body.evalJump, Body.exec_relabel, Body.evalJump]
  simp only [Body.exec_eq_evalRTL, map_bind, map_pure, Prod.map_apply, id_eq]

private theorem lookup_relabel {K K' D E : Type} [DecidableEq K] [DecidableEq K']
    (rename : K → K') (injective : Function.Injective rename) (mapBlock : D → E)
    (table : List (K × D)) (label : K) :
    (table.map fun (key, block) => (rename key, mapBlock block)).lookup (rename label) =
      (table.lookup label).map mapBlock := by
  induction table with
  | nil => rfl
  | cons item rest ih =>
    rcases item with ⟨key, block⟩
    by_cases same : label = key
    · subst key
      simp only [List.map_cons, List.lookup_cons, beq_self_eq_true, Option.map_some]
    · have miss : rename label ≠ rename key := fun equal => same (injective equal)
      simp only [List.map_cons, List.lookup_cons, beq_false_of_ne same, beq_false_of_ne miss, ih]

theorem runSSA_relabel {K K' : Type} [DecidableEq K] [DecidableEq K']
    (model : Model F Part α) (rename : K → K') (injective : Function.Injective rename)
    (graph : CFG V K F) (store : V → α) :
    Prod.map rename id <$> Cyclic.runSSA model graph store =
      Cyclic.runSSA model (graph.relabel rename) store := by
  let encode : K × α → K' × α := Prod.map rename id
  have square (transfer : K × α) :
      Sum.map encode encode <$> Cyclic.stepSSA model graph.blocks store transfer =
        Cyclic.stepSSA model (graph.relabel rename).blocks store (encode transfer) := by
    rcases transfer with ⟨label, packet⟩
    simp only [Cyclic.stepSSA, CFG.relabel, encode, Prod.map_apply, id_eq]
    rw [lookup_relabel rename injective]
    cases graph.blocks.lookup label <;> simp [Block.relabel, evalJump_relabel, Part.map_map, Function.comp_def]
  have run := iter_simulation (Cyclic.stepSSA model graph.blocks store)
    (Cyclic.stepSSA model (graph.relabel rename).blocks store) encode encode square
  simp only [Cyclic.runSSA, CFG.relabel, evalJump_relabel, map_bind, bind_map_left]
  exact bind_congr run

private theorem lookup_private {p q : Nat} {D : Type} (value : Fin p → D)
    (keys : List (Fin p)) (i : Fin p) (member : i ∈ keys) :
    @List.lookup (Label p q) D instBEqOfDecidableEq (Sum.inl i)
      (keys.map fun j => (Sum.inl j, value j)) = some (value i) := by
  induction keys with
  | nil => simp at member
  | cons key rest ih =>
    by_cases same : i = key
    · subst key
      simp
    · have miss : @BEq.beq (Label p q) instBEqOfDecidableEq (Sum.inl i) (Sum.inl key) = false := by
        change decide ((Sum.inl i : Label p q) = Sum.inl key) = false
        simp [same]
      simp only [List.map_cons, List.lookup_cons, miss]
      exact ih ((List.mem_cons.mp member).resolve_left same)

private theorem lookup_public {p q : Nat} {D : Type} (value : Fin p → D)
    (keys : List (Fin p)) (i : Fin q) :
    @List.lookup (Label p q) D instBEqOfDecidableEq (Sum.inr i)
      (keys.map fun j => (Sum.inl j, value j)) = none := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
    have miss : @BEq.beq (Label p q) instBEqOfDecidableEq (Sum.inr i) (Sum.inl key) = false := by
      change decide ((Sum.inr i : Label p q) = Sum.inl key) = false
      simp
    simpa only [List.map_cons, List.lookup_cons, miss] using ih

theorem table_closed (graph : Graph V F a b) : RoundTrip.PacketClosedTable graph.table := by
  intro item member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact graph.closed index

theorem denote_eq_resume (model : Model F Part α) (graph : Graph V F a b)
    (external : V → α) (input : Fin a × α) :
    Prod.map Sum.inr id <$> graph.denote model input =
      resumeSSA model graph.table external (graph.entry input.1, input.2) := by
  have canonical : Prod.map Sum.inr id <$> graph.denote model input =
      resumeSSA model graph.table (fun _ => model.unit) (graph.entry input.1, input.2) := by
    apply iter_simulation (graph.step model) (Cyclic.stepSSA model graph.table (fun _ => model.unit)) _ id
    rintro ⟨index | port, packet⟩
    · simp only [Graph.step, id_eq, Cyclic.stepSSA, Graph.table, lookup_private _ _ _ (List.mem_finRange _),
        Functor.map_map, Sum.map_inr]
    · simp [Graph.step, Cyclic.stepSSA, Graph.table, lookup_public]
  let start := (graph.entry input.1, input.2, external)
  exact canonical.trans ((resumeRTL_eq_resumeSSA model graph.table (table_closed graph)
    (fun _ => model.unit) start).symm.trans
      (resumeRTL_eq_resumeSSA model graph.table (table_closed graph) external start))

theorem denote_identity (model : Model F Part α) (input : Fin a × α) :
    (Graph.identity (V := V) (F := F) a).denote model input = pure input := by
  unfold Graph.denote
  rw [congrFun (LawfulElgotMonad.fixpoint _) _]
  simp [Graph.identity, Graph.step]

variable [Inhabited V]

theorem denote_link (model : Model F Part α) (left : Graph V F a b) (right : Graph V F b c)
    (input : Fin a × α) :
    (left.link right).denote model input =
      left.denote model input >>= right.denote model := by
  let startRight (packet : Fin b × α) := (right.entry packet.1, packet.2)
  let phase := phased (left.step model) (right.step model) startRight
  let encode : (Label left.locals b × α) ⊕ (Label right.locals c × α) →
      Label (Graph.linkedCount left right) c × α :=
    Sum.elim (Prod.map (left.leftLabel right) id) (Prod.map (left.rightLabel right) id)
  have square (state : (Label left.locals b × α) ⊕ (Label right.locals c × α)) :
      Sum.map id encode <$> flattenBody phase state = (left.link right).step model (encode state) := by
    rcases state with ⟨index | port, packet⟩ | ⟨index | port, packet⟩
    · simp [phase, phased, Graph.step, Graph.link, Graph.linkedBlock, Graph.leftLabel, encode,
        Block.relabel, evalJump_relabel, flattenBody, Elgot.flatten, Bind.kleisliRight, liftPure,
        Function.comp_def]
      rw [Part.map_map, ← Part.bind_eq_bind, ← Part.map_eq_map]
      exact bind_pure_comp (m := Part) _ _
    · simp [phase, phased, Graph.step, Graph.link, Graph.linkedBlock, Graph.leftLabel, encode,
        Graph.handoff, Body.evalJump, Body.exec, Term.exec, Val.eval, upd, flattenBody, Elgot.flatten,
        Bind.kleisliRight, liftPure, startRight]
    · simp [phase, phased, Graph.step, Graph.link, Graph.linkedBlock, Graph.rightLabel, encode,
        Block.relabel, evalJump_relabel, flattenBody, Elgot.flatten, Bind.kleisliRight, liftPure,
        Function.comp_def]
      rw [Part.map_map, ← Part.bind_eq_bind, ← Part.map_eq_map]
      exact bind_pure_comp (m := Part) _ _
    · simp [phase, phased, Graph.step, Graph.link, Graph.rightLabel, encode, flattenBody, Elgot.flatten,
        Bind.kleisliRight, liftPure]
  have transport := iter_simulation (flattenBody phase) ((left.link right).step model) id encode
    square (.inl (left.entry input.1, input.2))
  rw [id_map] at transport
  exact transport.symm.trans (phased_run (left.step model) (right.step model) startRight _)

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link
