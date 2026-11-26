module

public import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.Defs
import Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.Simulation.PacketCopy
import Mathlib.Data.Finset.Card

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.CopyChain

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.CopyChain

variable {V F : Type} [DecidableEq V] {a b c d : Nat}

/-- Scanning a stage consumes only private labels in its embedded range. -/
private theorem inspect_embed (stage : Graph V F a b) (linked : Graph V F c d)
    (embed : Fin stage.locals → Fin linked.locals) (injective : Function.Injective embed)
    (rename : Label stage.locals b → Label linked.locals d)
    (privateLabel : ∀ i, rename (.inl i) = .inl (embed i))
    (next_map : ∀ i, next? linked (embed i) = (next? stage i).map rename)
    (finish : Fin b → Outcome linked.locals d)
    (baseline available : Finset (Fin linked.locals)) (remaining : Finset (Fin stage.locals))
    (exitReady : ∀ (pool : Finset (Fin linked.locals)),
      (∀ j, (∀ i, embed i ≠ j) → (j ∈ pool ↔ j ∈ baseline)) →
      ∀ port, inspect linked pool (rename (.inr port)) = finish port)
    (inside : ∀ i, embed i ∈ available ↔ i ∈ remaining)
    (outside : ∀ j, (∀ i, embed i ≠ j) → (j ∈ available ↔ j ∈ baseline))
    (start : Label stage.locals b) :
    inspect linked available (rename start) =
      (inspect stage remaining start).continueWith embed finish := by
  induction remaining using Finset.strongInductionOn generalizing available start with
  | _ remaining ih =>
    cases start with
    | inr port =>
      rw [inspect.eq_def stage remaining]
      exact exitReady available outside port
    | inl i =>
      rw [privateLabel, inspect.eq_def stage remaining, inspect.eq_def linked available]
      by_cases fresh : i ∈ remaining
      · simp only [dite_eq_left fresh, dite_eq_left ((inside i).mpr fresh), next_map]
        cases edge : next? stage i with
        | none => rfl
        | some next =>
          apply ih (remaining.erase i) (Finset.erase_ssubset fresh) (available.erase (embed i))
          · intro j
            simp only [Finset.mem_erase, inside]
            exact and_congr (not_congr injective.eq_iff) Iff.rfl
          · intro j disjoint
            exact (Finset.mem_erase.trans (and_iff_right (Ne.symm (disjoint i)))).trans (outside j disjoint)
      · simp only [dite_eq_right fresh, dite_eq_right (fun mem => fresh ((inside i).mp mem))]
        rfl

variable [Inhabited V] (left : Graph V F a b) (right : Graph V F b c)

private abbrev leftIndex (i : Fin left.locals) : Fin (left.link right).locals :=
  (i.castAdd b).castAdd right.locals

private abbrev rightIndex (i : Fin right.locals) : Fin (left.link right).locals :=
  i.natAdd (left.locals + b)

private abbrev handoffIndex (port : Fin b) : Fin (left.link right).locals :=
  (port.natAdd left.locals).castAdd right.locals

private theorem left_ne_right (i : Fin left.locals) (j : Fin right.locals) :
    leftIndex left right i ≠ rightIndex left right j := by
  intro same
  have vals : i.val = left.locals + b + j.val := congrArg Fin.val same
  omega

private theorem left_ne_handoff (i : Fin left.locals) (port : Fin b) :
    leftIndex left right i ≠ handoffIndex left right port := by
  intro same
  have vals : i.val = left.locals + port.val := congrArg Fin.val same
  omega

private theorem right_ne_handoff (i : Fin right.locals) (port : Fin b) :
    rightIndex left right i ≠ handoffIndex left right port := by
  intro same
  have vals : left.locals + b + i.val = left.locals + port.val := congrArg Fin.val same
  omega

private theorem next_left (i : Fin left.locals) :
    next? (left.link right) (leftIndex left right i) = (next? left i).map (left.leftLabel right) := by
  simp only [next?, Graph.link, Graph.linkedBlock, Fin.addCases_left, Block.relabel,
    Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy.target_relabel]

private theorem next_right (i : Fin right.locals) :
    next? (left.link right) (rightIndex left right i) = (next? right i).map (left.rightLabel right) := by
  simp only [next?, Graph.link, Graph.linkedBlock, Fin.addCases_right, Block.relabel,
    Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.PacketCopy.target_relabel]

private theorem next_handoff (port : Fin b) :
    next? (left.link right) (handoffIndex left right port) = some (left.rightLabel right (right.entry port)) := by
  simp [next?, Graph.link, Graph.linkedBlock, Graph.handoff, PacketCopy.target?]

private theorem inspect_right (available : Finset (Fin (left.link right).locals))
    (ready : ∀ i, rightIndex left right i ∈ available) (port : Fin b) :
    inspect (left.link right) available (left.rightLabel right (right.entry port)) =
      (entryOutcome right port).continueWith (rightIndex left right) Outcome.returns := by
  refine inspect_embed right (left.link right) (rightIndex left right) ?_ (left.rightLabel right) ?_
    (next_right left right) Outcome.returns available available Finset.univ ?_ ?_ ?_ (right.entry port)
  · intro i j same
    apply Fin.ext
    have vals : left.locals + b + i.val = left.locals + b + j.val := congrArg Fin.val same
    omega
  · intro i
    rfl
  · intro pool _ exit
    change inspect (left.link right) pool (.inr exit) = .returns exit
    rw [inspect.eq_def]
  · intro i
    simp [ready i]
  · exact fun _ _ => Iff.rfl

theorem entry_link (input : Fin a) :
    entryOutcome (left.link right) input =
      (entryOutcome left input).continueWith (fun i => (i.castAdd b).castAdd right.locals) (fun mid =>
        (entryOutcome right mid).continueWith (fun i => i.natAdd (left.locals + b)) Outcome.returns) := by
  refine inspect_embed left (left.link right) (leftIndex left right) ?_ (left.leftLabel right) ?_
    (next_left left right) _ Finset.univ Finset.univ Finset.univ ?_ ?_ ?_ (left.entry input)
  · intro i j same
    exact Fin.ext (congrArg (fun index : Fin (left.link right).locals => index.val) same)
  · intro i
    rfl
  · intro pool outside mid
    change inspect (left.link right) pool (.inl (handoffIndex left right mid)) = _
    have ready : handoffIndex left right mid ∈ pool :=
      (outside _ (fun i => left_ne_handoff left right i mid)).mpr (Finset.mem_univ _)
    rw [inspect.eq_def]
    simp only [dite_eq_left ready, next_handoff left right mid]
    apply inspect_right left right
    intro i
    exact Finset.mem_erase.mpr ⟨right_ne_handoff left right i mid,
      (outside _ (fun j => left_ne_right left right j i)).mpr (Finset.mem_univ _)⟩
  · intro i
    simp
  · exact fun _ _ => Iff.rfl

end Silmaril.Proofs.SSA.LambdaRTL.CFG.Cyclic.Link.CopyChain
