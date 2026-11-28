module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.BitFragment.Recursive.Packed.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.Normalization
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive.Tree
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.BitQuery.RequestTree.Readback.Thms

/-! # Reflection and checked histories at the original recursive sources -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.BitFragment (inputStructural)
open Paper.WithAdministrativeReturns.BitFragment.Recursive
open Paper.WithCaseBind.BitQuery (signature Exits model Trace modelCoherent)
open Paper.WithCaseBind.BitQuery.RequestTree
open Paper.WithCaseBind.BitQuery.RequestTree.Readback (eq_of_direct_key)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel typingCoherent_ofType)
open CategoryTheory

local notation "J" => _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli.J (m := Trace)
local notation "M" => types

noncomputable local instance : InstructionModel J M signature.Instr := instructions model
local instance : RegionTypingCoherent (Φ := signature.Instr) J M := modelCoherent

theorem replay_packed (p : Program) :
    p.packed = Paper.Extension.Singleton.ofRegion (Step false) (p.tree.written_typed inputSlots).packExits := by
  have e := replay p id
  rw [← written_input p] at e
  exact Eqv.packed_eq false p.typed (p.tree.written_typed inputSlots) e

set_option backward.isDefEq.respectTransparency false in
theorem observations_eq (p : Program) (g : Bool) : p.observations g = p.tree.outcomes (fun _ => g) := by
  have h := (Paper.Extension.Singleton.ofRegion_eq_iff (Step false)
    p.typed.packExits (p.tree.written_typed inputSlots).packExits).1 (replay_packed p)
  have eq := Eqv.sound false J M (fun _ _ => ⟨rfl, rfl⟩) h
    p.typed.packExits.hasType (p.tree.written_typed inputSlots).packExits.hasType
  have other := written_singleton_outcomes p.tree g
  unfold Program.observations
  unfold denoteSingletonRegion at other ⊢
  rw [eq]
  exact other

set_option backward.isDefEq.respectTransparency false in
private theorem valid_of_packed {p q : Program} (h : p.packed = q.packed) :
    p.endpoint.Valid q.endpoint := by
  have e := (Paper.Extension.Singleton.ofRegion_eq_iff (Step false) p.typed.packExits q.typed.packExits).1 h
  intro V C vcat ccat cart sym prem symPrem sumV sumC distV distC iter elgot K freyd central
    N instr regionCoherent _ shared
  let : InstructionModel K N signature.Instr := instr
  let : RegionTypingCoherent (Φ := signature.Instr) K N := regionCoherent
  exact Eqv.sound false K N shared e p.typed.packExits.hasType q.typed.packExits.hasType

set_option backward.isDefEq.respectTransparency false in
private theorem key_of_valid {p q : Program} (h : p.endpoint.Valid q.endpoint) :
    p.tree.key = q.tree.key := by
  have coherent : Silmaril.Isotope.LetIter.Semantics.Categorical.TypingCoherent
      (ν := Empty) J M signature.Instr :=
    typingCoherent_ofType (ν := Empty) (Empty.elim : Empty → Type) model
  have eq := h J M coherent (fun _ _ => ⟨rfl, rfl⟩)
  change denoteRegion J M p.typed.packExits.hasType = denoteRegion J M q.typed.packExits.hasType at eq
  apply key_of_observations
  intro g
  rw [packed_outcomes, packed_outcomes, ← observations_eq p g, ← observations_eq q g]
  unfold Program.observations denoteSingletonRegion
  rw [eq]

private theorem packed_of_key {p q : Program} (h : p.tree.key = q.tree.key) : p.packed = q.packed := by
  have same : p.tree = q.tree := eq_of_direct_key (direct (p.normalize id)) (direct (q.normalize id)) h
  exact (replay_packed p).trans ((congrArg (fun t : Tree 1 =>
    Paper.Extension.Singleton.ofRegion (Step false) (t.written_typed inputSlots).packExits) same).trans
    (replay_packed q).symm)

theorem packed_eq_iff_key (p q : Program) : p.packed = q.packed ↔ p.tree.key = q.tree.key :=
  ⟨fun h => key_of_valid (valid_of_packed h), packed_of_key⟩

theorem packed_eq_iff_compiled (p q : Program) : p.packed = q.packed ↔ p.CompiledEq q := by
  have law := p.endpoint.valid_iff_compiled inputStructural q.endpoint
  exact ⟨fun h => law.mp (valid_of_packed h), fun h => packed_of_key (key_of_valid (law.mpr h))⟩

set_option backward.isDefEq.respectTransparency false in
theorem separate_some (p q : Program) {w : Difference} (h : p.tree.separate? q.tree = some w) :
    w.history.observation ∈ (if w.fromRight then q else p).observations w.guard ∧
      w.history.observation ∉ (if w.fromRight then p else q).observations w.guard := by
  have separated := Paper.WithCaseBind.BitQuery.RequestTree.separate_some p.tree q.tree h
  obtain ⟨g, side, history⟩ := w
  cases side <;>
    simpa only [Difference.source, Difference.target, Bool.false_eq_true, ite_true, ite_false,
      observations_eq, packed_outcomes] using separated

private def finish {n : Nat} (i : Fin n) : Code 2 n :=
  .ask false (.read i) (.ret 0 0) (.ret 1 0)

private def nested : Program :=
  .letBit
    (.ask false (.read 0)
      (.letUnit (.ret 0 0))
      (.ask true (.read 0) (.letBit (.ret 0 2) (.ret 0 0)) (.ret 0 2)))
    (.ask false (.known true 0 1) (.ret 0 0) (.ret 1 0))

private def directWritten : Program :=
  .ask false (.read 0) (finish 0) (.ask true (.read 0) (finish 2) (finish 2))

private def changed : Program :=
  .ask false (.read 0) (finish 0) (.ask true (.read 0) (finish 2) (finish 1))

example : nested.written ≠ directWritten.written := by
  intro h
  cases h

example : nested.packed = directWritten.packed :=
  (packed_eq_iff_key nested directWritten).2 rfl

example : nested.CompiledEq directWritten :=
  (packed_eq_iff_compiled nested directWritten).1 ((packed_eq_iff_key nested directWritten).2 rfl)

private def laterRight : History :=
  ⟨[event false true (true, false), event true false (true, false), event false true (true, false)], true, false⟩

private def earlierLeft : History :=
  ⟨[event false true (false, false), event false false (false, true)], false, true⟩

example : laterRight.observation ∈ nested.observations true := by
  rw [observations_eq]
  exact (outcomes_history_iff _ _ _).2 ⟨laterRight, by decide, rfl⟩

example : earlierLeft.observation ∈ nested.observations true := by
  rw [observations_eq]
  exact (outcomes_history_iff _ _ _).2 ⟨earlierLeft, by decide, rfl⟩

private def witness : Difference :=
  ⟨false, false, ⟨[event false false (true, true), event true true (true, false),
    event false false (false, false)], false, false⟩⟩

example : witness.history.observation ∈ nested.observations false ∧
    witness.history.observation ∉ changed.observations false :=
  separate_some nested changed (w := witness) rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.BitFragment.Recursive
