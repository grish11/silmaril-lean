module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.FlatLetCase.Defs

/-! # A hand-written named cycle swaps its argument before returning -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Tests

open Silmaril.SSA.LambdaRTL
open LambdaSSA (Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (iterate_fixpoint)

private abbrev SortName := ULift.{1} Unit
private abbrev Atom := ULift.{1} Nat
private abbrev Event (_ : Type) := Empty

private inductive Reg : Type 1
  | firstInput | nextInput | testArg | swapArg | current | replacement | retry | live
  deriving DecidableEq

private inductive Label : Type 1
  | test | swap | spare | done
  deriving DecidableEq

private instance : AtomValues SortName := ⟨fun _ => Atom⟩
private instance : HasTy Empty (Ty SortName) := ⟨Empty.elim, Empty.elim⟩
private instance : HasEff Empty Bool := ⟨Empty.elim⟩

private def signature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Empty

private abbrev C := AtomValues.carrier (κ := SortName)
private abbrev Runtime := Sigma C

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private def model : Model (κ := SortName) Event signature.Instr where
  instructions :=
    { denote := fun f => Empty.elim f
      denotePure := fun f => Empty.elim f
      denote_pure := fun f => Empty.elim f }
  raw := Empty.elim
  compatible := fun f => Empty.elim f

private def num : Ty SortName := .base ⟨()⟩
private def choice : Ty SortName := .coprod num num
private def packetType : Ty SortName := .product choice choice

private def names (i : Fin 2) : Reg := if i = 0 then .nextInput else .firstInput

private def ports : Interface SortName Reg Label :=
  ⟨2, .snoc (.snoc .nil choice) choice, names,
    (show ∀ i j : Fin 2, names i = names j → i = j from by decide),
    [.spare, .done], fun _ => .unit⟩

private def fields (label : Label) : List (Reg × Ty SortName) :=
  if label = .done then [(.live, num)] else []

private def source : CFG Reg Label signature.Instr :=
  ⟨.term (.br .test (.pair (.var .firstInput) (.var .nextInput))),
    [(.test, ⟨.testArg, .let2 .current .replacement (.val (.var .testArg))
      (.term (.case (.val (.var .current))
        .retry (.br .swap (.pair (.var .replacement) (.var .current)))
        .live (.br .done .unit)))⟩),
     (.swap, ⟨.swapArg, .term (.br .test (.var .swapArg))⟩)]⟩

private def checked := admit (P := signature) ports fields source (fun _ => packetType)

private def admitted : Admission signature ports fields source := checked.get (by decide +kernel)

-- The exact lexical entry and the backward jump both use a unit saved record.
example : admitted.versioned.table.code.entry =
    .br ⟨0, by decide +kernel⟩ (.pair (.pair (.bv ⟨1, by decide⟩) (.bv ⟨0, by decide⟩)) .unit) :=
  rfl

example : admitted.versioned.table.code.block ⟨1, by decide +kernel⟩ =
    .let₂ (.bv 0) (.br ⟨0, by decide +kernel⟩ (.pair (.bv 1) .unit)) :=
  rfl

-- Attaching an exit read of an ambient entry name breaks packet closure.
example : (admit (P := signature) ports (fun _ => [(.firstInput, choice)])
    source (fun _ => packetType)).isNone = true := by decide +kernel

example : LambdaSSA.Acyclic.FlatLetCase.entryCheck admitted.versioned.table.code = false := by decide +kernel

private abbrev Input := Ty.denote C (Region.packedInputType ports.context.toList)
private def input (first next : Atom) : Input :=
  ((PUnit.unit, Sum.inl first), Sum.inr next)

private def atom (n : Atom) : Value Runtime := .atom ⟨⟨()⟩, n⟩
private def inputStore (x : Input) : Reg → Value Runtime := store ports.names ports.context x
private def result (n : Atom) : Transfer Runtime :=
  (0, .inr (.inl (.pair .unit (.pair (atom n) .unit))))

private def decoded (s : Reg → Value Runtime) (a b : Value Runtime) : Reg → Value Runtime :=
  upd (upd (upd s .testArg (.pair a b)) .current a) .replacement b

private theorem run_cycle (first next : Atom) :
    let s := inputStore (input first next)
    let a := Value.inl (atom first)
    let b := Value.inr (atom next)
    let afterSwap := upd (upd (decoded s a b) .retry (atom first)) .swapArg (.pair b a)
    CFG.Cyclic.run (treeModel model.raw) source s =
      pure (.done, .unit, upd (decoded afterSwap b a) .live (atom next)) := by
  dsimp only
  let s := inputStore (input first next)
  let a := Value.inl (atom first)
  let b := Value.inr (atom next)
  let step := CFG.Cyclic.step (treeModel model.raw) source.blocks
  let entry : CFG.Cyclic.Transfer Reg Label (Value Runtime) := (.test, .pair a b, s)
  let swapped : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
    (.swap, .pair b a, upd (decoded s a b) .retry (atom first))
  let back : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
    (.test, .pair b a, upd swapped.2.2 .swapArg (.pair b a))
  let finish : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
    (.done, .unit, upd (decoded back.2.2 b a) .live (atom next))
  change iter step entry = pure finish
  have forward : step entry = pure (.inr swapped) := by
    change (pure (.pair a b) >>= (treeModel model.raw).unpair >>= _) = _
    rw [pure_bind]
    change (pure (a, b) >>= _) = _
    rw [pure_bind]
    change (pure a >>= (treeModel model.raw).split >>= _) = _
    rw [pure_bind]
    change (pure (Sum.inl (atom first)) >>= _) = _
    rw [pure_bind]
    rfl
  have returnToTest : step swapped = pure (.inr back) := rfl
  have exit : step back = pure (.inr finish) := by
    change (pure (.pair b a) >>= (treeModel model.raw).unpair >>= _) = _
    rw [pure_bind]
    change (pure (b, a) >>= _) = _
    rw [pure_bind]
    change (pure b >>= (treeModel model.raw).split >>= _) = _
    rw [pure_bind]
    change (pure (Sum.inr (atom next)) >>= _) = _
    rw [pure_bind]
    rfl
  rw [congrFun (iterate_fixpoint step) entry, forward, pure_bind]
  change iter step swapped = _
  rw [congrFun (iterate_fixpoint step) swapped, returnToTest, pure_bind]
  change iter step back = _
  rw [congrFun (iterate_fixpoint step) back, exit, pure_bind]
  change iter step finish = _
  rw [congrFun (iterate_fixpoint step) finish, show step finish = pure (.inl finish) from rfl, pure_bind]
  rfl

-- The return uses the replacement payload from the second visit to test.
private theorem observe_cycle (first next : Atom) :
    LiveOut.observe model ports fields source (input first next) = pure (result next) := by
  change (CFG.Cyclic.run (treeModel model.raw) source (inputStore (input first next)) >>= _) = _
  rw [run_cycle, pure_bind]
  rfl

example (first next : Atom) (ambient : Env Runtime) :
    region model.raw
      (extend ambient (encodeValue C (Region.packedInputType ports.context.toList) (input first next)))
      admitted.program.code = pure (result next) :=
  (admitted.packed_tree model (input first next) ambient).trans (observe_cycle first next)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Tests
