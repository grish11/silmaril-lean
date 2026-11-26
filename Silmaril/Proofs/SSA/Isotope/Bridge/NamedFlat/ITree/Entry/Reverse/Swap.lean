module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Reverse.Profile.Thms

/-! # The destination overwrites the same two registers after the edge swap -/

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Swap

open Silmaril.SSA.LambdaRTL
open LambdaSSA (FiniteCFG Region)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (region Transfer)
open LambdaSSA.Semantics.Interaction.Typed (AtomValues)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open Silmaril.Isotope.Semantics (encodeValue)
open Silmaril.Elgot (iter)
open Silmaril.Elgot.ITree (Tree iterate_fixpoint)

private abbrev SortName := ULift.{1} Unit
private abbrev Reg := ULift.{1} Nat
private abbrev Label := ULift.{1} Nat
private abbrev Event (_ : Type) := Empty
private abbrev Atom := ULift.{1} Nat

private instance : AtomValues SortName := ⟨fun _ => Atom⟩
private instance : HasTy Empty (Ty SortName) := ⟨Empty.elim, Empty.elim⟩
private instance : HasEff Empty Bool := ⟨Empty.elim⟩

private def signature : FlatInstitution.Signature.{0, 0} SortName where
  Instr := Empty

private instance : DecidableEq signature.Instr := fun f => Empty.elim f

private abbrev Runtime := Sigma (AtomValues.carrier (κ := SortName))

attribute [local instance] LambdaSSA.Semantics.Interaction.Typed.typeModel

private def model : Model (κ := SortName) Event signature.Instr where
  instructions :=
    { denote := fun f => Empty.elim f
      denotePure := fun f => Empty.elim f
      denote_pure := fun f => Empty.elim f }
  raw := Empty.elim
  compatible := fun f => Empty.elim f

private def num : Ty SortName := .base ⟨()⟩
private def pairType : Ty SortName := .product num num

private abbrev ports : Interface SortName Reg Label :=
  numberedInterface (.snoc (.snoc .nil num) num) [⟨3⟩, ⟨2⟩] (fun _ => .unit)
private def labels (i : Fin 2) : Label := ⟨i.val⟩
private def fields (_ : Label) : List (Reg × Ty SortName) := [(⟨3⟩, num), (⟨4⟩, num)]

private def flat : FiniteCFG signature.Instr 2 ports.exits.length ports.slots where
  entry := .br 0 (.pair (.bv 1) (.bv 0))
  block i := if i = 0 then
      .let₂ (.bv 0) (.br 1 (.pair (.bv 0) (.bv 1)))
    else
      .let₂ (.bv 0) (.br 3 (.pair .unit (.pair (.bv 1) (.pair (.bv 0) .unit))))

private def edgeProfile (_ : Fin 2) : Ty SortName := pairType

private theorem typed : flat.HasType ports.context edgeProfile
    (LiveOut.exitInterface ports fields).external :=
  NamedFlat.check_sound flat ports.context edgeProfile _ (by decide)

private def lowered : Lowered ports fields flat :=
  (lowerFresh labels ports.context ports.exits ports.external fields flat).get (by decide)

example : (lowerFresh labels ports.context ports.exits ports.external
    (fun k => (fields k).reverse) flat).isNone = true := by decide

-- The versioner saves the two used open fields in its actual support order.
example : ∀ i, lowered.savedRegisters i = [⟨1⟩, ⟨0⟩] := by decide

private def profile := (lowered.synthesizeProfile edgeProfile).get (by decide)

example : ∀ i, profile i = .product pairType (.product num (.product num .unit)) := by decide

private def recompiled : LiveOut.Admission signature ports fields lowered.source :=
  (lowered.reAdmit edgeProfile).get (by decide)

private abbrev Input := Ty.denote (AtomValues.carrier (κ := SortName))
  (Region.packedInputType ports.context.toList)
private def sample : Input := ((PUnit.unit, ⟨7⟩), ⟨9⟩)
private def atom (n : Nat) : Value Runtime := .atom ⟨⟨()⟩, ⟨n⟩⟩
private def ambient : Env Runtime := fun _ => .unit

private def result (first second : Nat) : Transfer Runtime :=
  (0, .inr (.inl (.pair .unit (.pair (atom first) (.pair (atom second) .unit)))))

private def exitBlock : CFG.Block Reg Label signature.Instr :=
  ⟨⟨2⟩, .let2 ⟨3⟩ ⟨4⟩ (.val (.var ⟨2⟩)) (.term (.br ⟨2⟩ .unit))⟩

private theorem loweredBlocks :
    lowered.source.blocks =
      [(⟨0⟩, ⟨⟨2⟩, .let2 ⟨3⟩ ⟨4⟩ (.val (.var ⟨2⟩))
        (.term (.br ⟨1⟩ (.pair (.var ⟨4⟩) (.var ⟨3⟩))))⟩),
       (⟨1⟩, exitBlock)] := rfl

private def naiveFirst : CFG.Block Reg Label signature.Instr :=
  ⟨⟨2⟩, .let2 ⟨3⟩ ⟨4⟩ (.val (.var ⟨2⟩))
    (.let1 ⟨3⟩ (.val (.var ⟨4⟩)) (.let1 ⟨4⟩ (.val (.var ⟨3⟩))
      (.term (.br ⟨1⟩ (.pair (.var ⟨3⟩) (.var ⟨4⟩))))))⟩

private def naive : CFG Reg Label signature.Instr :=
  { lowered.source with
    blocks := (⟨0⟩, naiveFirst) :: lowered.source.blocks.drop 1 }

private theorem takeStep (graph : CFG Reg Label signature.Instr)
    (pending next : CFG.Cyclic.Transfer Reg Label (Value Runtime))
    (h : CFG.Cyclic.step (treeModel model.raw) graph.blocks pending = pure (.inr next)) :
    iter (CFG.Cyclic.step (treeModel model.raw) graph.blocks) pending =
      iter (CFG.Cyclic.step (treeModel model.raw) graph.blocks) next := by
  rw [congrFun (iterate_fixpoint _) pending, h, pure_bind]
  rfl

private theorem finish (graph : CFG Reg Label signature.Instr)
    (out : CFG.Cyclic.Transfer Reg Label (Value Runtime))
    (h : CFG.Cyclic.step (treeModel model.raw) graph.blocks out = pure (.inl out)) :
    iter (CFG.Cyclic.step (treeModel model.raw) graph.blocks) out = pure out := by
  rw [congrFun (iterate_fixpoint _) out, h, pure_bind]
  rfl

private def start : CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
  (⟨0⟩, .pair (atom 7) (atom 9), store ports.names ports.context sample)

private def firstStore : Reg → Value Runtime :=
  upd (upd (upd start.2.2 ⟨2⟩ start.2.1) ⟨3⟩ (atom 7)) ⟨4⟩ (atom 9)

private def mid (second : Nat) (σ : Reg → Value Runtime) :
    CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
  (⟨1⟩, .pair (atom 9) (atom second), σ)

private def exit (packet : CFG.Cyclic.Transfer Reg Label (Value Runtime)) (second : Nat) :
    CFG.Cyclic.Transfer Reg Label (Value Runtime) :=
  (⟨2⟩, .unit, upd (upd (upd packet.2.2 ⟨2⟩ packet.2.1) ⟨3⟩ (atom 9)) ⟨4⟩ (atom second))

private theorem secondStep (first : CFG.Block Reg Label signature.Instr)
    (second : Nat) (σ : Reg → Value Runtime) :
    CFG.Cyclic.step (treeModel model.raw) [(⟨0⟩, first), (⟨1⟩, exitBlock)] (mid second σ) =
      pure (.inr (exit (mid second σ) second)) := by
  change exitBlock.body.exec (treeModel model.raw)
    (fun label value store => pure (Sum.inr (label, value, store)))
    (upd σ ⟨2⟩ (.pair (atom 9) (atom second))) = _
  simp [exitBlock, exit, mid, CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval, treeModel, upd]

set_option maxRecDepth 2048 in
private theorem swap_result :
    LiveOut.observe (P := signature) model ports fields lowered.source sample = pure (result 9 7) := by
  let next := mid 7 firstStore
  let out := exit next 7
  change (iter (CFG.Cyclic.step (treeModel model.raw) lowered.source.blocks) start >>= _) = _
  have first := takeStep lowered.source start next (by
    simp [CFG.Cyclic.step, start, next, mid, firstStore, loweredBlocks, CFG.Body.exec,
      CFG.Term.exec, Op.eval, Val.eval, treeModel, upd])
  have second := takeStep lowered.source next out (by rw [loweredBlocks]; exact secondStep _ _ _)
  rw [first, second, finish _ out rfl, pure_bind]
  rfl

set_option maxRecDepth 2048 in
private theorem naive_result :
    LiveOut.observe (P := signature) model ports fields naive sample = pure (result 9 9) := by
  let overwritten := upd (upd firstStore ⟨3⟩ (atom 9)) ⟨4⟩ (atom 9)
  let next := mid 9 overwritten
  let out := exit next 9
  change (iter (CFG.Cyclic.step (treeModel model.raw) naive.blocks) start >>= _) = _
  have first := takeStep naive start next (by
    simp [CFG.Cyclic.step, start, next, overwritten, mid, firstStore, naive, naiveFirst,
      CFG.Body.exec, CFG.Term.exec, Op.eval, Val.eval, treeModel, upd])
  have second := takeStep naive next out (secondStep naiveFirst 9 overwritten)
  rw [first, second, finish _ out rfl, pure_bind]
  rfl

private def encodedSample : Value Runtime := encodeValue (AtomValues.carrier (κ := SortName))
  (Region.packedInputType ports.context.toList) sample

example : region model.raw (extend ambient encodedSample) (Program.ofCFGEntry typed).code =
    region model.raw (extend ambient encodedSample) recompiled.program.code :=
  lowered.packed_roundTrip model typed recompiled sample ambient

example : region model.raw (extend ambient encodedSample) recompiled.program.code =
    pure (result 9 7) :=
  (recompiled.packed_tree model sample ambient).trans swap_result

example : LiveOut.observe (P := signature) model ports fields lowered.source sample ≠
    LiveOut.observe (P := signature) model ports fields naive sample := by
  rw [swap_result, naive_result]
  intro eq
  have same := congrArg Silmaril.Elgot.ITree.out eq
  change Silmaril.Elgot.ITree.out (Silmaril.Elgot.ITree.ret (result 9 7)) =
    Silmaril.Elgot.ITree.out (Silmaril.Elgot.ITree.ret (result 9 9)) at same
  rw [Silmaril.Elgot.ITree.out_ret, Silmaril.Elgot.ITree.out_ret] at same
  have bad := Silmaril.Elgot.ITree.Visible.ret.inj (Part.some_inj.mp same)
  simp [result, atom] at bad
  exact (by decide : (7 : Nat) ≠ 9) (congrArg ULift.down bad)

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Reverse.Swap
