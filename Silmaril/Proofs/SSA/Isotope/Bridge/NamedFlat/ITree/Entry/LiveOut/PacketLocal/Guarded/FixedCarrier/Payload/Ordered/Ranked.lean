module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.Payload.Ordered.Ranked.Defs
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked

open Silmaril.Isotope
open Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut
open Silmaril.SSA.LambdaRTL (CFG)
open LambdaSSA.Acyclic.Positional
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet unpack)
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent.Native (Typed withExitUB)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.Payload (Endpoint)
open LambdaSSA.UB.Overlay.Shape.TwoRequest (Tag)
open Recognize (Bit interface requestTypes encodeValue)
open PayloadRecognition (Incoming packetTree roots guardedControl)
open Syntax (StatePrimitives Primitives)

attribute [local instance] requestTypes

universe v

variable {Φ : Type} {σ : Type v}

private def bitFalse : Syntax.Payload Bit := ⟨.inl .unit, .inl .unit⟩
private def bitTrue : Syntax.Payload Bit := ⟨.inr .unit, .inr .unit⟩
private def unitPayload : Syntax.Payload (.unit : Syntax.Ty) := ⟨.unit, .unit⟩

def configurations : ConfigurationEnumeration Incoming :=
  ⟨[⟨0, bitFalse⟩, ⟨0, bitTrue⟩, ⟨1, bitFalse⟩, ⟨1, bitTrue⟩, ⟨2, unitPayload⟩], by
    rintro ⟨i, value, typed⟩
    fin_cases i
    · cases typed with
      | inl h => cases h; exact List.Mem.head _
      | inr h => cases h; exact List.Mem.tail _ (List.Mem.head _)
    · cases typed with
      | inl h => cases h; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      | inr h => cases h; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    · cases typed
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩

def replyPackets : ReplyEnumeration (Recognize.signature Φ) :=
  ⟨fun _ => [⟨0, bitFalse⟩, ⟨0, bitTrue⟩, ⟨1, unitPayload⟩, ⟨2, unitPayload⟩], by
    intro f
    rintro ⟨i, value, typed⟩
    fin_cases i
    · cases typed with
      | inl h => cases h; exact List.Mem.head _
      | inr h => cases h; exact List.Mem.tail _ (List.Mem.head _)
    · cases typed
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    · cases typed
      exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))⟩

theorem output_left_inv : Function.LeftInverse outputEncode outputDecode := by
  intro i
  fin_cases i <;> rfl

theorem output_right_inv : Function.RightInverse outputEncode outputDecode := by
  rintro ⟨tag, value, typed⟩
  fin_cases tag <;>
    cases typed with
    | pair old fields =>
      cases old
      cases fields with
      | pair first rest =>
        cases rest with
        | pair second tail =>
          cases tail
          cases first <;> cases ‹LambdaSSA.UB.Overlay.Shape.ValueTyped Syntax.atomType _ .unit› <;>
            cases second <;> cases ‹LambdaSSA.UB.Overlay.Shape.ValueTyped Syntax.atomType _ .unit› <;> rfl

private def targetShape (bitDest : Fin 3) (i : Fin Incoming.length) : List (Fin Incoming.length) :=
  if i = 0 then [bitDest, 2, 2] else []

private theorem bit_dest (routes : Recognize.TypedRoutes Incoming.get) :
    routes.destination 0 = 0 ∨ routes.destination 0 = 1 := by
  have typed := routes.packet 0
  generalize routes.destination 0 = i at typed ⊢
  fin_cases i <;> simp_all

private theorem unit_dest (routes : Recognize.TypedRoutes Incoming.get) (i : Fin 3)
    (nonzero : i ≠ 0) : routes.destination i = 2 := by
  have typed := routes.packet i
  generalize routes.destination i = j at typed ⊢
  fin_cases i <;> fin_cases j <;> simp_all

private theorem targets_eq (routes : Recognize.TypedRoutes Incoming.get) (op : Φ)
    (bitTag unitTag : Tag) (selected : Tag → Bool) :
    (guardedControl routes op bitTag unitTag selected).targets = targetShape (routes.destination 0) := by
  funext i
  fin_cases i
  · change List.ofFn routes.destination = [routes.destination 0, 2, 2]
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ]
    simp [unit_dest routes (1 : Fin 3) (by decide), unit_dest routes (2 : Fin 3) (by decide)]
  · rfl
  · rfl

theorem control_rank (p : Profile Φ) (op : Φ) (selected : Tag → Bool) :
    let g := (p.endpoint op selected).control
    (g.entryCheck = true ↔ p.routes.destination 0 ≠ 0) ∧
      g.ranks.get g.entry = if p.routes.destination 0 = 0 then none else some 1 := by
  let g := guardedControl p.routes op p.bitTag p.unitTag selected
  change (Rank.checkFrom g.targets [0] = true ↔ p.routes.destination 0 ≠ 0) ∧
    (Rank.rounds g.targets 3).get 0 = if p.routes.destination 0 = 0 then none else some 1
  rw [show g.targets = targetShape (p.routes.destination 0) from targets_eq _ _ _ _ _]
  rcases bit_dest p.routes with bad | good
  · rw [bad]
    decide +kernel
  · rw [good]
    decide +kernel

private theorem exits_after_reply (p : Profile Φ) (op : Φ) (selected : Tag → Bool)
    (ranked : (p.endpoint op selected).control.entryCheck = true)
    (reply : Packet Recognize.Packets) : p.routes.destination reply.1 ≠ 0 := by
  by_cases bit : reply.1 = 0
  · exact bit ▸ (control_rank p op selected).1.mp ranked
  · rw [unit_dest p.routes reply.1 bit]
    decide

private theorem nonentry_exit (p : Profile Φ) (op : Φ) (chosen : Tag → Bool) (caller : Syntax.Payload Bit)
    (a : Packet Incoming) (nonzero : a.1 ≠ 0) :
    ∃ i mark, (p.endpoint op chosen).control.head caller a = .exit i mark := by
  rcases a with ⟨i, payload⟩
  fin_cases i
  · exact (nonzero rfl).elim
  · exact ⟨p.bitTag, chosen p.bitTag, rfl⟩
  · exact ⟨p.unitTag, chosen p.unitTag, rfl⟩

theorem native_observation {κ V K : Type 1} [DecidableEq V] [DecidableEq K]
    {P : FlatInstitution.Signature.{0, 0} κ} [DecidableEq P.Instr]
    {seed first second : V} {names : Fin 5 ≃ K} {source : CFG V K P.Instr}
    {a : Admission P (interface seed names) (fields first second) source}
    {op : P.Instr} {literals : P.Instr → Option Bool} (ck : Checked a op literals)
    (selected : Tag → Bool) (caller : Syntax.Payload Bit) (store : V → Value Runtime)
    (seedValue : store seed = encodeValue ULift.up caller.val)
    (raw : Typed P.Instr [Bit] Outputs) (valid : (ck.profile.endpoint op selected).checkNative raw = true)
    (prim : StatePrimitives P.Instr σ) (s : σ) :
    observeNamedOn source names first second store literals prim s selected =
      LambdaSSA.UB.Overlay.Shape.denote (withExitUB raw selected)
        (Syntax.model prim ((ck.profile.endpoint op selected).control.bindings caller)) s := by
  unfold observeNamedOn
  rw [ck.named_tree selected caller store seedValue]
  let g := ck.profile.endpoint op selected
  exact (observe_roots_on g caller prim (packetTree g caller) (roots g caller)
    (constructorDecoder PayloadType) constructorDecoder_return ⟨0, caller⟩ s).trans
      (g.observe_entry_state raw valid caller prim s).symm

private def destination (p : Profile Φ) (reply : Packet Recognize.Packets) : Packet Incoming :=
  ⟨p.routes.destination reply.1, cast (congrArg Syntax.Payload (p.routes.packet reply.1).symm) reply.2⟩

private theorem first_step (p : Profile Φ) (op : Φ) (selected : Tag → Bool)
    (caller : Syntax.Payload Bit) (prim : StatePrimitives Φ σ) (s : σ) :
    (p.endpoint op selected).observeAt caller prim ⟨0, caller⟩ s =
      match prim op caller s with
      | .ret value t => (p.endpoint op selected).observeAt caller prim (destination p (unpack value)) t
      | .fault t => WithTop.some {Outcome.fault t}
      | .diverge => WithTop.some {Outcome.diverge} := by
  have root : (p.endpoint op selected).control.head caller ⟨0, caller⟩ =
      .request op caller (fun i a => destination p ⟨i, a⟩) := rfl
  rw [(p.endpoint op selected).observe_state_step, root]
  simp only [Head.execute]
  cases prim op caller s <;> rfl

private theorem tail_failure
    (g : Endpoint (Recognize.signature Φ) Incoming PayloadType)
    (h : Endpoint (Recognize.signature Φ) Incoming PayloadType)
    (x : Syntax.Payload (Incoming.get g.control.entry)) (y : Syntax.Payload (Incoming.get h.control.entry))
    (p q : Packet Incoming)
    (terminal : (∃ i b, g.control.head x p = .exit i b) ∨ (∃ j b, h.control.head y q = .exit j b))
    (prim : StatePrimitives Φ σ) (s : σ) (other : Primitives Φ 2) (t : Fin 2)
    (ordinaryDiv : ∀ f a, other f a t = .diverge)
    (bad : ¬ g.observeAt x prim p s ≤ h.observeAt y prim q s) :
    ¬ g.observeAt x other p t ≤ h.observeAt y other q t := by
  rw [g.observe_state_step, h.observe_state_step] at bad ⊢
  cases left : g.control.head x p <;> cases right : h.control.head y q
  all_goals
    rw [left, right] at bad
    simp only [Head.execute] at bad ⊢
  · rename_i i marked j marked'
    cases a : g.control.selected i <;> cases b : h.control.selected j <;>
      simp [a, b, WithTop.coe_le_coe] at bad ⊢
    exact bad
  · rename_i i marked
    cases g.control.selected i <;> simp [WithTop.coe_le_coe]
  · rename_i i marked f arg route
    rw [ordinaryDiv]
    cases g.control.selected i <;> simp [WithTop.coe_le_coe]
  · rename_i j marked
    cases b : h.control.selected j
    · simp [WithTop.coe_le_coe]
    · exact (bad (by simp [b])).elim
  · simp_all
  · simp_all
  · rename_i f arg route j marked
    rw [ordinaryDiv]
    cases b : h.control.selected j
    · simp [WithTop.coe_le_coe]
    · exact (bad (by simp [b])).elim
  · simp_all
  · simp_all

private def replay (reply : CFG.Dependent.Packed Recognize.Packets) : Primitives Φ 2 :=
  fun _ _ s => if s = 0 then .ret reply 1 else .diverge

theorem witness_two [DecidableEq Φ] (p q : Profile Φ) (op op' : Φ) (selected selected' : Tag → Bool)
    (caller : Syntax.Payload Bit) (prim : StatePrimitives Φ σ) (s : σ)
    (ranked : (p.endpoint op selected).control.entryCheck = true ∨ (q.endpoint op' selected').control.entryCheck = true)
    (bad : ¬ (p.endpoint op selected).observeAt caller prim ⟨0, caller⟩ s ≤
      (q.endpoint op' selected').observeAt caller prim ⟨0, caller⟩ s) :
    ∃ (other : Primitives Φ 2) (t : Fin 2),
      ¬ (p.endpoint op selected).observeAt caller other ⟨0, caller⟩ t ≤
        (q.endpoint op' selected').observeAt caller other ⟨0, caller⟩ t := by
  by_cases same : op = op'
  · subst op'
    rw [first_step, first_step] at bad
    cases reply : prim op caller s with
    | fault => exact (bad (by rw [reply])).elim
    | diverge => exact (bad (by rw [reply])).elim
    | ret value t =>
      rw [reply] at bad
      let parsed := unpack (L := Recognize.Packets) value
      have done : (∃ i b, (p.endpoint op selected).control.head caller (destination p parsed) = .exit i b) ∨
          (∃ j b, (q.endpoint op selected').control.head caller (destination q parsed) = .exit j b) :=
        ranked.imp (fun h => nonentry_exit p op selected caller _ (exits_after_reply p op selected h parsed))
          (fun h => nonentry_exit q op selected' caller _ (exits_after_reply q op selected' h parsed))
      have suffix : ∀ f a, replay (Φ := Φ) value f a 1 = .diverge := fun _ _ => rfl
      refine ⟨replay value, 0, ?_⟩
      rw [first_step, first_step]
      exact tail_failure (p.endpoint op selected) (q.endpoint op selected') caller caller
        (destination p parsed) (destination q parsed) done prim t (replay value) 1 suffix bad
  · let separate : Primitives Φ 2 := fun f _ s => if f = op then .fault s else .diverge
    refine ⟨separate, 0, ?_⟩
    rw [first_step, first_step]
    simp [separate, Ne.symm same, WithTop.coe_le_coe]

theorem cutoff_two (p q : Profile Φ) (op op' : Φ) (selected selected' : Tag → Bool)
    (ranked : (p.endpoint op selected).control.entryCheck = true ∨ (q.endpoint op' selected').control.entryCheck = true) :
    (p.endpoint op selected).control.rankedCutoff (q.endpoint op' selected').control = 2 := by
  obtain ⟨leftRank, left⟩ := control_rank p op selected
  obtain ⟨rightRank, right⟩ := control_rank q op' selected'
  unfold Table.rankedCutoff
  rw [left, right]
  by_cases a : p.routes.destination 0 = 0 <;> by_cases b : q.routes.destination 0 = 0
  · exact (ranked.elim (fun ok => leftRank.mp ok a) (fun ok => rightRank.mp ok b)).elim
  all_goals simp [a, b]

section Compare

variable {κ V K : Type 1} [DecidableEq V] [DecidableEq K] {P : FlatInstitution.Signature.{0, 0} κ}
  [DecidableEq P.Instr] {seed first second : V} {names : Fin 5 ≃ K} {source target : CFG V K P.Instr}
  {a : Admission P (interface seed names) (fields first second) source}
  {b : Admission P (interface seed names) (fields first second) target}
  {op op' : P.Instr} {literals : P.Instr → Option Bool} {results : Nat}
  (l : Checked a op literals) (r : Checked b op' literals)
  (caller : Syntax.Payload Bit) (store store' : V → Value Runtime)
  (seedValue : store seed = encodeValue ULift.up caller.val)
  (seedValue' : store' seed = encodeValue ULift.up caller.val)
  (raw raw' : Typed P.Instr [Bit] Outputs) (selected selected' : Tag → Bool)
  (codec : Fin results ≃ Packet Outputs) (replies : ReplyEnumeration (Recognize.signature P.Instr))
  (configs : ConfigurationEnumeration Incoming)
  (valid : (l.profile.endpoint op selected).checkNative raw = true)
  (valid' : (r.profile.endpoint op' selected').checkNative raw' = true)
  (ranked : (l.profile.endpoint op selected).control.entryCheck = true ∨
    (r.profile.endpoint op' selected').control.entryCheck = true)

local notation "g" => l.profile.endpoint op selected
local notation "h" => r.profile.endpoint op' selected'
local notation "verdict" => compareRanked? (some l) (some r) raw raw' selected selected' codec caller replies configs

include valid valid' ranked in
private theorem finite_equiv :
    verdict = some true ↔ ∀ (prim : Primitives P.Instr 2) (s : Fin 2),
      (g).observeAt caller prim ⟨0, caller⟩ s ≤ (h).observeAt caller prim ⟨0, caller⟩ s := by
  have active : ((g).control.entryCheck || (h).control.entryCheck) = true := Bool.or_eq_true_iff.mpr ranked
  change (if (g).control.entryCheck || (h).control.entryCheck then
    (g).checkAllInterpreters? (h) raw raw' codec caller caller replies configs configs
      ((g).control.rankedStores (h).control) else none) = some true ↔ _
  rw [ite_eq_left active, (g).acceptance_iff (h) raw raw' codec caller caller replies configs configs
    ((g).control.rankedStores (h).control) valid valid']
  simp only [(g).observe_entry_state raw valid, (h).observe_entry_state raw' valid']
  rw [cutoff_two l.profile r.profile op op' selected selected' ranked]

include seedValue seedValue' valid valid' ranked in
theorem acceptance_sound (yes : verdict = some true) (prim : StatePrimitives P.Instr σ) (s : σ) :
    observeNamedOn source names first second store literals prim s selected ≤
      observeNamedOn target names first second store' literals prim s selected' := by
  rw [native_observation l selected caller store seedValue raw valid, native_observation r selected' caller store' seedValue' raw' valid',
    (g).observe_entry_state raw valid, (h).observe_entry_state raw' valid']
  by_contra bad
  obtain ⟨other, t, fails⟩ := witness_two l.profile r.profile op op' selected selected' caller prim s ranked bad
  exact fails ((finite_equiv l r caller raw raw' selected selected' codec replies configs valid valid' ranked).mp yes other t)

include seedValue seedValue' valid valid' ranked in
theorem acceptance_iff :
    verdict = some true ↔
      ∀ (σ : Type) (prim : StatePrimitives P.Instr σ) (s : σ),
        observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected' := by
  constructor
  · intro yes σ prim s
    exact acceptance_sound l r caller store store' seedValue seedValue' raw raw' selected selected'
      codec replies configs valid valid' ranked yes prim s
  · intro refines
    apply (finite_equiv l r caller raw raw' selected selected' codec replies configs valid valid' ranked).mpr
    intro prim s
    have agrees := refines (Fin 2) prim s
    rw [native_observation l selected caller store seedValue raw valid, native_observation r selected' caller store' seedValue' raw' valid',
      (g).observe_entry_state raw valid, (h).observe_entry_state raw' valid'] at agrees
    exact agrees

include seedValue seedValue' valid valid' ranked in
theorem rejection_iff :
    verdict = some false ↔
      ∃ (σ : Type) (prim : StatePrimitives P.Instr σ) (s : σ),
        ¬ observeNamedOn source names first second store literals prim s selected ≤
          observeNamedOn target names first second store' literals prim s selected' := by
  classical
  have decided := acceptance_iff l r caller store store' seedValue seedValue' raw raw' selected selected'
    codec replies configs valid valid' ranked
  have active : ((g).control.entryCheck || (h).control.entryCheck) = true := Bool.or_eq_true_iff.mpr ranked
  have supported : (verdict).isSome = true := by
    change (if (g).control.entryCheck || (h).control.entryCheck then
      (g).checkAllInterpreters? (h) raw raw' codec caller caller replies configs configs
        ((g).control.rankedStores (h).control) else none).isSome = true
    simp [active, Endpoint.checkAllInterpreters?, valid, valid']
  cases checked : verdict with
  | none => simp [checked] at supported
  | some answer =>
    simp only [checked, Option.some.injEq] at decided ⊢
    simp only [Bool.eq_false_iff, ne_eq, decided, not_forall]

end Compare


end Silmaril.Proofs.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.FixedCarrier.OrderedLiveOut.Ranked
