module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.LiveOut.PacketLocal.Guarded.Recognize.Defs
import Mathlib.Tactic.FinCases

public section

namespace Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize

open Silmaril.Isotope Silmaril.Isotope.Bridge.NamedFlat Silmaril.Isotope.Bridge.NamedFlat.Entry
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded
open Silmaril.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.Elgot (mapReturn liftPure)
open Silmaril.Elgot.ITree (Tree)
open LambdaSSA (Flat FiniteCFG)
open LambdaSSA.Semantics (Env extend)
open LambdaSSA.Semantics.Interaction (Primitive Transfer region term)
open LambdaSSA.Semantics.Interaction.Typed.Ordered
open LambdaSSA.UB.Overlay.Shape
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.CFG.Dependent (Packet pack)
open LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands (Head Table)

attribute [local instance] requestTypes

variable {κ V K α : Type 1} [DecidableEq V] [DecidableEq K]
  {P : FlatInstitution.Signature.{0, 0} κ} {E : Type → Type}
  {seed : V} {names : Fin 5 ≃ K} {source : CFG V K P.Instr} {opcode : P.Instr}

local notation "I" => (interface (κ := κ) seed names)

variable {fields : K → List (V × Ty κ)} {a : Admission P (interface (κ := κ) seed names) fields source}
  {profile : LiveProfile P.Instr}
  (checked : Checked a opcode (liveOpcodes profile)) (atom : Unit → α)
  (query : Query (signature P.Instr) E) (instr : Primitive E P.Instr α)
  (input : V × Nat → Value α)

local notation "lexical" => a.versioned.source
local notation "m" => treeModel instr

private theorem entryAt {F : Type} {n d : Nat} (graph : CFG V K F) (exits : List K)
    (captures : Fin n → V) (count : graph.blocks.length = d)
    {target : FiniteCFG F d exits.length n} (accepted : elaborateAt graph exits captures d count = some target)
    (prim : Primitive E F α) (store : V → Value α) (env : Env α)
    (inputs : ∀ i, env i.val = store (captures i)) :
    (graph.entry.evalJump (treeModel prim) store >>= fun p => pure (treeNumber (labelIndex graph.blocks exits) p)) =
      region prim env target.entry.erase := by
  subst d
  exact Silmaril.Isotope.Bridge.NamedFlat.entry_tree prim graph exits captures ((elaborateAt_eq _ _ _).symm.trans accepted)
    store env inputs

private theorem stepAt {F : Type} {n d : Nat} (graph : CFG V K F) (exits : List K)
    (captures : Fin n → V) (count : graph.blocks.length = d)
    {target : FiniteCFG F d exits.length n} (accepted : elaborateAt graph exits captures d count = some target)
    (prim : Primitive E F α) (store : V → Value α) (env : Env α) (payload : Value α)
    (label : K) (i : Fin d)
    (hit : graph.blocks.findFinIdx? (fun item => label == item.1) = some (Fin.cast count.symm i)) :
    (CFG.Cyclic.stepSSA (treeModel prim) graph.blocks store (label, payload) >>=
      fun s => pure (s.map id (treeNumber (labelIndex graph.blocks exits)))) =
      (region prim (extend env payload) (target.block i).erase >>= fun p => pure (.inr p)) := by
  subst d
  exact Silmaril.Isotope.Bridge.NamedFlat.step_tree prim graph exits captures ((elaborateAt_eq _ _ _).symm.trans accepted)
    label i hit store env payload

private def number {d : Nat} (names : Fin (d + 2) ≃ K) (p : K × Value α) : Transfer α :=
  ((names.symm p.1).val, p.2)


omit [DecidableEq K] in
private theorem restore_number {d : Nat} (names : Fin (d + 2) ≃ K) : Function.LeftInverse
    (restoreAt (α := α) names) (number names) := by
  intro p
  simp [restoreAt, number]

private theorem bind_injective {X Y : Type 1} (f : X → Y) (g : Y → X) (inv : Function.LeftInverse g f) :
    Function.Injective (fun t : Tree E X => t >>= fun x => pure (f x)) := by
  intro l r same
  have lifted := congrArg (fun t : Tree E Y => t >>= fun y => pure (g y)) same
  have inverse (x : X) : g (f x) = x := inv x
  simpa only [bind_assoc, pure_bind, inverse, bind_pure] using lifted

section Numbered

variable {d : Nat} {keys : Fin (d + 2) ≃ K}
  {admission : Admission P (numberedInterface (κ := κ) seed keys) fields source}
local notation "J" => (numberedInterface (κ := κ) seed keys)
local notation "g" => admission.versioned.source

private theorem treeNumber_eq {code : FiniteCFG P.Instr d 2 1} (readback : NumberedReadback admission code) (p : K × Value α) :
    treeNumber (labelIndex (g).blocks (J).exits) p = number keys p := by
  have atName := readback.numbered (keys.symm p.1)
  rw [Equiv.apply_symm_apply] at atName
  unfold treeNumber number
  rw [atName]
  rfl

private theorem block_hit {code : FiniteCFG P.Instr d 2 1} (readback : NumberedReadback admission code) (i : Fin d) :
    (g).blocks.findFinIdx? (fun item => keys (i.castAdd 2) == item.1) =
      some (Fin.cast readback.count.symm i) := by
  have numbered := readback.numbered (i.castAdd 2)
  cases hit : (g).blocks.findFinIdx? (fun item => keys (i.castAdd 2) == item.1) with
  | some j =>
    simp only [labelIndex, hit, Option.map_some, Option.some.injEq, Fin.val_castAdd] at numbered
    exact congrArg some (Fin.ext numbered)
  | none =>
    cases ext : (J).exits.findFinIdx? (fun exit => keys (i.castAdd 2) == exit) with
    | none => simp [labelIndex, hit, ext] at numbered
    | some j =>
      simp [labelIndex, hit, ext, readback.count] at numbered
      omega

private theorem exit_miss {code : FiniteCFG P.Instr d 2 1} (readback : NumberedReadback admission code) (i : TwoRequest.Tag) :
    (g).blocks.lookup (keys (i.natAdd d)) = none := by
  apply List.lookup_eq_none_iff.mpr
  have noHit : (g).blocks.findFinIdx? (fun item => keys (i.natAdd d) == item.1) = none := by
    cases hit : (g).blocks.findFinIdx? (fun item => keys (i.natAdd d) == item.1) with
    | none => rfl
    | some j =>
      have numbered := readback.numbered (i.natAdd d)
      simp only [labelIndex, hit, Option.map_some, Option.some.injEq, Fin.val_castAdd,
        Fin.val_natAdd] at numbered
      have bound := j.isLt
      have count := readback.count
      omega
  simpa [List.findFinIdx?_eq_none_iff, bne] using noHit

private theorem finish_number {d : Nat} (names : Fin (d + 2) ≃ K) (i : TwoRequest.Tag) (payload : Value α) :
    treeExitNumber [names ((0 : Fin 2).natAdd d), names ((1 : Fin 2).natAdd d)]
      (names (i.natAdd d), payload) = (i.val, payload) := by
  have distinct : names ((1 : Fin 2).natAdd d) ≠ names ((0 : Fin 2).natAdd d) := by
    intro eq
    have value := congrArg Fin.val (names.injective eq)
    simp only [Fin.val_natAdd, Fin.val_zero, Fin.val_one] at value
    omega
  fin_cases i <;> simp [treeExitNumber, treeNumber, List.findFinIdx?_cons, distinct]

end Numbered

private def next (query : Query (signature P.Instr) E) :
    Head (signature P.Instr) Packets → Tree E (Cursor Packets)
  | .exit i _ => pure (atExit i)
  | .diverge => Silmaril.Elgot.ITree.diverge
  | .request op arg route => query op arg >>= fun r => pure (atBlock (route r.down.1 r.down.2))

private theorem headStep_eq (query : Query (signature P.Instr) E) (h : Head (signature P.Instr) Packets) :
    headStep (B := Transfer α) query h = (next query h >>= fun p => pure (.inr p)) := by
  cases h with
  | diverge => exact (Silmaril.Elgot.ITree.diverge_bind _).symm
  | exit | request => simp [headStep, next]

private theorem cast_payload_val {A B : Syntax.Ty} (h : A = B) (p : Syntax.Payload A) :
    (cast (congrArg Syntax.Payload h) p).val = p.val := by cases h; rfl

private theorem eval_entry (routes : Routes) (instr : Primitive E P.Instr α) (env : Env α) :
    region instr env (expected opcode routes (liveOpcodes profile)).entry.erase = pure (0, .pair (env 0) .unit) := by
  simp [expected, Flat.erase, Morphism.CaseSSA.erase, region, LambdaSSA.Semantics.Interaction.term]

theorem eval_request {d : Nat} (destination : Fin 3 → Fin d) (fallback : Fin d) (agrees : QueryAgreement opcode atom query instr)
    (env : Env α) (packet : Syntax.Payload Bit) :
    region instr (extend env (.pair (encodeValue atom packet.val) .unit)) (requestAt opcode destination fallback).erase =
      (query opcode packet >>= fun r => pure ((destination r.down.1).val, .pair (encodeValue atom r.down.2.val) .unit)) := by
  simp only [requestAt, Flat.erase, Morphism.CaseSSA.erase, region, LambdaSSA.Semantics.Interaction.term, pure_bind]
  change (instr opcode (encodeValue atom packet.val) >>= _) = _
  rw [agrees packet, bind_assoc]
  congr 1
  funext reply
  rw [pure_bind]
  rcases reply with ⟨⟨i, value⟩⟩
  fin_cases i <;> simp [replyValue, pack, extend] <;> rfl

private theorem eval_loop (routes : Routes) (agrees : QueryAgreement opcode atom query instr)
    (env : Env α) (packet : Syntax.Payload Bit) :
    region instr (extend env (.pair (encodeValue atom packet.val) .unit))
      ((expected opcode routes (liveOpcodes profile)).block 0).erase =
      (query opcode packet >>= fun r => pure ((routes.destination r.down.1).val,
        .pair (encodeValue atom r.down.2.val) .unit)) :=
  eval_request atom query instr routes.destination 2 agrees env packet

omit [DecidableEq K] in
private theorem eval_exit (profile : LiveProfile P.Instr) (agrees : LiveAgreement profile instr)
    (env : Env α) (incoming : Value α) (label : Fin 5) (i : TwoRequest.Tag) :
    region instr (extend env (.pair incoming .unit)) (exitRow label (liveOpcodes profile i)).erase =
      pure (label.val, exitPayload (liveValues profile i)) := by
  cases h : profile i with
  | none =>
    simp [h, liveOpcodes, liveValues, exitRow, exitPayload, region, LambdaSSA.Semantics.Interaction.term,
      extend, Flat.erase, Morphism.CaseSSA.erase]
  | some action =>
    obtain ⟨f, bit⟩ := action
    simp [h, liveOpcodes, liveValues, exitRow, exitPayload, region, LambdaSSA.Semantics.Interaction.term,
      extend, Flat.erase, Morphism.CaseSSA.erase, agrees i f bit h]

omit [DecidableEq K] in
private theorem eval_row (routes : Routes) (agrees : QueryAgreement opcode atom query instr)
    (liveAgrees : LiveAgreement profile instr)
    (env : Env α) (caller : Syntax.Payload Bit) (p : Packet Packets) :
    region instr (extend env (.pair (encodeValue atom p.2.val) .unit)) ((expected opcode routes (liveOpcodes profile)).block p.1).erase =
      (next query ((guardedTable opcode routes).head caller p) >>= fun t => pure (number names (encodeCursorWith (liveValues profile) names atom t))) := by
  rcases p with ⟨i, payload⟩
  fin_cases i
  · change Syntax.Payload Bit at payload
    change region instr (extend env (.pair (encodeValue atom payload.val) .unit)) ((expected opcode routes (liveOpcodes profile)).block 0).erase = _
    rw [eval_loop atom query instr routes agrees env payload]
    change _ = ((query opcode payload >>= fun r => pure (atBlock (R := Packets)
      ⟨routes.destination r.down.1, cast (congrArg Syntax.Payload (routes.packet r.down.1).symm) r.down.2⟩)) >>= _)
    erw [bind_assoc]
    congr 1
    funext reply
    change ULift.{1} (Packet Packets) at reply
    rw [pure_bind]
    simp [encodeCursorWith, atBlock, number]
    exact congrArg (fun value => (pure ((routes.destination reply.down.1).val,
      .pair (encodeValue atom value) .unit) : Tree E (Transfer α)))
      (cast_payload_val (routes.packet reply.down.1).symm reply.down.2).symm
  · change region instr (extend env (.pair (encodeValue atom payload.val) .unit))
      (exitRow 3 (liveOpcodes profile 0)).erase = (pure (atExit 0) >>= _)
    rw [eval_exit instr profile liveAgrees]
    simp [number, encodeCursorWith, atExit]
  · change region instr (extend env (.pair (encodeValue atom payload.val) .unit))
      (exitRow 4 (liveOpcodes profile 1)).erase = (pure (atExit 1) >>= _)
    rw [eval_exit instr profile liveAgrees]
    simp [number, encodeCursorWith, atExit]

local notation "code" => (expected opcode checked.routes (liveOpcodes profile))
local notation "G" => (guardedTable opcode checked.routes)

include checked

private theorem entry_eq (caller : Syntax.Payload Bit) (seedValue : input (seed, 0) = encodeValue atom caller.val) :
    (lexical).entry.evalJump m input = pure (encodeCursorWith (liveValues profile) names atom (atBlock ⟨0, caller⟩)) := by
  let env : Env α := fun _ => encodeValue atom caller.val
  have read := entryAt lexical (I).exits (I).version.names checked.count checked.accepted instr input env
    (fun _ => seedValue.symm)
  simp only [treeNumber_eq (checked.readback)] at read
  apply bind_injective (E := E) (number names) (restore names) (restore_number names)
  change ((lexical).entry.evalJump m input >>= fun p => pure (number names p)) = _
  rw [read]
  exact (eval_entry checked.routes instr env).trans (by simp [env, encodeCursorWith, atBlock, number])

private theorem block_eq (agrees : QueryAgreement opcode atom query instr)
    (liveAgrees : LiveAgreement profile instr)
    (caller : Syntax.Payload Bit) (p : Packet Packets) :
    CFG.Cyclic.stepSSA m (lexical).blocks input (encodeCursorWith (liveValues profile) names atom (atBlock p)) =
      (next query ((G).head caller p) >>= fun t => pure (.inr (encodeCursorWith (liveValues profile) names atom t))) := by
  let index : Fin 3 := p.1
  let payload := Value.pair (encodeValue atom p.2.val) .unit
  let env : Env α := fun _ => .unit
  have read := stepAt lexical (I).exits (I).version.names checked.count checked.accepted instr input env
    payload (names (index.castAdd 2)) index (block_hit (checked.readback) index)
  have numberFn : treeNumber (labelIndex (lexical).blocks (I).exits) = (number (α := α) names) :=
    funext (treeNumber_eq (checked.readback))
  rw [numberFn] at read
  apply bind_injective (E := E) (Sum.map id (number names)) (Sum.map id (restore names)) (by
    intro out
    cases out with
    | inl => rfl
    | inr p => exact congrArg Sum.inr (restore_number names p))
  change (_ >>= fun s => pure (Sum.map id (number names) s)) =
    ((next query ((G).head caller p) >>= fun t => pure (Sum.inr (encodeCursorWith (liveValues profile) names atom t))) >>=
      fun s => pure (Sum.map id (number names) s))
  rw [show CFG.Cyclic.stepSSA m (lexical).blocks input (encodeCursorWith (liveValues profile) names atom (atBlock p)) >>=
      (fun s => pure (s.map id (number names))) = _ from read]
  change (region instr (extend env (.pair (encodeValue atom p.2.val) .unit)) ((code).block p.1).erase
    >>= fun out => pure (Sum.inr out : (K × Value α) ⊕ Transfer α)) = _
  rw [eval_row (names := names) atom query instr checked.routes agrees liveAgrees env caller p]
  simp only [bind_assoc, pure_bind, Sum.map_inr]

theorem entry (caller : Syntax.Payload Bit) (seedValue : input (seed, 0) = encodeValue atom caller.val) :
    (lexical).entry.evalJump m input = pure (encodeCursorWith (liveValues profile) names atom (atBlock ⟨(G).entry, caller⟩)) :=
  entry_eq checked atom instr input caller seedValue

theorem localStep (agrees : QueryAgreement opcode atom query instr)
    (liveAgrees : LiveAgreement profile instr) (caller : Syntax.Payload Bit)
    (state : Cursor Packets) :
    (step G caller query (exitResult (liveValues profile)) state >>= liftPure (Sum.map id (encodeCursorWith (liveValues profile) names atom))) =
      mapReturn (CFG.Cyclic.stepSSA m (lexical).blocks input)
        (liftPure fun p => FiniteCFG.packedTreeOutput (treeExitNumber (I).exits p)) (encodeCursorWith (liveValues profile) names atom state) := by
  rcases state with ⟨i | p⟩
  · let pending := encodeCursorWith (liveValues profile) names atom (atExit i)
    have miss : CFG.Cyclic.stepSSA m (lexical).blocks input pending = pure (.inl pending) := by
      simp only [CFG.Cyclic.stepSSA, pending, encodeCursorWith, atExit, exit_miss (checked.readback) i]
    change (pure (Sum.inl (exitResult (liveValues profile) i : Transfer α) : Transfer α ⊕ Cursor Packets) >>= _) = mapReturn _ _ pending
    simp only [mapReturn, miss, pure_bind, liftPure, Function.comp_apply, Sum.map_inl, id_eq, Sum.elim_inl]
    have out := finish_number names i (exitPayload (α := α) (liveValues profile i))
    change pure (Sum.inl (exitResult (liveValues profile) i : Transfer α) : Transfer α ⊕ (K × Value α)) =
      pure (.inl (FiniteCFG.packedTreeOutput
        (treeExitNumber (I).exits (names (i.natAdd 3), exitPayload (liveValues profile i)))))
    rw [out]
    rfl
  · change (headStep query ((G).head caller p) >>= _) =
      mapReturn _ _ (encodeCursorWith (liveValues profile) names atom (atBlock p))
    unfold mapReturn
    rw [headStep_eq, block_eq checked atom query instr input agrees liveAgrees caller p]
    simp only [liftPure, bind_assoc, pure_bind, Function.comp_apply, Sum.map_inr, Sum.elim_inr]

omit checked

section Readback

variable {d : Nat} {keys : Fin (d + 2) ≃ K}
  {admission : Admission P (numberedInterface (κ := κ) seed keys) fields source}
  {target : FiniteCFG P.Instr d 2 1} (readback : NumberedReadback admission target)
local notation "J" => (numberedInterface (κ := κ) seed keys)
local notation "g" => admission.versioned.source
include readback

theorem numbered_entry_eval (env : Env α) (agrees : ∀ i, env i.val = input ((J).version.names i)) :
    ((g)).entry.evalJump m input =
      (region instr env target.entry.erase >>= fun p => pure (restoreAt keys p)) := by
  have read := entryAt (g) (J).exits (J).version.names readback.count readback.accepted instr input env agrees
  simp only [treeNumber_eq readback] at read
  have decoded := congrArg (fun t : Tree E (Transfer α) => t >>= fun p => pure (restoreAt keys p)) read
  have inverse (q : K × Value α) : restoreAt keys (number keys q) = q := restore_number keys q
  simpa only [bind_assoc, pure_bind, inverse, bind_pure] using! decoded

theorem numbered_block_eval (env : Env α) (p : Value α) (i : Fin d) :
    CFG.Cyclic.stepSSA m ((g)).blocks input (keys (i.castAdd 2), p) =
      (region instr (extend env p) (target.block i).erase >>= fun q => pure (.inr (restoreAt keys q))) := by
  have read := stepAt (g) (J).exits (J).version.names readback.count readback.accepted instr input env
    p (keys (i.castAdd 2)) i (block_hit readback i)
  have numberFn : treeNumber (labelIndex ((g)).blocks (J).exits) = (number (α := α) keys) :=
    funext (treeNumber_eq readback)
  rw [numberFn] at read
  have decoded := congrArg (fun t : Tree E ((K × Value α) ⊕ Transfer α) =>
    t >>= fun q => pure (q.map id (restoreAt keys))) read
  have inverse (q : (K × Value α) ⊕ (K × Value α)) :
      (q.map id (number keys)).map id (restoreAt keys) = q := by
    cases q with
    | inl => rfl
    | inr p => exact congrArg Sum.inr (restore_number keys p)
  simpa only [bind_assoc, pure_bind, inverse, bind_pure, Sum.map_inr] using! decoded

theorem numbered_exit_eval (p : Value α) (i : TwoRequest.Tag) :
    mapReturn (CFG.Cyclic.stepSSA m ((g)).blocks input)
      (liftPure fun t => FiniteCFG.packedTreeOutput (treeExitNumber (J).exits t)) (keys (i.natAdd d), p) =
      pure (.inl (FiniteCFG.packedTreeOutput (i.val, p))) := by
  simp [mapReturn, liftPure, CFG.Cyclic.stepSSA, exit_miss readback i, finish_number]

end Readback

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize
