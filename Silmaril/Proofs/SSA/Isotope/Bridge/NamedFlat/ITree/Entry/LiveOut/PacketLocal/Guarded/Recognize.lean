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

private def number (names : Fin 5 ≃ K) (p : K × Value α) : Transfer α :=
  ((names.symm p.1).val, p.2)

private def restore (names : Fin 5 ≃ K) (p : Transfer α) : K × Value α :=
  (names (if h : p.1 < 5 then ⟨p.1, h⟩ else 0), p.2)

omit [DecidableEq K] in
private theorem restore_number (names : Fin 5 ≃ K) : Function.LeftInverse
    (restore (α := α) names) (number names) := by
  intro p
  simp [restore, number]

private theorem bind_injective {X Y : Type 1} (f : X → Y) (g : Y → X) (inv : Function.LeftInverse g f) :
    Function.Injective (fun t : Tree E X => t >>= fun x => pure (f x)) := by
  intro l r same
  have lifted := congrArg (fun t : Tree E Y => t >>= fun y => pure (g y)) same
  have inverse (x : X) : g (f x) = x := inv x
  simpa only [bind_assoc, pure_bind, inverse, bind_pure] using lifted

private theorem treeNumber_eq (checked : Checked a opcode (liveOpcodes profile)) (p : K × Value α) :
    treeNumber (labelIndex (lexical).blocks (I).exits) p = number names p := by
  have atName := checked.numbered (names.symm p.1)
  rw [Equiv.apply_symm_apply] at atName
  unfold treeNumber number
  rw [atName]
  rfl

private theorem block_hit (checked : Checked a opcode (liveOpcodes profile)) (i : Fin 3) :
    (lexical).blocks.findFinIdx? (fun item => names (i.castAdd 2) == item.1) =
      some (Fin.cast checked.count.symm i) := by
  have numbered := checked.numbered (i.castAdd 2)
  cases hit : (lexical).blocks.findFinIdx? (fun item => names (i.castAdd 2) == item.1) with
  | some j =>
    simp only [labelIndex, hit, Option.map_some, Option.some.injEq, Fin.val_castAdd] at numbered
    exact congrArg some (Fin.ext numbered)
  | none =>
    cases ext : (I).exits.findFinIdx? (fun exit => names (i.castAdd 2) == exit) with
    | none => simp [labelIndex, hit, ext] at numbered
    | some j =>
      simp [labelIndex, hit, ext, checked.count] at numbered
      omega

private theorem exit_miss (checked : Checked a opcode (liveOpcodes profile)) (i : TwoRequest.Tag) :
    (lexical).blocks.lookup (names (i.natAdd 3)) = none := by
  apply List.lookup_eq_none_iff.mpr
  have noHit : (lexical).blocks.findFinIdx? (fun item => names (i.natAdd 3) == item.1) = none := by
    cases hit : (lexical).blocks.findFinIdx? (fun item => names (i.natAdd 3) == item.1) with
    | none => rfl
    | some j =>
      have numbered := checked.numbered (i.natAdd 3)
      simp only [labelIndex, hit, Option.map_some, Option.some.injEq, Fin.val_castAdd,
        Fin.val_natAdd] at numbered
      have bound := j.isLt
      have count := checked.count
      omega
  simpa [List.findFinIdx?_eq_none_iff, bne] using noHit

private theorem finish_number (names : Fin 5 ≃ K) (i : TwoRequest.Tag) (payload : Value α) :
    treeExitNumber [names 3, names 4] (names (i.natAdd 3), payload) = (i.val, payload) := by
  have distinct : names 4 ≠ names 3 := fun h => (by decide : (4 : Fin 5) ≠ 3) (names.injective h)
  fin_cases i <;> simp [treeExitNumber, treeNumber, List.findFinIdx?_cons, distinct]

private def next (query : Query (signature P.Instr) E) :
    Head (signature P.Instr) Packets → Tree E (Cursor Packets)
  | .exit i _ => pure (atExit i)
  | .request op arg route => query op arg >>= fun r => pure (atBlock (route r.down.1 r.down.2))

private theorem headStep_eq (query : Query (signature P.Instr) E) (h : Head (signature P.Instr) Packets) :
    headStep (B := Transfer α) query h = (next query h >>= fun p => pure (.inr p)) := by
  cases h <;> simp [headStep, next]

private theorem cast_payload_val {A B : Syntax.Ty} (h : A = B) (p : Syntax.Payload A) :
    (cast (congrArg Syntax.Payload h) p).val = p.val := by cases h; rfl

private theorem eval_entry (routes : Routes) (instr : Primitive E P.Instr α) (env : Env α) :
    region instr env (expected opcode routes (liveOpcodes profile)).entry.erase = pure (0, .pair (env 0) .unit) := by
  simp [expected, Flat.erase, Morphism.CaseSSA.erase, region, LambdaSSA.Semantics.Interaction.term]

private theorem eval_loop (routes : Routes) (agrees : QueryAgreement opcode atom query instr)
    (env : Env α) (packet : Syntax.Payload Bit) :
    region instr (extend env (.pair (encodeValue atom packet.val) .unit)) ((expected opcode routes (liveOpcodes profile)).block 0).erase =
      (query opcode packet >>= fun r => pure ((routes.destination r.down.1).val, .pair (encodeValue atom r.down.2.val) .unit)) := by
  simp only [expected, Fin.cases_zero, Flat.erase, Morphism.CaseSSA.erase, region, LambdaSSA.Semantics.Interaction.term, pure_bind]
  change (instr opcode (encodeValue atom packet.val) >>= _) = _
  rw [agrees packet, bind_assoc]
  congr 1
  funext reply
  rw [pure_bind]
  rcases reply with ⟨⟨i, value⟩⟩
  fin_cases i <;> simp [replyValue, pack, extend] <;> rfl

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
  simp only [treeNumber_eq checked] at read
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
    payload (names (index.castAdd 2)) index (block_hit checked index)
  have numberFn : treeNumber (labelIndex (lexical).blocks (I).exits) = (number (α := α) names) :=
    funext (treeNumber_eq checked)
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
      simp only [CFG.Cyclic.stepSSA, pending, encodeCursorWith, atExit, exit_miss checked i]
    change (pure (Sum.inl (exitResult (liveValues profile) i : Transfer α) : Transfer α ⊕ Cursor Packets) >>= _) = mapReturn _ _ pending
    simp only [mapReturn, miss, pure_bind, liftPure, Function.comp_apply, Sum.map_inl, id_eq, Sum.elim_inl]
    have out := finish_number names i (exitPayload (α := α) (liveValues profile i))
    change pure (Sum.inl (exitResult (liveValues profile) i : Transfer α) : Transfer α ⊕ (K × Value α)) =
      pure (.inl (FiniteCFG.packedTreeOutput
        (treeExitNumber [names 3, names 4] (names (i.natAdd 3), exitPayload (liveValues profile i)))))
    rw [out]
    rfl
  · change (headStep query ((G).head caller p) >>= _) =
      mapReturn _ _ (encodeCursorWith (liveValues profile) names atom (atBlock p))
    unfold mapReturn
    rw [headStep_eq, block_eq checked atom query instr input agrees liveAgrees caller p]
    simp only [liftPure, bind_assoc, pure_bind, Function.comp_apply, Sum.map_inr, Sum.elim_inr]

end Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Entry.LiveOut.PacketLocal.Guarded.Recognize
