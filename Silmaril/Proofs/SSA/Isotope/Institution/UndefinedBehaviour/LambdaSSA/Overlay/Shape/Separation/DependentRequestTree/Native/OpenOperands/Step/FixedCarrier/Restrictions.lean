module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.FixedCarrier.Defs
public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Thms
import Mathlib.Data.List.Nodup
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.CFG.Dependent.Packet.Thms

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree (RequestSignature)
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.InterpreterScript
open CFG.Dependent (Packet pack unpack)
open ScheduleSearch (StateInventory)

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {S : RequestSignature Φ} {R : List Syntax.Ty} {states : Nat}

private theorem answer_mem (replies : ReplyEnumeration S) (stores : StateInventory states)
    (q : Query Φ states) (answer : Syntax.Reply (instrTrg q.op) states) :
    answer ∈ choices replies stores q := by
  cases answer with
  | diverge => simp [choices]
  | fault t => simp [choices, stores.complete t]
  | ret a t =>
    let packed := cast (congrArg Syntax.Payload (S.target q.op)) a
    let reply := unpack packed
    have same : (InterpreterScript.Row.success q reply t).2 = .ret a t := by
      change Syntax.Reply.ret (cast (congrArg Syntax.Payload (S.target q.op).symm) (pack (unpack packed))) t = _
      rw [CFG.Dependent.pack_unpack]
      simp [packed]; rfl
    exact List.mem_cons_of_mem _ (List.mem_append_right _ <| List.mem_flatMap.mpr
      ⟨reply, replies.complete _ reply, List.mem_map.mpr ⟨t, stores.complete t, same⟩⟩)

private theorem restriction_mem (replies : ReplyEnumeration S) (stores : StateInventory states)
    (prim : Syntax.Primitives Φ states) (keys : List (Query Φ states)) :
    (keys.map fun q => (⟨q, q.read prim⟩ : InterpreterScript.Row Φ states)) ∈ assignments replies stores keys := by
  induction keys with
  | nil => simp [assignments]
  | cons q rest ih =>
    exact List.mem_flatMap.mpr ⟨q.read prim, answer_mem replies stores q _, List.mem_map.mpr ⟨_, ih, rfl⟩⟩

private theorem assignment_keys (replies : ReplyEnumeration S) (stores : StateInventory states)
    {keys : List (Query Φ states)} {script : List (InterpreterScript.Row Φ states)}
    (listed : script ∈ assignments replies stores keys) : script.map Sigma.fst = keys := by
  induction keys generalizing script with
  | nil =>
    have empty : script = [] := List.mem_singleton.mp listed
    simp [empty]
  | cons q rest ih =>
    obtain ⟨answer, _, rows⟩ := List.mem_flatMap.mp listed
    obtain ⟨tail, mem, rfl⟩ := List.mem_map.mp rows
    simp [ih mem]

variable [DecidableEq Φ]

theorem assignments_iff (replies : ReplyEnumeration S) (stores : StateInventory states)
    {keys : List (Query Φ states)} (distinct : keys.Nodup) (script : List (InterpreterScript.Row Φ states)) :
    script ∈ assignments replies stores keys ↔
      ∃ prim : Syntax.Primitives Φ states, script = keys.map fun q => ⟨q, q.read prim⟩ := by
  constructor
  · intro listed
    have keys_eq := assignment_keys replies stores listed
    have nodup : (script.map Sigma.fst).Nodup := keys_eq ▸ distinct
    have consistent : Consistent script := by
      intro a ha b hb eq
      obtain rfl := List.inj_on_of_nodup_map nodup ha hb eq
      rfl
    have realized := extend_realizes consistent (fun _ _ _ => .diverge)
    refine ⟨interpret script, ?_⟩
    rw [← keys_eq, List.map_map]
    exact (List.map_id script).symm.trans (List.map_congr_left (fun row mem =>
      Sigma.ext rfl (heq_of_eq (realized row mem).symm)))
  · rintro ⟨prim, rfl⟩
    exact restriction_mem replies stores prim keys

/-- Replaying any total interpreter's finite restriction returns its exact
typed answer at every listed key. -/
theorem restricted (replies : ReplyEnumeration S) (stores : StateInventory states)
    (keys : List (Query Φ states)) (prim : Syntax.Primitives Φ states) :
    ∃ script ∈ assignments replies stores keys,
      ∀ q ∈ keys, q.read (interpret script) = q.read prim := by
  let script := keys.map fun q => (⟨q, q.read prim⟩ : InterpreterScript.Row Φ states)
  have realizes : Realizes prim script := by
    intro row mem
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp mem
    rfl
  have consistent := (feasible_iff script).mp ⟨prim, realizes⟩
  exact ⟨script, restriction_mem replies stores prim keys, fun q mem =>
    extend_realizes consistent _ ⟨q, q.read prim⟩ (List.mem_map_of_mem mem)⟩

omit [DecidableEq Φ] in
theorem query_mem (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (configs : ConfigurationEnumeration R) (stores : StateInventory states)
    (p : Packet R) (s : Fin states) {q : Query Φ states}
    (head : (g.head caller p).query? s = some q) : q ∈ g.queries caller configs stores :=
  List.mem_filterMap.mpr ⟨(p, s), configs.invocation_mem stores _, head⟩

omit [DecidableEq Φ] in
theorem head_execute_congr (g : Table S R) (caller : Syntax.Payload (R.get g.entry))
    (configs : ConfigurationEnumeration R) (stores : StateInventory states) {prim other : Syntax.Primitives Φ states}
    (agree : ∀ q ∈ g.queries caller configs stores, q.read prim = q.read other)
    (p : Packet R) (s : Fin states) :
    (g.head caller p).execute prim s = (g.head caller p).execute other s := by
  cases head : g.head caller p with
  | exit | diverge => rfl
  | request f arg next =>
    let q : InterpreterScript.Query Φ states := ⟨f, arg, s⟩
    have listed := query_mem g caller configs stores p s (q := q) (by rw [head]; rfl)
    have reply : prim f arg s = other f arg s := agree q listed
    simp only [Head.execute, reply]

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.FixedCarrier
