module

public import Silmaril.Machine.SqliteVfs.ReadSplit.Fragments.Defs
import Silmaril.Machine.SqliteVfs.ReadSplit.Thms

@[expose] public section

namespace Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.ReadSplit.Fragments
open Silmaril.Machine.SqliteVfs.ReadSplit (combine range_split reads_split)

theorem read_fragments_trace {State : Type} (step : Handler State) (handle : Handle)
    (state : State) (offset count : Nat) (rest : List Nat) :
    let result := readFragments step handle state offset count rest
    Trace.Valid step state result.trace result.file ∧
      result.trace.map Exchange.request = fragmentRequests handle offset (count :: rest) := by
  induction rest generalizing state offset count with
  | nil => exact ⟨.cons rfl (.nil _), rfl⟩
  | cons next rest ih =>
    obtain ⟨valid, requests⟩ := ih (step state (.read handle offset count)).2 (offset + count) next
    refine ⟨.cons rfl valid, ?_⟩
    rw [readFragments]
    simp only [List.map_cons, requests, fragmentRequests]

private theorem combine_empty {bytes : Bytes} {offset count : Nat} {reply : ReadReply}
    (result : ReadResult bytes offset count reply) : combine (.ok []) reply = some reply := by
  obtain ⟨buffer, rfl, _⟩ := result
  split <;> rfl

private theorem fragments_agree {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadLaw step view) (state : State) (handle : Handle)
    (offset count : Nat) (rest : List Nat) (countPositive : 0 < count)
    (restPositive : ∀ n ∈ rest, 0 < n) (admitted : ReadRange offset (count + rest.sum : Nat))
    (live : ((view state).mode handle).isNone = false) :
    let result := readFragments step handle state offset count rest
    let whole := step state (.read handle offset (count + rest.sum : Nat))
    result.reply = some whole.1 ∧ view result.file = view whole.2 := by
  induction rest generalizing state offset count with
  | nil =>
    simp only [List.sum_nil, Nat.add_zero] at admitted ⊢
    have goodRead : ReadResult (view state).bytes offset count (step state (.read handle offset count)).1 := by
      simpa only [live, Bool.false_eq_true, ite_false, admitted, ite_true, Int.toNat_natCast] using
        (law.read state handle offset count).2
    exact ⟨combine_empty goodRead, rfl⟩
  | cons next rest ih =>
    have nextPositive := restPositive next (by simp)
    have tailPositive : 0 < next + rest.sum := Nat.add_pos_left nextPositive rest.sum
    simp only [List.sum_cons] at admitted ⊢
    have tailAdmitted := (range_split admitted countPositive tailPositive).2
    have firstView : view (step state (.read handle offset count)).2 = view state :=
      (law.read state handle offset count).1
    have tailLive : ((view (step state (.read handle offset count)).2).mode handle).isNone = false :=
      firstView ▸ live
    have restPositive' : ∀ n ∈ rest, 0 < n := fun n member =>
      restPositive n (List.mem_cons_of_mem _ member)
    obtain ⟨tailReply, tailView⟩ :=
      ih (step state (.read handle offset count)).2 (offset + count) next
        nextPositive restPositive' tailAdmitted tailLive
    obtain ⟨combineReply, combineView, _, _⟩ :=
      reads_split law state handle admitted countPositive tailPositive live
    refine ⟨?_, tailView.trans combineView⟩
    rw [readFragments]
    simp only [tailReply]
    exact combineReply

/-- Every positive ordered partition of an admitted range reproduces the
whole-read reply on the same initial live file view. The two execution
traces retain their actual request granularity and handler endpoints. -/
theorem read_fragments_sound {State : Type} {step : Handler State} {view : State → FileState}
    (law : ReadLaw step view) (state : State) (handle : Handle)
    (offset count : Nat) (rest : List Nat) (countPositive : 0 < count)
    (restPositive : ∀ n ∈ rest, 0 < n) (admitted : ReadRange offset (count + rest.sum : Nat))
    (live : ((view state).mode handle).isNone = false) :
    let result := readFragments step handle state offset count rest
    let request := Request.read handle offset (count + rest.sum : Nat)
    let whole := step state request
    result.reply = some whole.1 ∧ view result.file = view whole.2 ∧
      Trace.Valid step state result.trace result.file ∧
      result.trace.map Exchange.request = fragmentRequests handle offset (count :: rest) ∧
      Trace.Valid step state [⟨request, whole.1⟩] whole.2 := by
  obtain ⟨reply, sameView⟩ :=
    fragments_agree law state handle offset count rest countPositive restPositive admitted live
  obtain ⟨valid, requests⟩ := read_fragments_trace step handle state offset count rest
  exact ⟨reply, sameView, valid, requests, .cons rfl (.nil _)⟩

end Silmaril.Proofs.Machine.SqliteVfs.ReadSplit.Fragments
