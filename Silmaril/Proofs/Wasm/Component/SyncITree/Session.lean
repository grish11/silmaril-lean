module

public import Silmaril.Proofs.Wasm.Component.SyncITree.Body
public import Silmaril.Wasm.Component.Reference.SessionDiv.Thms
public import Silmaril.Wasm.Component.Reference.SessionAdequacy.Thms
public import Silmaril.Wasm.Component.Reference.SessionAdequacy.Readback.Thms

public section

namespace Silmaril.Proofs.Wasm.Component.SyncITree

open Silmaril.Games
open Silmaril.Wasm.Component (checkList_of_liftArgs)
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component.SyncITree
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

variable {c : Simple} {o : GrowOracle} {r : Ready c} {s s' : Store Nat}
  {qs : List (Question c)} {outs : List (Option (List Silmaril.Wasm.Component.Val))}

private theorem typed_questions (qs : List (Question c)) :
    TypedCalls c (qs.map Question.erase) := by
  intro q mem
  obtain ⟨question, _, rfl⟩ := List.mem_map.mp mem
  exact question.args.property

private theorem runs_iff :
    Runs o r s qs outs s' ↔
      SessSpec (profile o) c r.inst s (specCalls c (qs.map Question.erase)) outs s' := by
  induction qs generalizing s outs with
  | nil =>
    constructor
    · intro h
      cases h
      exact .nil _
    · intro h
      cases h
      exact .nil _
  | cons q qs ih =>
    constructor
    · intro h
      cases h with
      | @cons _ _ _ _ _ _ a step rest =>
        have done := responds_iff.mp step
        cases a with
        | none => exact .trap done (ih.mp rest)
        | some vs => exact .ret done (ih.mp rest)
    · intro h
      change SessSpec _ _ _ _ ((c.exports[q.exportIdx], q.args.val) :: _) _ _ at h
      cases h with
      | ret done rest =>
        obtain ⟨_, _, _, _, _, _, lifted⟩ := done.run
        exact .cons (a := some ⟨_, checkList_of_liftArgs lifted⟩)
          (responds_iff.mpr done) (ih.mpr rest)
      | trap done rest =>
        exact .cons (a := none) (responds_iff.mpr done) (ih.mpr rest)

theorem completes_iff_reference (prof : Silmaril.Wasm.Component.ProfileKind) :
    Completes o r qs outs ↔ refOuts outs ∈ sessObs (profile o) prof c (qs.map Question.erase) := by
  constructor
  · rintro ⟨st, h⟩
    exact c.sess_specToRef (profile o) prof r.adequate r.isInst _ _ st (typed_questions qs)
      (runs_iff.mp h)
  · intro h
    obtain ⟨inst, os, st, hI, hs, eq⟩ :=
      c.sess_refToSpec (profile o) prof r.adequate _ (typed_questions qs) h
    obtain rfl := refOuts_injective eq
    obtain rfl := NumModule.inst_unique hI r.isInst
    exact ⟨st, runs_iff.mpr hs⟩

theorem completes_iff_game (hlen : qs.length = outs.length) :
    Completes o r qs outs ↔
      sessMoves c (qs.map Question.erase) outs ∈ c.toComp.den (modSem (profile o)) := by
  rw [completes_iff_reference .deterministic]
  constructor
  · intro h
    obtain ⟨os, eq, _, move⟩ :=
      c.sess_sound (profile o) .deterministic r.adequate _ (typed_questions qs) h
    obtain rfl := refOuts_injective eq
    exact move
  · exact c.sess_complete (profile o) .deterministic r.adequate _ _
      (typed_questions qs) (by simpa using hlen)

private theorem sessMoves_idle (qs : List (Question c)) (outs : List (Option (List Silmaril.Wasm.Component.Val))) :
    Path .idle (sessMoves c (qs.map Question.erase) outs) .idle := by
  induction qs generalizing outs with
  | nil => exact .nil _
  | cons q qs ih =>
    cases outs with
    | nil => exact .nil _
    | cons out outs =>
      exact .cons (.ask q.gameOp) (.cons (.ret q.gameOp (out.map .vals)) (ih outs))

theorem pending_iff_game (hlen : qs.length = outs.length) (q : Question c) :
    Completes o r qs outs ↔
      sessMoves c (qs.map Question.erase) outs ++ [.inr (.ask q.gameOp)] ∈
        c.toComp.den (modSem (profile o)) := by
  rw [completes_iff_game hlen]
  constructor
  · intro h
    exact Strategy.receptive _ h (sessMoves_idle qs outs) (.ask q.gameOp) trivial
  · intro h
    exact Strategy.of_prefix _ h (List.prefix_append _ _)

theorem quiet_iff_reference (prof : Silmaril.Wasm.Component.ProfileKind) (q : Question c) :
    Quiet o r qs outs q ↔
      outs ∈ refDivs (profile o) prof c (qs.map Question.erase) q.exportIdx q.args.val := by
  rw [← c.sessDivs_eq_refDivs (profile o) prof r.adequate _ _ _ (typed_questions qs)
    q.args.property]
  constructor
  · rintro ⟨st, hs, hd⟩
    exact ⟨r.inst, st, r.isInst, runs_iff.mp hs, diverges_iff.mp hd⟩
  · rintro ⟨inst, st, hI, hs, hd⟩
    obtain rfl := NumModule.inst_unique hI r.isInst
    exact ⟨st, runs_iff.mpr hs, diverges_iff.mpr hd⟩

end Silmaril.Proofs.Wasm.Component.SyncITree
