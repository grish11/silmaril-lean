module

public import Silmaril.SSA.PEG.Simple.Structured.Completion.Token.Recursive.Defs
public import Silmaril.Proofs.SSA.PEG.Simple.Structured.Token.Region

public section

namespace Silmaril.SSA.PEG.Simple.Structured.Token.Recursive.Proofs

set_option backward.isDefEq.respectTransparency false

open RVSDG (Port Tuple)
open Structured.Proofs
open Token.Proofs

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params vars mid outs before all : List (Ty Data)}
variable {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params}
variable {read : Reads (model m) all} {active : List (Fin all.length)}
variable {i : Index all.length}

@[expose] def BottomOn (read : Reads (model m) all) (active : List (Fin all.length))
    (i : Index all.length) (marker : Port all .bool) : Prop :=
  ∀ j, Agrees active i j → read marker j = none

/-- A compiled statement preserves its entire typed store on success.
Defined completion recovers a source execution from a realized entry.
An unavailable incoming marker remains unavailable through the fragment. -/
structure StatementFacts (stmt : Stmt P true vars outs) (ctx : Tuple (Port before) (.bool :: vars))
    (b : Build (Opcode P) params before (.bool :: outs)) (v : View (model m) env read active b.code) : Prop where
  bottom : ∀ {i : Index all.length},
    BottomOn read active i (v.embed (b.code.lift (ctx.get .head))) →
    BottomOn read active i (v.embed (b.refs.get .head))
  ofReturns : ∀ {i : Index all.length} {store final},
    RealizesOn read (fun r => v.embed (b.code.lift r)) ctx (pack m store) active i →
    Exec m stmt store (some final) →
    RealizesOn read v.embed b.refs (pack m final) active i
  ofToken : ∀ {i : Index all.length} {store},
    RealizesOn read (fun r => v.embed (b.code.lift r)) ctx (pack m store) active i →
    (read (v.embed (b.refs.get .head)) i).isSome →
    ∃ final, Exec m stmt store (some final) ∧ RealizesOn read v.embed b.refs (pack m final) active i

variable {stmt : Stmt P true vars outs} {ctx : Tuple (Port before) (.bool :: vars)}
variable {b : Build (Opcode P) params before (.bool :: outs)} {v : View (model m) env read active b.code}

/-- A realized input makes the completion result uniform over the enclosing
coordinates. This lets sequencing propagate failure through later loops
even if they discard every data output of the failed statement. -/
theorem StatementFacts.bottomOfRead (facts : StatementFacts stmt ctx b v)
    {store : Tuple m.Value vars}
    (entry : RealizesOn read (fun r => v.embed (b.code.lift r)) ctx (pack m store) active i)
    (missing : read (v.embed (b.refs.get .head)) i = none) :
    BottomOn read active i (v.embed (b.refs.get .head)) := by
  intro j agree
  cases atJ : read (v.embed (b.refs.get .head)) j with
  | none => exact atJ
  | some token =>
    have entryAt : RealizesOn read (fun r => v.embed (b.code.lift r)) ctx (pack m store) active j :=
      fun k h => entry k (fun l mem => (h l mem).trans (agree l mem))
    have done : (read (v.embed (b.refs.get .head)) j).isSome := by rw [atJ]; rfl
    obtain ⟨final, _, realized⟩ := facts.ofToken entryAt done
    have defined := realized i (fun l mem => (agree l mem).symm) .bool .head
    change read (v.embed (b.refs.get .head)) i = some ⟨true⟩ at defined
    rw [missing] at defined
    cases defined

theorem straightFacts (s : Body P vars outs) (ctx : Tuple (Port before) (.bool :: vars))
    (v : View (model m) env read active (.straight (s.lower ctx).code)) :
    StatementFacts s.source.enableWhile ctx (.straight (s.lower ctx)) v := by
  constructor
  · intro i bottom j agree
    exact sliceBottom s ctx v j (bottom j agree)
  · intro i store final entry ran
    have exact := sliceExact s ctx v store entry
    rw [(s.source.runLoopFree_enableWhile store).deterministic ran] at exact
    exact exact
  · intro i store entry done
    have assessed := sliceExact s ctx v store entry
    change (read (v.embed ((s.lower ctx).refs.get .head)) i).isSome at done
    cases ran : s.source.runLoopFree m store with
    | none =>
      rw [ran] at assessed
      rw [assessed i (agrees_self active i)] at done
      cases done
    | some final =>
      rw [ran] at assessed
      exact ⟨final, ran ▸ s.source.runLoopFree_enableWhile store, assessed⟩

theorem sequenceFacts (first : Stmt P true vars mid) (second : Stmt P true mid outs)
    (ctx : Tuple (Port before) (.bool :: vars))
    (a : Build (Opcode P) params before (.bool :: mid))
    (b : Build (Opcode P) params a.nodes (.bool :: outs))
    (v : View (model m) env read active (.seq a.code b.code))
    (fa : StatementFacts first ctx a v.left) (fb : StatementFacts second a.refs b v.right) :
    StatementFacts (.seq first second) ctx (a.thenBuild b) v := by
  constructor
  · intro i missing
    exact fb.bottom (fa.bottom missing)
  · intro i store final entry ran
    cases ran with
    | seq one two => exact fb.ofReturns (fa.ofReturns entry one) two
  · intro i store entry done
    cases intermediate : read (v.left.embed (a.refs.get .head)) i with
    | none =>
      have missing := fb.bottom (fa.bottomOfRead entry intermediate)
      change (read (v.right.embed (b.refs.get .head)) i).isSome at done
      have atI := missing i (agrees_self active i)
      change read (v.right.embed (b.refs.get .head)) i = none at atI
      rw [atI] at done
      cases done
    | some token =>
      have reached : (read (v.left.embed (a.refs.get .head)) i).isSome := by rw [intermediate]; rfl
      obtain ⟨next, one, nextAligned⟩ := fa.ofToken entry reached
      obtain ⟨final, two, finalAligned⟩ := fb.ofToken nextAligned done
      exact ⟨final, .seq one two, finalAligned⟩

end Silmaril.SSA.PEG.Simple.Structured.Token.Recursive.Proofs
