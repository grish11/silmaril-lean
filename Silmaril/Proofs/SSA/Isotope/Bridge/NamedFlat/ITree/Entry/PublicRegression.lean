module

import Silmaril.SSA.Isotope.Bridge.NamedFlat.ITree.Entry.Public.Thms
import Mathlib.Tactic.FinCases
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.Isotope.Bridge.NamedFlat.Entry.Public

open Silmaril.Isotope (BoundCtx Value)
open Silmaril.Isotope.Bridge.NamedFlat (elaborate check_sound)
open Silmaril.Isotope.LambdaSSA.Semantics (Env)
open Silmaril.SSA.LambdaRTL (CFG)
open Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

private abbrev bit : PacketType := .coprod .unit .unit
private def signature : PrimitiveSignature Unit := ⟨fun _ => bit, fun _ => bit⟩
private def inputs : Fin 1 → PacketType := fun _ => bit
private def outputs : Fin 2 → PacketType := fun _ => .product .unit (.product bit .unit)
private def locals : Fin 2 → PacketType := fun _ => bit

-- A visible reply selects the first exit or the second arm. The left
-- second arm takes a silent backedge and the right returns to exit one.
private def publicGraph (loops : Bool) : Program signature inputs outputs where
  locals := 2
  localType := locals
  entry _ := .inl 0
  entryType _ := rfl
  block i := Fin.cases (.apply () (.var .here) (.inl 1) (.var .here))
    (fun _ => .term (.case (.var .here)
      (.jump (.inr 0) (.pair .unit (.pair (.var (.there .here)) .unit)))
      (if loops then .jump (.inl 1) (.var (.there .here))
       else .jump (.inr 1) (.pair .unit (.pair (.var (.there .here)) .unit))))) i

private def context : BoundCtx PacketType 1 := .snoc .nil bit
private def publicNames : Fin 1 → Register := fun _ => ⟨0⟩
private instance : Silmaril.HasTy Unit PacketType := signature.typing

private theorem publicAccepted (loops : Bool) :
    (elaborate ((publicGraph loops).compile 0) (publicGraph loops).exits publicNames).isSome := by
  cases loops <;> decide

private def packed (loops : Bool) : Program.PackedEntry (publicGraph loops) 0 where
  count := 1
  captures := publicNames
  context := context
  blocks := locals
  exits := outputs
  target := (elaborate ((publicGraph loops).compile 0) (publicGraph loops).exits publicNames).get (publicAccepted loops)
  accepted := Option.eq_some_of_isSome (publicAccepted loops)
  typed := check_sound _ _ _ _ (by cases loops <;> decide)

-- The mutable names and label order differ from the public compiler's.
-- At an exit the original runner reads the selected reply register.
private abbrev Name := ULift.{1} Nat
private def exits : List Name := [⟨22⟩, ⟨11⟩]
private def fields (_ : Name) : List Name := [⟨7⟩]
private def namedNames : Fin 1 → Name := fun _ => ⟨14⟩

private def namedGraph (loops : Bool) : CFG Name Name Unit :=
  ⟨.term (.br ⟨9⟩ (.var ⟨14⟩)),
    [(⟨9⟩, ⟨⟨6⟩, .let1 ⟨7⟩ (.app () (.var ⟨6⟩)) (.term (.br ⟨5⟩ (.var ⟨7⟩)))⟩),
      (⟨5⟩, ⟨⟨7⟩, .term (.case (.val (.var ⟨7⟩)) ⟨19⟩ (.br ⟨22⟩ .unit) ⟨19⟩
        (if loops then .br ⟨5⟩ (.var ⟨7⟩) else .br ⟨11⟩ .unit))⟩)]⟩

private abbrev attached (loops : Bool) := Silmaril.SSA.LambdaRTL.CFG.Cyclic.LiveOut.attach fields (namedGraph loops)

private theorem closed (loops : Bool) : Silmaril.SSA.LambdaRTL.CFG.Cyclic.RoundTrip.PacketClosed (attached loops) := by
  have localClosed (i : Fin 2) :
      (attached loops).blocks[i.val]'i.isLt |>.2.body.toRegion.fv ⊆
        {(attached loops).blocks[i.val]'i.isLt |>.2.param} := by
    cases loops <;> fin_cases i <;> decide
  intro item mem
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem mem
  exact localClosed ⟨i, hi⟩

private theorem namedAccepted (loops : Bool) :
    (elaborate (attached loops) exits namedNames).isSome := by
  cases loops <;> decide

private def readback (loops : Bool) : Readback (packed loops) (namedGraph loops) exits fields where
  captureCount := 1
  captures := namedNames
  exitCount := rfl
  closed := closed loops
  blocks := (attached loops).blocks.length
  blockCount := rfl
  flat := (elaborate (attached loops) exits namedNames).get (namedAccepted loops)
  accepted := (NamedFlat.elaborateAt_eq _ exits namedNames).trans (Option.eq_some_of_isSome (namedAccepted loops))
  agrees := by cases loops <;> rfl

private def packet : Denote (inputs 0) := .inl ⟨⟩
private def initial (p : Denote bit) : Name → Value Atom :=
  fun reg => if reg = ⟨14⟩ then PacketType.encode bit p else .unit
private def record (p : Denote bit) : Env Atom := fun _ => PacketType.encode bit p
private def ambient : Env Atom := fun _ => .unit

private abbrev inclusion (left right : Bool) (packet : Denote bit) :=
  ∀ policy : Silmaril.Logic.ITree.Model.{0,0} signature.traceSignature.toSignature,
    ∀ x, policy.initial x → ∀ p,
      Silmaril.Elgot.ITree.HandledTrace policy.step x
        (LiveOut.observeRaw signature.primitive exits fields (namedGraph left) (initial packet)) p →
      Silmaril.Elgot.ITree.HandledTrace policy.step x
        (LiveOut.observeRaw signature.primitive exits fields (namedGraph right) (initial packet)) p

private theorem decision (left right : Bool) :
    (publicGraph left).refinementAt? (publicGraph right) 0 packet = true ↔ inclusion left right packet :=
  refinementAt?_iff_namedHandledTrace packet (packed left) (packed right) (readback left) (readback right)
    (initial packet) ambient ambient (record packet) (record packet)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

private def entryAt (loops : Bool) (input : Fin 1) : Program.PackedEntry (publicGraph loops) input := by
  have position : input = 0 := Subsingleton.elim _ _
  subst input
  exact packed loops

private def readbackAt (loops : Bool) (input : Fin 1) :
    Readback (entryAt loops input) (namedGraph loops) exits fields := by
  have position : input = 0 := Subsingleton.elim _ _
  subst input
  exact readback loops

private theorem agreesAt (loops : Bool) (input : Fin 1) (packet : Denote (inputs input)) :
    (entryAt loops input).recordAgrees packet (record packet) := by
  have position : input = 0 := Subsingleton.elim _ _
  subst input
  exact fun _ => rfl

private theorem capturesAt (loops : Bool) (input : Fin 1) (packet : Denote (inputs input))
    (i : Fin (readbackAt loops input).captureCount) :
    record packet i.val = initial packet ((readbackAt loops input).captures i) := by
  have position : input = 0 := Subsingleton.elim _ _
  subst input
  rfl

example (p : Denote bit) : inclusion true false p := by
  have decided := refinement?_iff_namedHandledTrace (entryAt true) (entryAt false)
    (readbackAt true) (readbackAt false) (fun _ p => initial p) ambient ambient
    (fun _ p => record p) (fun _ p => record p) (capturesAt true) (capturesAt false)
    (agreesAt true) (agreesAt false)
  exact decided.mp (by cbv) 0 p

example : ¬ inclusion false true packet := by
  intro included
  have accepted := (decision false true).mpr included
  have rejected : (publicGraph false).refinementAt? (publicGraph true) 0 packet = false := by cbv
  simp [rejected] at accepted

end Silmaril.Isotope.Bridge.NamedFlat.Entry.Public
