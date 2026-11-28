module

import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Packed.Institution.Conservativity.Thms
import Mathlib.Tactic.FinCases
meta import Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible.Defs

namespace Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible

open Silmaril.Isotope.Bridge.NamedFlat (elaborate check_sound)
open Silmaril.Isotope.LambdaSSA

private def signature : PrimitiveSignature Empty :=
  ⟨Empty.elim, Empty.elim⟩

private def bit : PacketType := .coprod .unit .unit
private def packetType : PacketType := .product bit bit
private def inputs : Fin 2 → PacketType := Fin.cases bit (fun _ => packetType)
private def outputs : Fin 2 → PacketType := fun _ => bit
private def locals : Fin 1 → PacketType := fun _ => packetType

-- The first entry returns directly. The second carries an argument and a
-- selector in one packet. The selector can change the exit while the
-- original argument is the payload on either exit.
private def fixture (different : Bool) : Program signature inputs outputs where
  locals := 1
  localType := locals
  entry := Fin.cases (.inr 0) (fun _ => .inl 0)
  entryType input := by fin_cases input <;> rfl
  block _ := .unpack (.var .here) (.term (.case (.var .here)
    (.jump (.inr 0) (.var (.there (.there .here))))
    (.jump (.inr (if different then 1 else 0)) (.var (.there (.there .here))))))

private abbrev left := fixture false
private abbrev right := fixture true
private def matching : Denote (inputs 1) := (.inl ⟨⟩, .inl ⟨⟩)
private def mismatch : PacketAt inputs := ⟨1, (.inl ⟨⟩, .inr ⟨⟩)⟩

private theorem matchingPass : left.weakEqAt? right 1 matching = true := by cbv

example : left.observe 1 matching = right.observe 1 matching :=
  (left.weakEqAt?_iff right 1 matching).mp matchingPass

private theorem found : left.firstMismatch? right = some mismatch := by cbv

example : left.observe mismatch.1 mismatch.2 ≠ right.observe mismatch.1 mismatch.2 :=
  left.firstMismatch?_sound found

#guard left.weakEq? left
#guard !(left.weakEq? right)

private def captures : Fin 1 → Register := fun _ => ⟨0⟩
private instance : Silmaril.HasTy Empty PacketType := signature.typing

private theorem accepts (different : Bool) (input : Fin 2) :
    (elaborate ((fixture different).compile input) (fixture different).exits captures).isSome := by
  cases different <;> fin_cases input <;> decide

private def target (different : Bool) (input : Fin 2) :=
  (elaborate ((fixture different).compile input) (fixture different).exits captures).get
    (accepts different input)

private def packed (different : Bool) (input : Fin 2) : Program.PackedEntry (fixture different) input where
  count := 1
  captures := captures
  context := .snoc .nil (inputs input)
  blocks := locals
  exits := outputs
  target := target different input
  accepted := Option.eq_some_of_isSome (accepts different input)
  typed := check_sound _ _ _ _ (by cases different <;> fin_cases input <;> decide)

private def ambient : Semantics.Env Atom := fun _ => .unit
private def record (input : Fin 2) (packet : Denote (inputs input)) : Semantics.Env Atom :=
  fun _ => PacketType.encode (inputs input) packet

private theorem agrees (different : Bool) (input : Fin 2) (packet : Denote (inputs input)) :
    (packed different input).recordAgrees packet (record input packet) :=
  fun _ => rfl

example : (packed false 1).observe ambient (record 1 matching) =
    (packed true 1).observe ambient (record 1 matching) := by
  rw [(packed false 1).observe_eq _ _ _ (agrees false 1 matching),
    (packed true 1).observe_eq _ _ _ (agrees true 1 matching)]
  exact (left.weakEqAt?_iff_packedOutput right 1 matching).mp matchingPass

example : (packed false mismatch.1).observe ambient (record mismatch.1 mismatch.2) ≠
    (packed true mismatch.1).observe ambient (record mismatch.1 mismatch.2) :=
  left.firstMismatch?_sound_packed found _ _ _ _ _ _ (agrees false _ _) (agrees true _ _)

private def explanation : Program.Mismatch signature inputs :=
  ⟨mismatch, .leftToRight, .result (0, .inl .unit)⟩

private theorem explained : left.explainMismatch? right = some explanation := by cbv

#guard (left.explainMismatch? left).isNone

example : explanation.direction.distinguishes
    ((packed false mismatch.1).observe ambient (record mismatch.1 mismatch.2))
    ((packed true mismatch.1).observe ambient (record mismatch.1 mismatch.2))
    (explanation.trace.map FiniteCFG.packedTreeOutput) :=
  left.explainMismatch?_sound_packed explained _ _ _ _ _ _ (agrees false _ _) (agrees true _ _)

example : ¬ Silmaril.Logic.ITree.TraceInstitution.institution.{0, 1, 0}.Sat signature.traceSignature
    ⟨signature.traceModel⟩
    ((packed false mismatch.1).refinementSentence (packed true mismatch.1)
      explanation.direction ambient ambient (record mismatch.1 mismatch.2) (record mismatch.1 mismatch.2)) :=
  left.explainMismatch?_refutes_traceSat explained (packed false mismatch.1) (packed true mismatch.1)
    ambient ambient _ _ (agrees false _ _) (agrees true _ _)

example : ¬ (∀ input packet, (packed false input).observe ambient (record input packet) =
    (packed true input).observe ambient (record input packet)) := by
  intro equal
  have accepted := (left.weakEq?_iff_packed right (packed false) (packed true) ambient ambient
    record record (agrees false) (agrees true)).mpr equal
  simp [Program.weakEq?, found] at accepted

open Silmaril.Logic.ITree

example : ¬ (∀ input packet (policy : Silmaril.Logic.ITree.Model.{0, 0} signature.traceSignature.toSignature),
    TraceInstitution.Sat policy ((packed false input).refinementSentence (packed true input) .leftToRight
      ambient ambient (record input packet) (record input packet)) ∧
    TraceInstitution.Sat policy ((packed false input).refinementSentence (packed true input) .rightToLeft
      ambient ambient (record input packet) (record input packet))) := by
  intro valid
  have accepted := (left.weakEq?_iff_mutual_valid_traceSat right (packed false) (packed true) ambient ambient
    record record (agrees false) (agrees true)).mpr valid
  simp [Program.weakEq?, found] at accepted

end Silmaril.SSA.LambdaRTL.CFG.Cyclic.Link.Fields.Typed.Visible
