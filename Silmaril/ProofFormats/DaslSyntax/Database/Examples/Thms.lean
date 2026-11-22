module

public import Silmaril.ProofFormats.DaslSyntax.Database.Examples.Defs
public import Silmaril.ProofFormats.DaslSyntax.Database.Thms
import Silmaril.Proofs.ProofFormats.DaslSyntax.DatabaseExamples

public section

namespace Silmaril.ProofFormats.DaslSyntax.Database.Examples

namespace HOL

open Silmaril.Logic.HOLLight

theorem premiseTyped : HasType initialSignature [] premise .bool :=
  Proofs.ProofFormats.DaslSyntax.DatabaseExamples.HOL.premiseTyped

theorem assumed : Derives initialSignature [] {premise} premise :=
  Proofs.ProofFormats.DaslSyntax.DatabaseExamples.HOL.assumed

theorem consequenceProof : Derives initialSignature [] {premise} consequence :=
  Proofs.ProofFormats.DaslSyntax.DatabaseExamples.HOL.consequenceProof

theorem closedProof : Database.HOL.ClosedProof initialSignature [] closed :=
  Proofs.ProofFormats.DaslSyntax.DatabaseExamples.HOL.closedProof

theorem contextRow : Database.HOL.derives hypotheses terms initialSignature [] true .consequence :=
  namedSystem_iff.mpr ⟨{premise}, consequence, rfl, rfl, consequenceProof⟩

theorem closedRow : TermName.closed ∈ Database.HOL.closedTheorems terms initialSignature [] :=
  Semantics.Naming.Lift.mem_where_iff.mpr ⟨closed, rfl, closedProof⟩

end HOL

namespace MLTT

open Silmaril.Logic.TypeTheory.ExtensionalMLTT

theorem sigmaFormation : ECtx.JEq .nil (.univ 0) sigma sigma :=
  Proofs.ProofFormats.DaslSyntax.DatabaseExamples.MLTT.sigmaFormation

theorem pairTyping : ECtx.JEq .nil sigma pair pair :=
  Proofs.ProofFormats.DaslSyntax.DatabaseExamples.MLTT.pairTyping

theorem firstProjection : ECtx.JEq .nil .nats (.fst pair) .zero :=
  Proofs.ProofFormats.DaslSyntax.DatabaseExamples.MLTT.firstProjection

theorem secondProjection : ECtx.JEq .nil (fiber.lst .zero) (.snd pair) (.refl .zero) :=
  Proofs.ProofFormats.DaslSyntax.DatabaseExamples.MLTT.secondProjection

theorem formationRow : Database.MLTT.formation contexts types () () :=
  namedSystem_iff.mpr ⟨.nil, sigma, rfl, rfl, .nil_ok, 0, sigmaFormation⟩

theorem inhabitanceRow : Database.MLTT.inhabitance contexts types () () :=
  namedSystem_iff.mpr ⟨.nil, sigma, rfl, rfl, pair, .nil_ok, pairTyping⟩

theorem typingRow : Database.MLTT.typing contexts terms types () true () :=
  typingTable_iff.mpr ⟨.nil, pair, sigma, rfl, rfl, rfl, .nil_ok, pairTyping⟩

end MLTT

end Silmaril.ProofFormats.DaslSyntax.Database.Examples
