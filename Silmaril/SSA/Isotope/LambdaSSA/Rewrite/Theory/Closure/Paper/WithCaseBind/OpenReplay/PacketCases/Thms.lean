module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.PacketCases.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.PacketCases

/-! # Native extensionality at the expanded packet constructors -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload
open Paper.WithCaseBind.SelectedTerminal (Seed)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local instance packetCasesHasTy : HasTy signature.Instr (Ty Empty) := signature.hasTy

/-- Each extracted payload is a constructor-valued unit at the case context. -/
theorem packetPayload_typed {Γ : List (Ty Empty)} (n : Nat) (j : Fin n) :
    Tm.BranchValue (packetCaseCtx n Γ) (packetPayload n j) unit :=
  PacketCases.packetPayload_typed n j

/-- The base slot of the expanded packet retains its unit type. -/
theorem packetBase_typed {Γ : List (Ty Empty)} {i n : Nat}
    (hi : At Γ i (replyContext n)) : Tm.BranchValue (packetCaseCtx n Γ) (packetBase n i) unit :=
  PacketCases.packetBase_typed hi

/-- To compare two regions on an open reply packet, it suffices to compare
them at its tagged constructor rows. Each row retains its lexical unit
payload binders and the original outward interface. -/
theorem packet_case_ext {n : Nat} {L : List (Ty Empty)} {p q : Region signature.Instr}
    (hp : HasType [replyContext n] p L) (hq : HasType [replyContext n] q L)
    (rows : ∀ env : Finite.Assignment n, Paper.Extension.Eqv Seed (packetCaseCtx n [replyContext n])
      (p.substVars (Tm.singleSubst (casePacket env 0)))
      (q.substVars (Tm.singleSubst (casePacket env 0))) L) :
    Paper.Extension.Eqv Seed [replyContext n] p q L :=
  PacketCases.packet_case_ext hp hq rows

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
