module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseBind.OpenReplay.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.ProductEta.Defs

/-! # Constructor packets for a finite retained Boolean context -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay

open Silmaril
open Paper.WithComputedProductProducers.Intrinsic
open CaseTree.ReplyAgreement
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload

/-- Rebuild the nested reply product from an initial unit value and the
unit payload of each tagged slot. -/
def replyPacket : {n : Nat} → Finite.Assignment n → (Fin n → Tm signature.Instr) →
    Tm signature.Instr → Tm signature.Instr
  | 0, _, _, base => base
  | _ + 1, env, payload, base =>
    .pair (replyPacket env.tail (fun j => payload j.succ) base)
      (if env 0 then .inr (payload 0) else .inl (payload 0))

/-- Each expansion opens a product and then opens its newest bit. -/
def packetCaseCtx : Nat → List (Ty Empty) → List (Ty Empty)
  | 0, Γ => Γ
  | n + 1, Γ => packetCaseCtx n (unit :: Bit :: replyContext n :: Γ)

/-- The payload binders of the case-expanded packet, in logical reply order. -/
def packetPayload : (n : Nat) → Fin n → Tm signature.Instr
  | 0, j => j.elim0
  | n + 1, j => Fin.cases (.var (3 * n)) (packetPayload n) j

/-- For a nonempty packet the innermost product exposes the initial unit. -/
def packetBase : Nat → Nat → Tm signature.Instr
  | 0, i => .var i
  | _ + 1, _ => .var 2

/-- The constructor substitution at one row of a case-expanded packet. -/
def casePacket {n : Nat} (env : Finite.Assignment n) (i : Nat) : Tm signature.Instr :=
  replyPacket env (packetPayload n) (packetBase n i)

/-- The actual tag and payload of a bit constructor. -/
def replyBitTag (b : Bool) (u : Tm signature.Instr) : Tm signature.Instr :=
  if b then .inr u else .inl u

/-- Focus on a bit variable and substitute its tagged payload in a case arm. -/
def bitBranch (i : Nat) (b : Bool) (j : Nat) : Tm signature.Instr :=
  if j = i then replyBitTag b (.var 0) else .var (j + 1)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseBind.OpenReplay
