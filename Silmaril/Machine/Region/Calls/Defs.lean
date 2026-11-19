module

public import Silmaril.Machine.Region.Defs
public import Silmaril.X86.FnContract.Thms

/-! # Optional strict call summaries

Reuses the repository's System V `FnContract.Strict` over a supplied machine.
An angelic total contract alone is insufficient to describe every first
return. Summaries below retain ABI, footprint and postcondition facts and
never create an atomic instruction edge. In particular the Ext adapter keeps
calls/returns Top. A return summary is not a region first-exit theorem unless
code support and no earlier boundary crossing are also established.
-/

@[expose] public section
namespace Silmaril.Machine.Region.Calls
open Silmaril.X86

/-- A finite resumption allowance justified by a first-return contract on the
chosen machine. The return address is read from the admitted entry state;
ABI admission must prove that the stack slot is actually readable. -/
def resumption {σ : Type} (I : SegVC.Isa σ) (entry : σ) : Nat :=
  (FnContract.retOf (I.core entry) (I.mem entry)).toNat

/-- Both admission and the strict contract refer to the same machine, image,
frame and state. No assumption about unverified/relocated callees is added. -/
def Admitted {σ : Type} {I : SegVC.Isa σ} (C : FnContract.Strict I) (s : σ) : Prop :=
  I.live s ∧ FnContract.AbiEntry (I.core s) (I.mem s) ∧ C.entry s

end Silmaril.Machine.Region.Calls
