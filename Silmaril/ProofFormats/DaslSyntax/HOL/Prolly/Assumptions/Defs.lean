module

public import Silmaril.ProofFormats.DaslSyntax.HOL.Defs
public import Silmaril.ProofFormats.DaslSyntax.HOL.Prolly.Defs

@[expose] public section

namespace Silmaril.ProofFormats.DaslSyntax.HOL.Prolly

open Silmaril.Formats.Dasl
open Silmaril.Formats.Dasl.Prolly (Read Fault ByteKey setCodec byteKey closedSet setNames)
open Silmaril.Logic.HOLLight

universe u

variable {Name : Type}

abbrev assumptionCodec : Encode.PartialCodec (Semantics.Prolly.Block Name ByteKey Unit) (Shallow Name) :=
  setCodec byteKey

/-- Failure to resolve assumptions is not a negative logical judgment. -/
inductive ReadFault (Name : Type) where
  | block (fault : Fault Name)
  | invalidKey (key : ByteKey)
  deriving DecidableEq, Repr

def readKey (key : ByteKey) : Except (ReadFault Name) Tm :=
  match hypothesisKey.decode? key with
  | some term => if hypothesisKey.encode term = key then .ok term else .error (.invalidKey key)
  | none => .error (.invalidKey key)

/-- Read every block and decode every key canonically. The returned list is in key
order; its finite set, not that order, supplies HOL hypotheses. -/
def readAssumptions (read : Read Name) (width fuel : Nat) (root : Name) : Except (ReadFault Name) (List Tm) :=
  match closedSet assumptionCodec read width fuel root with
  | .ok view => view.keys.mapM readKey
  | .error fault => .error (.block fault)

def assumptions (read : Read Name) (width fuel : Nat) : Name → Hyps → Prop :=
  Lift.codedSet (setNames assumptionCodec read width fuel) hypothesisKey

def derives (store : Store Name) (read : Read Name) (width fuel : Nat) (sig : Signature) (theory : Theory) :
    Consequence.System Name Name := HOL.derivesWith store (assumptions read width fuel) sig theory

def entails (store : Store Name) (read : Read Name) (width fuel : Nat) {sig : Signature} (model : Model.{u} sig) :
    Consequence.System Name Name := HOL.entailsWith store (assumptions read width fuel) model

end Silmaril.ProofFormats.DaslSyntax.HOL.Prolly
