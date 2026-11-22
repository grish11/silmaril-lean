module

public import Silmaril.ProofFormats.DaslSyntax.Database.Defs

@[expose] public section

namespace Silmaril.ProofFormats.DaslSyntax.Database.Examples

namespace HOL

open Silmaril.Logic.HOLLight
open Silmaril.Semantics.Naming (Relation graph)

def premise : Tm := .fvar 0 .bool
def consequence : Tm := Tm.imp Tm.truth premise
def closed : Tm := Tm.imp Tm.truth Tm.truth

inductive TermName where
  | premise | alias | consequence | closed | bound | missing
  deriving DecidableEq

def terms : Relation TermName Tm := graph fun
  | .premise | .alias => some premise
  | .consequence => some consequence
  | .closed => some closed
  | .bound => some (.bvar 0)
  | .missing => none

def hypotheses : Relation Bool Hyps := graph fun
  | true => some {premise}
  | false => none

def contexts : Relation Unit (List Ty) := graph fun _ => some [.bool]
def types : Relation Unit Ty := graph fun _ => some .bool

end HOL

namespace MLTT

open Silmaril.Logic.TypeTheory.ExtensionalMLTT
open Silmaril.Semantics.Naming (Relation graph)

def fiber : ETm 1 := .id .nats (.bv 0) (.bv 0)
def sigma : ETm 0 := .sigma .nats fiber
def pair : ETm 0 := .pair .zero (.refl .zero)

def contexts : Relation Unit ECtx := graph fun _ => some .nil
def types : Relation Unit (ETm 0) := graph fun _ => some sigma
def terms : Relation Bool (ETm 0) := graph fun
  | true => some pair
  | false => none

end MLTT

end Silmaril.ProofFormats.DaslSyntax.Database.Examples
