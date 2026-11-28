module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Identification.Defs

/-! Compose typed port maps and compare two successful guarded compiler paths. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition

open SeaOfNodes.Diamond (ValueSort)
open Silmaril.MLIR.Arith (Width)
open Identification (BankMap PortMap Refusal)
open Reindex.Guarded.Institution (AdmittedAt Generated)
open Reindex.Guarded.Institution renaming Signature → EntrySignature

variable {old middle new : List (ValueSort Width)}
variable {S T U : EntrySignature} {result : Width}

/-- Apply the first map, then the second, keeping the sort of every port. -/
def thenMap (first : BankMap old middle) (second : BankMap middle new) : BankMap old new :=
  fun sort port => second sort (first sort port)

/-- Check identification at the intermediate bank and then replay the
existing embedding compiler at the final bank. -/
def compileStaged (first : PortMap S T) (second : Embedding T U) (p : AdmittedAt S result) :
    Except Refusal (Generated U result) :=
  match Identification.compile first p with
  | .error reason => .error reason
  | .ok intermediate => (second.compile intermediate.source).mapError Refusal.checker

/-- A sentence operand for which both compiler paths succeeded. -/
structure Compared (first : PortMap S T) (second : Embedding T U) (result : Width) where
  source : AdmittedAt S result
  intermediate : Generated T result
  staged : Generated U result
  direct : Generated U result
  identified : Identification.compile first source = .ok intermediate
  embedded : second.compile intermediate.source = .ok staged
  composed : Identification.compile (thenMap first second.portMap) source = .ok direct

inductive Refused where
  | staged (reason : Refusal)
  | direct (reason : Refusal)
  deriving DecidableEq, Repr

/-- Check both paths for a program to use as an equation or termination operand. -/
def compare (first : PortMap S T) (second : Embedding T U) (p : AdmittedAt S result) :
    Except Refused (Compared first second result) :=
  match identified : Identification.compile first p with
  | .error reason => .error (.staged reason)
  | .ok intermediate =>
    match embedded : second.compile intermediate.source with
    | .error reason => .error (.staged (.checker reason))
    | .ok staged =>
      match composed : Identification.compile (thenMap first second.portMap) p with
      | .error reason => .error (.direct reason)
      | .ok direct => .ok ⟨p, intermediate, staged, direct, identified, embedded, composed⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.Composition
