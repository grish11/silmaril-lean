module

public import Silmaril.Wasm.Game.Intrinsic.Defs

@[expose] public section

namespace Silmaril.Wasm.Game.Intrinsic.Requests

open Silmaril.Games Execution.Core Numerics SingleThreaded

/-- The name is backed by the actual raw function import declaration. The
ordinal is retained: two equal textual names need not be the same game port.
Use with `IsInstance` to interpret that ordinal in the ordered scalar interface. -/
structure NamedImport (source : Module) (I : ScalarInstance) where
  slot : Fin I.imports.length
  moduleName : String
  name : String
  typeIndex : TypeIdx
  declaration : source.imports[slot.val]? = some ⟨moduleName, name, .func typeIndex⟩

abbrev NamedImport.signature {source : Module} {I : ScalarInstance} (request : NamedImport source I) : FnType :=
  I.imports.get request.slot

def NamedImport.question {source : Module} {I : ScalarInstance} (request : NamedImport source I)
    (args : Typed request.signature.params) : I.E.Op :=
  ⟨request.slot, args⟩

/-- A well-founded request/reply tree. A reply can
return typed values, trap, or throw; the continuation receives that exact
answer. This inductive tree alone does not represent an infinite run. -/
inductive Tree (source : Module) (I : ScalarInstance) (result : FnType) where
  | done (answer : Answer result)
  | ask (request : NamedImport source I) (args : Typed request.signature.params)
      (then_ : Answer request.signature → Tree source I result)

variable {source : Module} {I : ScalarInstance}

/-- A separate, partial, memoryless host interpretation. `none` means the
handler did not reply to a question, never that Wasm trapped. This is not a
restriction on the open tree or on what a Wasm import can do. -/
def Tree.handle {result : FnType} (env : Env I.E) : Tree source I result → Option (Answer result)
  | .done answer => some answer
  | .ask request args then_ => (env (request.question args)).bind fun reply => (then_ reply).handle env

/-- Read the handled result. A missing reply is an observable host divergence,
not a Wasm trap and not failure to compute the tree. -/
def Tree.handledBehaviour {result : FnType} (env : Env I.E) (tree : Tree source I result) : Behaviour Val :=
  (tree.handle env).elim .diverges Answer.toBehaviour

/-- Completed traces of the tree itself, starting after the export question.
Unlike the comparison relation, this does not inspect Wasm code or a store. -/
inductive Completes (n : Nat) (op : I.F.Op) :
    Tree source I (I.exports.get op.1) → List (Move I.E I.F) → Prop where
  | done (answer : I.F.Ar op) : Completes n op (.done answer) [.inr (.ans op answer)]
  | ask {request : NamedImport source I} {args : Typed request.signature.params}
      {then_ : Answer request.signature → Tree source I (I.exports.get op.1)} {moves}
      (reply : Answer request.signature) (allowed : Answer.ThrowsBelow n reply)
      (tail : Completes n op (then_ reply) moves) :
      Completes n op (.ask request args then_)
        (.inl (.ask (request.question args)) :: .inl (.ans (request.question args) reply) :: moves)

/-- The implementation obligation, branch by branch, entirely in terms of the
stock host-free machine and its resumption. `n` is a bound on incoming thrown
addresses; valid concrete uses must justify it for the callout stores. -/
inductive Realizes (P : Profile) (n : Nat) (op : I.F.Op) :
    Tree source I (I.exports.get op.1) → Store Nat → Thread → Prop where
  | done {store target : Store Nat} {thread final : Thread} {answer : I.F.Ar op}
      (run : Reach P (store, thread) (target, final))
      (result : ResultAt target final (Answer.toResult (ft := I.exports.get op.1) answer)) :
      Realizes P n op (.done answer) store thread
  | ask {store callStore : Store Nat} {thread waiting : Thread}
      {request : NamedImport source I} {args : Typed request.signature.params}
      {then_ : Answer request.signature → Tree source I (I.exports.get op.1)}
      (run : Reach P (store, thread) (callStore, waiting))
      (callout : CalloutAt callStore waiting request.slot.val args.val)
      (decode : I.importOp? request.slot.val args.val = some (request.question args))
      (next : ∀ reply, Answer.ThrowsBelow n reply →
        Realizes P n op (then_ reply) callStore (resumeResult callStore waiting reply.toResult)) :
      Realizes P n op (.ask request args then_) store thread

end Silmaril.Wasm.Game.Intrinsic.Requests
