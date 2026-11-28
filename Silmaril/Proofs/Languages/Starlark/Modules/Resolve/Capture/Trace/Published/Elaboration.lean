module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (globalSlot fileSlot TopCode)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive (compile_site)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Named
  (resolves_at Spread Mapping)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Functions.Lowering.Resolve (SourceExpr resolveTracked)

private theorem root_compiles {globals : List String} (root : Root globals) :
    elaborateCommand ⟨(moduleLex globals).context, .global⟩ root.command root.seed =
      .ok (.exec (.define root.site.name root.id), root.table) := by
  have compiled := compile_site root.site root.lexical
    (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.compiles root.suite)
  have localResult := elaborateCommand_nativeDefinition _ .global _ _ _ _ _ _ _ compiled
  exact localResult

theorem plan_compiles {globals : List String} {env : Environment} {source : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {seed final : Program} {code : List Modules.Command} {exports : Environment}
    (profile : Plan globals env source seed code final exports) :
    (source.mapM (elaborateCommand ⟨(moduleLex globals).context, .global⟩)) seed = .ok (code, final) := by
  induction profile with
  | done => rfl
  | define root _ later =>
    simp [List.mapM_cons, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, root_compiles root, later]
  | @assign _ name operand rhs reads _ _ _ seed _ _ _ lexical _ _ later =>
    have compiled := elaborateCommand_assign ⟨(moduleLex globals).context, .global⟩ name operand seed
    rw [show resolveTracked (moduleLex globals).context operand = .ok (rhs, reads) from
      (by simp [resolveTracked, Body.resolves_at lexical [], Except.map])] at compiled
    simp [List.mapM_cons, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, Except.mapError, Except.map, compiled, later]
  | invoke call _ _ _ later =>
    have callee : Body.Operand (moduleLex globals) (.scalar (.read call.callee))
        (Leaf.readOperand (globalSlot call.callee)) [globalSlot call.callee] :=
      .read call.legal (.global (by simp [moduleLex]) (by simp [moduleLex]) call.calleeGlobal)
        (.module (by simp [moduleLex]) (by simp [moduleLex]) call.calleeGlobal)
    have resolved := resolves_at (globalSlot call.callee) callee call.operands call.keywords call.star call.mapping
    simp [Invocation.source, Invocation.code, List.mapM_cons, elaborateCommand_assign, resolved,
      bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, Except.mapError, Except.map, later]

theorem plan_declares {globals : List String} {env : Environment}
    {source : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {seed final : Program} {code : List Modules.Command} {exports : Environment}
    (profile : Plan globals env source seed code final exports) :
    Block.ModuleBinders source (Trace.names source) := by
  induction profile with
  | done => exact .nil
  | define root _ rest => exact .cons (.define root.site.name _ _) rest
  | assign _ _ _ _ rest => exact .cons (.assign _ _) rest
  | invoke call _ _ _ rest => exact .cons (.assign call.destination _) rest

theorem preserves {globals : List String} {env : Environment} {source : List Silmaril.Languages.Starlark.Modules.Resolve.Command}
    {seed final : Program} {code : List Modules.Command} {exports : Environment}
    (profile : Plan globals env source seed code final exports) :
    PreservesDeclarations seed final := by
  induction profile with
  | done => exact fun _ _ found => found
  | define root _ later =>
    intro id declaration found
    have body :=
      (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call.Suite.Provenance.links
        root.suite).1 _ _ found
    exact later _ _ (by simp [Root.table, Array.getElem?_push, Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp body).choose, body])
  | assign _ _ _ _ later => exact later
  | invoke _ _ _ _ later => exact later

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
