module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.WriterPaths
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackEndWriters

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Game.HandleAccept.Wit
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled
open LiveDispatch ComponentCall.Delivery.FiniteSession ReturnFrame.Occurrence

variable {grow : SingleThreaded.GrowOracle} {sig : Signature} {profile : ProfileKind}
  {ready : HostReady (HostState sig)} {bindings : List (Binding sig)} {base : HostImpl (core3 grow) (HostState sig)}
  {start incoming left right finish : Config (core3 grow) (HostState sig)}
  {actual checked canonical trailing : Trace grow sig} {marks : List (Option Location)}
  {older : ReturnFrame.Substitutions (core3 grow) (HostState sig)}

private theorem appendSteps {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))}
    (front : Steps profile ready dispatch start checked left) (back : Steps profile ready dispatch left trailing finish) :
    Steps profile ready dispatch start (checked ++ trailing) finish := by
  induction front with
  | refl => exact back
  | cons step _ ih => exact .cons step (ih back)

private def PrefixCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checked canonical trailing left right marks, actual = checked ++ trailing ∧
    OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks ∧
    VisitorWriterPath profile ready base bindings start incoming checked canonical left right ∧
    Steps profile ready (specDispatch ready base) left trailing finish

private theorem stop (run : Steps profile ready (specDispatch ready base) start actual finish) :
    PrefixCut profile ready base bindings start incoming actual finish :=
  ⟨[], [], actual, start, incoming, [], rfl,
    CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place), WriterPaths.empty, run⟩

private theorem terminal (paths : OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks)
    (writers : VisitorWriterPath profile ready base bindings start incoming checked canonical left right)
    (run : Steps profile ready (specDispatch ready base) left trailing finish) :
    PrefixCut profile ready base bindings start incoming (checked ++ trailing) finish :=
  ⟨checked, canonical, trailing, left, right, marks, rfl, paths, writers, run⟩

private theorem follow (paths : OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks)
    (writers : VisitorWriterPath profile ready base bindings start incoming checked canonical left right)
    (tail : PrefixCut profile ready base bindings left right trailing finish) :
    PrefixCut profile ready base bindings start incoming (checked ++ trailing) finish := by
  obtain ⟨moreChecked, moreCanonical, rest, lhs, rhs, _, rfl, movement, effects, run⟩ := tail
  obtain ⟨_, transport, _⟩ := CallbackPrefix.transportAppend paths movement
  exact ⟨checked ++ moreChecked, canonical ++ moreCanonical, rest, lhs, rhs, _,
    (List.append_assoc ..).symm, transport, writers.append effects, run⟩

private theorem oneFrame {dispatch : Call (core3 grow) → Session grow sig (Ret (core3 grow))} {label}
    (run : Steps profile ready dispatch start [label] left) (writer : left.host.writer = start.host.writer) :
    WriterPath profile ready dispatch start [label] left [] := by
  cases run with
  | cons step tail => cases tail; exact .same step writer (.done _)

private theorem directReply {caller resume reply}
    (cut : CheckedProgramReplyCut profile ready (specDispatch ready base) start caller resume reply actual finish) :
    PrefixCut profile ready base bindings start incoming actual finish := by
  cases cut with
  | «prefix» _ _ _ writers paths =>
    simpa only [List.append_nil] using terminal
      (CallbackPrefix.stationaryTransport paths (fun place => .done incoming place))
      (.framed writers (.done incoming)) (.refl _)
  | popped written writers remaining _ _ =>
    -- The checked pop belongs to the residual because the raw occurrence is still pending.
    exact terminal (checked := [.tau, .tau])
      (CallbackPrefix.stationaryTransport written (fun place => .done incoming place))
      (.framed writers (.done incoming)) remaining

private theorem directPreparation {caller resume request ticket selected field}
    (cut : DirectGivePreparationCut profile ready base bindings start incoming caller resume request ticket selected field actual finish) :
    PrefixCut profile ready base bindings start incoming actual finish := by
  cases cut with
  | «prefix» _ paths writers =>
    simpa only [List.append_nil] using terminal paths (.framed writers (.done _)) (.refl _)
  | reached _ _ readSite paths writers _ refused prepared =>
    obtain ⟨_, read⟩ := readSite
    apply follow (CallbackPrefix.stationaryTransport paths (fun place => .done _ place)) (.prepare read writers (.done _))
    cases verdict : Stored.OwnedMemory.Claims.Record.prepare start.store start.host.writer field.objects with
    | error issue => exact directReply (refused issue verdict)
    | ok result =>
      cases result
      cases prepared verdict with
      | «prefix» paths => exact terminal paths WriterPaths.empty (.refl _)
      | reached _ _ paths writers residual decision =>
        apply follow (CallbackPrefix.stationaryTransport paths (fun place => .done incoming place))
          (.framed writers (.done incoming))
        rcases decision with ⟨_, reply⟩ | _
        · exact directReply reply
        · exact stop residual

private theorem cut (ending : CallbackSliceEnd profile ready base bindings older start incoming actual finish) :
    PrefixCut profile ready base bindings start incoming actual finish := by
  induction ending with
  | exhausted => exact stop (.refl _)
  | boundary _ step tail => exact stop (.cons step tail)
  | observation _ _ paths tail => exact stop (appendSteps (paths.choose_spec.1 none).1.steps tail)
  | pendingAssignment _ _ _ _ paths same =>
    obtain ⟨checked, canonical⟩ := paths.choose_spec.1 none
    exact terminal paths (.framed (oneFrame checked.steps same.1) (oneFrame canonical.steps same.2)) (.refl _)
  | componentEntryPrefix _ _ _ paths writers => simpa only [List.append_nil] using terminal paths writers (.refl _)
  | componentObserverTerminal _ paths writers tail => exact terminal paths writers tail
  | componentPreflightMismatch _ _ _ _ paths writers tail => exact terminal paths writers tail
  | componentRefusedTerminal _ _ paths writers tail => exact terminal paths writers tail
  | componentRegistrationMismatch _ _ paths writers _ tail => exact terminal paths writers tail
  | componentAcceptedTerminal _ _ paths writers _ tail => exact terminal paths writers tail
  | refused _ _ paths writers reply =>
    obtain ⟨_, _, rfl, _, _, tail, _, _, _, ⟨_, written, framed, pop⟩, _⟩ := reply
    apply follow paths writers
    exact terminal (checked := [.tau, .tau])
      (CallbackPrefix.stationaryTransport written (fun place => .done _ place))
      (.framed (WriterPaths.ofHostFrames framed) (.done _)) (.cons pop tail)
  | entryPrefix _ run _ _ => exact stop run
  | directGiveEntry _ _ _ _ paths _ _ _ tail => exact stop (appendSteps (paths.choose_spec.1 none).1.steps tail)
  | admissionTrap _ _ _ checked _ tail => exact stop (appendSteps checked tail)
  | directGiveTrap body _ _ _ => exact terminal body.paths body.writers body.residual
  | giveLookupMismatch _ body _ _ _ _ _ _ => exact terminal body.paths body.writers body.residual
  | directGiveSelected _ _ body _ _ _ _ compiler =>
    apply follow body.paths body.writers
    rcases compiler with ⟨_, _, _, _, preparation⟩ | ⟨_, _, reply⟩
    · exact directPreparation preparation
    · exact directReply reply
  | compilerRefused _ _ _ _ _ _ _ _ _ reached =>
    obtain ⟨_, _, _, split, body⟩ := reached
    exact split.symm ▸ terminal body.paths body.writers body.residual
  | placementTrap _ _ _ _ _ _ _ _ _ reached =>
    obtain ⟨_, _, _, split, body⟩ := reached
    exact split.symm ▸ terminal body.paths body.writers body.residual
  | body _ body ending =>
    cases ending with
    | coreRefusalPrefix _ _ _ _ writers paths =>
      apply follow body.paths body.writers
      simpa only [List.append_nil] using terminal
        (CallbackPrefix.stationaryTransport paths (fun place => .done _ place))
        (.framed writers (.done _)) (.refl _)
    | _ => exact terminal body.paths body.writers body.residual
  | directGiveLateReply _ _ body _ reply => exact follow body.paths body.writers (directReply reply)
  | directGiveFinite body => simpa only [List.append_nil] using terminal body.paths body.writers body.residual
  | allocator _ body _ _ _ _ ih => exact follow body.paths body.writers ih
  | uncertified _ _ _ paths tail => exact stop (appendSteps (paths.choose_spec.1 none).1.steps tail)
  | pollTerminal paths writers _ _ _ tail => exact terminal paths writers tail
  | waitTerminal paths writers _ _ tail => exact terminal paths writers tail
  | cancelTerminal paths writers _ _ _ tail => exact terminal paths writers tail
  | cancelHookBody paths writers _ _ _ ih => exact follow paths writers ih
  | cancelDecisionTerminal paths writers _ _ _ tail => exact terminal paths writers tail
  | cancelParked paths writers _ _ ih => exact follow paths writers ih

theorem extend {pending : Stored.OwnedMemory.Claims.Spend → Prop}
    (split : actual = checked ++ trailing)
    (segment : ExecutedCallbackSegment profile ready base bindings older start incoming checked canonical left right)
    (ending : CallbackSliceEnd profile ready base bindings older left right trailing finish)
    (initial : start.host.writer.ClaimDiscrepancies incoming.host.writer pending) :
    ∃ compared raw residual reached peer marks, actual = compared ++ residual ∧
      OccurrenceTransport profile ready base bindings start incoming compared raw reached peer marks ∧
      VisitorWriterPath profile ready base bindings start incoming compared raw reached peer ∧
      WriterDiscrepancyCut profile ready base bindings start incoming pending compared raw reached peer ∧
      Steps profile ready (specDispatch ready base) reached residual finish := by
  obtain ⟨compared, raw, residual, reached, peer, marks, eq, paths, writers, tail⟩ :=
    follow segment.occurrences segment.writers (cut ending)
  exact ⟨compared, raw, residual, reached, peer, marks, split.trans eq, paths, writers,
    WriterPaths.discrepancyCut writers initial, tail⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackEndWriters
