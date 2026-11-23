module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Component.Delivery.Session.LiveDispatch.Plan.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackPrefix
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.WriterPaths
import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Occurrence.Thms
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Scheduled.Plain.Thms

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

private def PrefixCut (profile : ProfileKind) (ready : HostReady (HostState sig))
    (base : HostImpl (core3 grow) (HostState sig)) (bindings : List (Binding sig))
    (start incoming : Config (core3 grow) (HostState sig)) (actual : Trace grow sig)
    (finish : Config (core3 grow) (HostState sig)) : Prop :=
  ∃ checked canonical trailing left right marks, actual = checked ++ trailing ∧
    OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks ∧
    VisitorWriterPath profile ready base bindings start incoming checked canonical left right ∧
    CheckedTerminalWriterTail profile ready (specDispatch ready base) left trailing finish

private theorem stop (run : Steps profile ready (specDispatch ready base) start actual finish) :
    PrefixCut profile ready base bindings start incoming actual finish :=
  ⟨[], [], actual, start, incoming, [], rfl,
    CallbackPrefix.stationaryTransport (fun place => .done _ place) (fun place => .done _ place), WriterPaths.empty, .residual run⟩

private theorem terminal (paths : OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks)
    (writers : VisitorWriterPath profile ready base bindings start incoming checked canonical left right)
    (run : Steps profile ready (specDispatch ready base) left trailing finish)
    (ending : CheckedTerminalWriterTail profile ready (specDispatch ready base) left trailing finish := .residual run) :
    PrefixCut profile ready base bindings start incoming (checked ++ trailing) finish :=
  ⟨checked, canonical, trailing, left, right, marks, rfl, paths, writers, ending⟩

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
  | popped written writers remaining _ residual =>
    exact terminal (checked := [.tau, .tau])
      (CallbackPrefix.stationaryTransport written (fun place => .done incoming place))
      (.framed writers (.done incoming)) remaining
      (.executed (.popProg rfl) (.inl rfl) rfl residual)

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
        rcases decision with ⟨_, reply⟩ | ⟨_, _, placement⟩
        · exact directReply reply
        · cases placement with
          | «prefix» tracks writers _ =>
            simpa only [List.append_nil] using terminal
              (CallbackPrefix.stationaryTransport tracks (fun place => .done incoming place))
              (.framed writers (.done incoming)) (.refl _)
          | trapped _ beforeTrap writers _ _ tail =>
            rw [List.append_assoc]
            exact terminal (CallbackPrefix.stationaryTransport beforeTrap.tracks (fun place => .done incoming place))
              (.framed writers (.done incoming)) (.cons beforeTrap.fault tail)
              (.executed beforeTrap.fault (.inr rfl) (congrArg HostState.writer beforeTrap.host.symm) tail)
          | reached _ _ _ tracks writers _ tail =>
            exact terminal (CallbackPrefix.stationaryTransport tracks (fun place => .done incoming place))
              (.framed writers (.done incoming)) tail

private theorem cut (ending : CallbackSliceEnd profile ready base bindings older start incoming actual finish) :
    PrefixCut profile ready base bindings start incoming actual finish := by
  induction ending with
  | exhausted => exact stop (.refl _)
  | boundary _ step tail => exact stop (.cons step tail)
  | observation _ _ paths writers tail => exact terminal paths writers tail
  | pendingAssignment _ _ _ _ paths same =>
    obtain ⟨checked, canonical⟩ := paths.choose_spec.1 none
    exact terminal paths (.framed (oneFrame checked.steps same.1) (oneFrame canonical.steps same.2)) (.refl _)
  | coreAcceptTerminal paths writers residual _ => exact terminal paths writers residual
  | sharedDropWorker _ _ _ _ _ _ _ paths writers _ residual => exact terminal paths writers residual
  | sharedDropCompared _ _ paths writers compared _ ih =>
    exact follow paths writers (follow compared.occurrences compared.writers ih)
  | sharedGiveProbeMismatch _ _ _ paths writers residual => exact terminal paths writers residual
  | comparedPrefix paths writers _ ih => exact follow paths writers ih
  | sharedRecordAllocator paths writers _ compared _ ih =>
    simpa only [List.append_assoc] using follow paths writers (follow compared.occurrences compared.writers ih)
  | sharedRecordAllocatorPop _ _ _ _ _ paths writers _ ih => exact follow paths writers ih
  | sharedRecordPrepareMismatch _ paths writers residual => exact terminal paths writers residual
  | sharedRecordOwnerMismatch _ paths writers residual => exact terminal paths writers residual
  | sharedRecordEndpointMismatch _ paths writers residual => exact terminal paths writers residual
  | sharedGiveSelectionMismatch _ _ _ paths writers residual => exact terminal paths writers residual
  | componentEntryPrefix _ _ _ paths writers => simpa only [List.append_nil] using terminal paths writers (.refl _)
  | componentObserverTerminal _ paths writers tail => exact terminal paths writers tail
  | componentPreflightMismatch _ _ _ _ paths writers tail => exact terminal paths writers tail
  | componentRefusedTerminal _ _ paths writers tail => exact terminal paths writers tail
  | componentRegistrationMismatch _ _ paths writers _ tail => exact terminal paths writers tail
  | componentAcceptedTerminal _ _ paths writers _ tail => exact terminal paths writers tail
  | componentReplyDisplaced _ _ _ paths writers tail => exact terminal paths writers tail
  | refused _ _ paths writers reply =>
    obtain ⟨_, _, rfl, _, _, tail, _, _, complete, ⟨_, written, framed, pop, edit⟩, _⟩ := reply
    apply follow paths writers
    exact terminal (checked := [.tau, .tau])
      (CallbackPrefix.stationaryTransport written (fun place => .done _ place))
      (.framed (WriterPaths.ofHostFrames framed) (.done _)) (.cons pop tail)
      (.executed pop (.inl edit) (complete.project_eq.trans framed.project_eq.symm) tail)
  | directGiveTrap body _ _ _ => exact terminal body.paths body.writers body.residual
  | giveLookupMismatch _ body _ _ _ _ _ _ => exact terminal body.paths body.writers body.residual
  | directGiveSelected _ _ body _ _ _ _ compiler =>
    apply follow body.paths body.writers
    rcases compiler with ⟨_, _, _, _, preparation⟩ | ⟨_, _, reply⟩
    · exact directPreparation preparation
    · exact directReply reply
  | compilerRefused _ _ _ _ _ _ _ _ _ reached =>
    obtain ⟨_, _, _, split, body, ending⟩ := reached
    exact split.symm ▸ terminal body.paths body.writers body.residual ending
  | placementTrap _ _ _ _ _ _ _ _ _ reached =>
    obtain ⟨_, _, _, split, body, ending⟩ := reached
    exact split.symm ▸ terminal body.paths body.writers body.residual ending
  | body _ body ending =>
    cases ending with
    | coreReplyPrefix _ reached =>
      apply follow body.paths body.writers
      simpa only [List.append_nil] using terminal
        (CallbackPrefix.stationaryTransport reached.paths (fun place => .done _ place))
        (.framed reached.writers (.done _)) (.refl _)
    | _ => exact terminal body.paths body.writers body.residual
  | directGiveLateReply _ _ body _ reply => exact follow body.paths body.writers (directReply reply)
  | directGiveFinite body => simpa only [List.append_nil] using terminal body.paths body.writers body.residual
  | allocator _ body _ _ _ _ ih => exact follow body.paths body.writers ih
  | nonGrowing _ _ paths writers tail => exact terminal paths writers tail
  | pollTerminal paths writers _ _ _ tail => exact terminal paths writers tail
  | waitTerminal paths writers _ _ tail => exact terminal paths writers tail
  | cancelTerminal paths writers _ _ _ tail => exact terminal paths writers tail
  | cancelHookBody paths writers _ _ _ ih => exact follow paths writers ih
  | cancelDecisionTerminal paths writers _ _ _ tail => exact terminal paths writers tail
  | cancelParked paths writers _ _ ih => exact follow paths writers ih

theorem extend {pending : Stored.OwnedMemory.Claims.Spend → Prop}
    (segment : ExecutedCallbackSegment profile ready base bindings older start incoming checked canonical left right)
    (ending : CallbackSliceEnd profile ready base bindings older left right trailing finish)
    (initial : start.host.writer.ClaimDiscrepancies incoming.host.writer pending) :
    ∃ compared raw residual reached peer marks, trailing = compared ++ residual ∧
      OccurrenceTransport profile ready base bindings start incoming (checked ++ compared) (canonical ++ raw) reached peer marks ∧
      VisitorWriterPath profile ready base bindings start incoming (checked ++ compared) (canonical ++ raw) reached peer ∧
      WriterDiscrepancyCut profile ready base bindings start incoming pending (checked ++ compared) (canonical ++ raw) reached peer ∧
      CheckedTerminalWriterTail profile ready (specDispatch ready base) reached residual finish := by
  obtain ⟨compared, raw, residual, reached, peer, _, split, endingPaths, endingWriters, tail⟩ := cut ending
  obtain ⟨_, paths, _⟩ := CallbackPrefix.transportAppend segment.occurrences endingPaths
  have writers := segment.writers.append endingWriters
  exact ⟨compared, raw, residual, reached, peer, _, split, paths, writers,
    WriterPaths.discrepancyCut writers initial, tail⟩

theorem complete {pending : Stored.OwnedMemory.Claims.Spend → Prop}
    (paths : OccurrenceTransport profile ready base bindings start incoming checked canonical left right marks)
    (writers : VisitorWriterPath profile ready base bindings start incoming checked canonical left right)
    (tail : CheckedTerminalWriterTail profile ready (specDispatch ready base) left trailing finish)
    (initial : start.host.writer.ClaimDiscrepancies incoming.host.writer pending) :
    ∃ taken residual reached, trailing = taken ++ residual ∧
      ((taken = [] ∧ reached = left) ∨ ∃ label, taken = [label] ∧
        Step profile ready (specDispatch ready base) left label reached ∧
        (transitionEdit left label = .pop ∨ transitionEdit left label = .clear)) ∧
      (∀ cursor, ∃ checkedMark rawMark,
        Trail profile ready (specDispatch ready base) start cursor (checked ++ taken) reached checkedMark ∧
        Trail profile ready (specDispatch ready (LiveDispatch.host bindings base)) incoming cursor canonical right rawMark ∧
        ((taken = [] ∧ checkedMark = rawMark) ∨
          ∃ label, taken = [label] ∧ checkedMark = rawMark.bind (transitionEdit left label).follow)) ∧
      VisitorWriterPath profile ready base bindings start incoming (checked ++ taken) canonical reached right ∧
      WriterDiscrepancyCut profile ready base bindings start incoming pending (checked ++ taken) canonical reached right ∧
      Steps profile ready (specDispatch ready base) reached residual finish := by
  obtain ⟨move, tracks, _⟩ := paths
  cases tail with
  | residual run =>
    refine ⟨[], _, left, rfl, .inl ⟨rfl, rfl⟩, ?_, ?_, ?_, run⟩
    · intro cursor
      obtain ⟨lhs, rhs⟩ := tracks cursor
      exact ⟨_, _, by simpa only [List.append_nil] using lhs, rhs, .inl ⟨rfl, rfl⟩⟩
    · simpa only [List.append_nil] using writers
    · simpa only [List.append_nil] using WriterPaths.discrepancyCut writers initial
  | executed step edit writer run =>
    have path := writers.append (.framed (.same step writer (.done _)) (.done right))
    rw [List.append_nil] at path
    refine ⟨[_], _, _, rfl, .inr ⟨_, rfl, step, edit⟩, ?_, path, WriterPaths.discrepancyCut path initial, run⟩
    intro cursor
    obtain ⟨lhs, rhs⟩ := tracks cursor
    exact ⟨_, _, lhs.append (.step step (.done _ _)), rhs, .inr ⟨_, rfl, rfl⟩⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Delivery.CallbackEndWriters
