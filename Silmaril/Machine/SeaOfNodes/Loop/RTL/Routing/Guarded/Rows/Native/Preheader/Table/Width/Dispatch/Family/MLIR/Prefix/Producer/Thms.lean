module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Thms

import Silmaril.Proofs.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer.Schedule

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer

open Silmaril.Machine.Lir (Memory Word)
open Silmaril.Machine.RTL (Frame)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (evalOp)

variable {old new tests : Nat} {entrySigs sigs : List (List PortTy)}
variable {mapping : InputMap old new} {source : Family.Source old old entrySigs sigs tests}
variable {origins : List (HeaderWord new old sigs)}

/-- Translate the producer tables, check the emitted RTL and admit the ordered
live scope against its actual dispatcher blocks and explicit-Φ view. -/
def compile (mapping : InputMap old new) (source : Family.Source old old entrySigs sigs tests)
    (origins : List (HeaderWord new old sigs)) : Option (Compiled mapping source origins) :=
  (Family.lowerChecked mapping source).pbind fun rtl accepted =>
    (graph (mapCaptures mapping source).primary).pbind fun program translated => do
      let fn := lowerFunc (mapCaptures mapping source)
      let plan ← MLIR.check fn (liveRegs (live origins)) old tests
      let phi ← Phi.extract fn tests
      pure ⟨program, translated, rtl, accepted, plan, phi⟩

theorem live_register (origins : List (HeaderWord new old sigs))
    (i : Fin (liveRegs (live origins)).length) :
    register (liveOrigin origins i).address = (liveRegs (live origins))[i] :=
  Proofs.live_register origins i

/-- The prefix consumes the same native origins that provided the CF scope. -/
def Compiled.setup (compiled : Compiled mapping source origins) :
    Setup mapping source compiled.program (live origins) where
  rtl := compiled.rtl
  accepted := compiled.accepted
  plan := compiled.plan
  phi := compiled.phi
  origin := liveOrigin origins
  register_eq := live_register origins

/-- On every header visit, evaluate both producer tables on the same captures
and carried bank. The signed guard and every transported word agree. -/
theorem header_match (compiled : Compiled mapping source origins)
    (input : WordTuple new) (carried : WordTuple old) :
    HeaderMatch compiled.setup input carried :=
  Proofs.header_match origins compiled.setup (fun _ => rfl) compiled.translated input carried

/-- The actual CF entry passes the same initial bank as the checked RTL entry
at the pulled capture valuation. -/
theorem entry_frame (compiled : Compiled mapping source origins) (input : WordTuple new) :
    compiled.setup.cf.entry.eval evalOp (fun term env => term.eval env) (wordEnv input) =
      .inl (headerFrame _ _ (source.primary.initial model (mapping.pull input))) :=
  Proofs.entry_frame compiled.setup compiled.translated input

/-- The emitted CF false successor carries the word read from the same typed
origin as the actual RTL false successor. -/
theorem header_exit (compiled : Compiled mapping source origins)
    (input : WordTuple new) (carried : WordTuple old) (value : Word)
    {before ready : Frame Reg} {mem : Memory}
    (cut : Family.ExitCut (mapCaptures mapping source) compiled.rtl input carried before ready mem value) :
    (compiled.setup.cf.block .header).eval evalOp (fun term env => term.eval env)
      ((wordEnv carried).append (wordEnv input)) = .inl ⟨.exit, .cons value .nil⟩ :=
  Proofs.header_exit compiled.setup compiled.translated input carried value cut

/-- Compose real CF/RTL feedback steps and explicit-Φ latches along the native
prefix. Only the starting frame relation and native occurrence choices are
needed from the caller. -/
theorem prefix_correct (compiled : Compiled mapping source origins)
    (input : WordTuple new) (mem : Memory) {slots : List (Fin (tests + 1))}
    {carried finish : WordTuple old}
    (taken : Feedbacks source (mapping.pull input) slots carried finish) (before : Frame Reg)
    (matched : ArgsMatch before (appendTuple carried input)) :
    ∃ after, Realized compiled.setup input mem slots carried before finish after :=
  Proofs.prefix_correct compiled.setup input mem
    (header_match compiled input) taken before matched

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix.Producer
