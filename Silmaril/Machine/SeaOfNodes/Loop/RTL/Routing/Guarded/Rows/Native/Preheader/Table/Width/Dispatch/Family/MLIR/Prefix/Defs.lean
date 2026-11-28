module

public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Defs
public import Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.Phi.Thms

/-! Bounded prefixes of reached feedback occurrences in the actual CF and RTL targets. -/

@[expose] public section

namespace Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix

open Silmaril.Machine.Lir (Memory)
open Silmaril.Machine.RTL (Frame packValues)
open Silmaril.Machine.RTL.SSA (Block Prog StepsNWithin)
open Silmaril.Machine.SeaOfNodes.Diamond.RTL (PortTy Reg model)
open Silmaril.Machine.SeaOfNodes.Loop.RTL.MLIR.CF (i64)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.Loop (appendTuple)
open Silmaril.SSA.SeaOfNodes.MLIR (sourceInputs)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (TargetOp evalOp)
open Silmaril.SSA.PhiView (latch)

variable {old new tests : Nat} {rtlEntry rtlHeader : List (List PortTy)}
variable {entrySigs sigs : List (List (Diamond.Ty Width))}

/-- Use the typed native bank as a CF environment, with no new evaluation. -/
def wordEnv : {n : Nat} → WordTuple n → Env (wordsTy n)
  | 0, .nil => .nil
  | _ + 1, .cons value rest => .cons value (wordEnv rest)

/-- Witnesses tying the same actual RTL program to the typed CF dispatcher and Φ view.
The origin map gives the native, typed meaning of each transported register. -/
structure Setup (mapping : InputMap old new) (source : Family.Source old old rtlEntry rtlHeader tests)
    (g : Program new old entrySigs sigs) (wires : Live new old sigs) where
  rtl : Prog Reg
  accepted : Family.lowerChecked mapping source = some rtl
  plan : Plan (lowerFunc (mapCaptures mapping source)) (liveRegs wires) old tests
  phi : Phi.Checked (lowerFunc (mapCaptures mapping source)) tests
  origin : Fin (liveRegs wires).length → HeaderWord new old rtlHeader
  register_eq : ∀ i, register (origin i).address = (liveRegs wires)[i]

variable {mapping : InputMap old new} {source : Family.Source old old rtlEntry rtlHeader tests}
variable {g : Program new old entrySigs sigs} {wires : Live new old sigs}

def Setup.cf (sys : Setup mapping source g wires) := lower g wires sys.plan

def livePacket (g : Program new old entrySigs sigs) (wires : Live new old sigs)
    (input : WordTuple new) (carried : WordTuple old) : Env (wordsTy wires.length) :=
  let args := appendTuple (sourceInputs (wordEnv carried)) (sourceInputs (wordEnv input))
  readLive args (g.header.eval Loop.MLIR.CF.model args PUnit.unit) wires

/-- The remaining producer-table obligation, stated before control transfer.
The CF table agrees with native reads on the guard and declared live origins. -/
def HeaderMatch (sys : Setup mapping source g wires) (input : WordTuple new) (carried : WordTuple old) : Prop :=
  let rtlArgs := appendTuple carried input
  let rtlLocals := (mapCaptures mapping source).primary.header.eval model rtlArgs PUnit.unit
  let cfArgs := appendTuple (sourceInputs (wordEnv carried)) (sourceInputs (wordEnv input))
  let cfLocals := g.header.eval Loop.MLIR.CF.model cfArgs PUnit.unit
  (Diamond.read Loop.MLIR.CF.model g.predicate cfArgs cfLocals).down =
    (Diamond.read model (mapCaptures mapping source).primary.predicate rtlArgs rtlLocals).down ∧
  ∀ i, (livePacket g wires input carried |>.append (wordEnv input)).get
      (argAt wires.length (i.cast (List.length_map ..))) =
    Diamond.read model (sys.origin i) rtlArgs rtlLocals

abbrev headerFrame (live tests : Nat) (values : WordTuple old) : Silmaril.MLIR.CF.Frame (Label live old tests) :=
  ⟨.header, wordEnv values⟩

abbrev dispatchFrame (bank : Nat) (slot : Fin (tests + 1)) {live : Nat} (packet : Env (wordsTy live)) :
    Silmaril.MLIR.CF.Frame (Label live bank tests) :=
  ⟨.dispatch slot, packet⟩

/-- A bounded prefix of actual CF block evaluations, stopped at a typed frame.
Each step uses the existing Code and Terminator evaluators. -/
inductive Transfers {live : Nat}
    (cfg : Silmaril.MLIR.CF.Cfg TargetOp (Label live old tests) (wordsTy new) [i64])
    (input : Env (wordsTy new)) :
    Nat → Silmaril.MLIR.CF.Frame (Label live old tests) → Silmaril.MLIR.CF.Frame (Label live old tests) → Prop
  | refl (state) : Transfers cfg input 0 state state
  | next {start middle finish count}
      (taken : (cfg.block start.label).eval evalOp (fun term env => term.eval env)
        (start.args.append input) = .inl middle)
      (rest : Transfers cfg input count middle finish) :
      Transfers cfg input (count + 1) start finish

/-- One reached feedback cut records both real paths and the exact explicit-Φ latch. -/
structure Visit (sys : Setup mapping source g wires) (input : WordTuple new) (mem : Memory)
    (slot : Fin (tests + 1)) (carried next : WordTuple old) (before after : Frame Reg) : Prop where
  rtlPath : StepsNWithin sys.rtl [] (rtlHeader.length + 1 + (slot.val + 1))
    ⟨⟨0, 1, 0⟩, before, [], mem⟩ ⟨⟨0, 1, 0⟩, after, [], mem⟩
  cfPath : Transfers sys.cf (wordEnv input) (slot.val + 2) (headerFrame _ _ carried) (headerFrame _ _ next)
  cut : ∃ ready block,
    FeedbackCut (mapCaptures mapping source) sys.rtl input carried before ready after mem slot next block ∧
    Snapshot (scope := liveRegs wires) (List.length_map ..) ((livePacket g wires input carried).append (wordEnv input))
      ready ∧
    latch sys.phi.view (sys.phi.edge slot.succ) (Phi.snapshot (lowerFunc (mapCaptures mapping source)).allDefs ready) =
      packValues (words next)

/-- Specify the reached native choices and the local producer obligation at each visit.
An empty prefix can stop at any header. -/
inductive Admitted (sys : Setup mapping source g wires) (input : WordTuple new) :
    List (Fin (tests + 1)) → WordTuple old → WordTuple old → Prop
  | stop (bank) : Admitted sys input [] bank bank
  | visit {slot slots bank next finish} (aligned : HeaderMatch sys input bank)
      (taken : source.step (mapping.pull input) bank = .inr (slot, next))
      (rest : Admitted sys input slots next finish) : Admitted sys input (slot :: slots) bank finish

/-- RTL counts each producer, the header branch and the inspected dispatchers. -/
def rtlCost (headerSize : Nat) (slots : List (Fin (tests + 1))) : Nat :=
  (slots.map (fun slot => headerSize + 1 + (slot.val + 1))).sum

/-- CF counts one block for the header and one per inspected dispatcher. -/
def cfCost (slots : List (Fin (tests + 1))) : Nat :=
  (slots.map (fun slot => slot.val + 2)).sum

/-- The cut invariant includes the exact carried words, per-visit evidence and full RTL memory. -/
inductive Realized (sys : Setup mapping source g wires) (input : WordTuple new) (mem : Memory) :
    List (Fin (tests + 1)) → WordTuple old → Frame Reg → WordTuple old → Frame Reg → Prop
  | stop {bank frame} (matched : ArgsMatch frame (appendTuple bank input)) :
      Realized sys input mem [] bank frame bank frame
  | visit {slot slots bank next finish before after final}
      (taken : Visit sys input mem slot bank next before after)
      (rest : Realized sys input mem slots next after finish final) :
      Realized sys input mem (slot :: slots) bank before finish final

end Silmaril.Machine.SeaOfNodes.Loop.RTL.Routing.Guarded.Rows.Native.Preheader.Table.Width.Dispatch.Family.MLIR.Prefix
