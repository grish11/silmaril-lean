module

public import Silmaril.Semantics.Region.Effects.Defs

/-! # Indexed effects with independently chosen payloads

A small analysis vocabulary; these declarations are not an ISA semantics.
Reads and writes intentionally have different domains. The call summary lives
in an extra layer and does not become a direct effect of the call instruction.
-/

@[expose] public section
namespace Silmaril.Semantics.Region.Effects.Examples

/-- Different domains by category; no common register/address/instruction type. -/
def Payload : DirectKind → Type
  | .clobber => Fin 16
  | .read => Nat
  | .write => String
  | .instruction => String
  | .call => String
  | .syscall => Fin 512
  | .ub | .trap | .fault | .raise => Unit

/-- Extend an existing alphabet without changing its definitions. -/
inductive Layer where
  | direct (kind : DirectKind)
  | callSummary

def LayerPayload : Layer → Type
  | .direct kind => Payload kind
  | .callSummary => Set (Atom Payload)

def embedDirect : Renaming Payload LayerPayload := ⟨Layer.direct, fun _ value => value⟩

def projectDirect : Atom LayerPayload → Option (Atom Payload)
  | ⟨.direct kind, value⟩ => some ⟨kind, value⟩
  | ⟨.callSummary, _⟩ => none

def load : Atom Payload := ⟨.read, (4096 : Nat)⟩
def store : Atom Payload := ⟨.write, "output"⟩
def ub : Atom Payload := ⟨.ub, ()⟩
def call : Atom Payload := ⟨.call, "callee"⟩
def syscall : Atom Payload := ⟨.syscall, (1 : Fin 512)⟩

/-- A callee's summary is not part of the direct call-site set. -/
def directCall : Set (Atom Payload) := {call}
def calleeSummary : Set (Atom Payload) := {syscall, store}

abbrev signature : BlockSignature :=
  ⟨DirectKind, Payload, Fin 16, ControlOutcome Nat String⟩

/-- Three possible instruction roles for a deterministic analysis example. -/
inductive Op where
  | define | use | branch
  deriving DecidableEq

def analyze : Op → InstructionSummary signature
  | .define => ⟨{⟨.instruction, "define"⟩}, ⟨∅, {0}⟩, {.next 1}⟩
  | .use => ⟨{⟨.instruction, "use"⟩}, ⟨{0}, ∅⟩, {.next 2}⟩
  | .branch => ⟨{⟨.instruction, "branch"⟩}, ⟨∅, ∅⟩, {.next 8, .next 12}⟩

def block : Block Op := ⟨[.define, .use], .branch⟩

def contract : BlockContract Op signature where
  analyze := analyze
  interior := fun op => op ≠ .branch
  directSound := fun op effects => effects = (analyze op).direct
  controlSound := fun op effects => effects = (analyze op).control

/-- An internal halt is observable even when it emits no direct event. -/
def faulting : TransitionSystem Unit Nat (Atom Payload) String where
  pc := fun _ => 0
  step := fun _ _ _ => False
  halt := fun _ reason => reason = "fault"

end Silmaril.Semantics.Region.Effects.Examples
