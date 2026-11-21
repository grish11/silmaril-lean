module

public import Silmaril.Wasm.Component.Reference.Machine.ReturnFrame.Defs

@[expose] public section

namespace Silmaril.Wasm.Component.Machine.HostFrame

open Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {E : CoreEngine} {Host : Type}

/-- Alter embedder data without changing scheduler control, the component
store, or the pending calls, resolutions, and cancellation records. -/
def replace (cfg : Config E Host) (other : Host) : Config E Host := { cfg with host := other }

/-- The reached host read leads to different residual programs. Both reads
take an actual scheduler step; neither mutates either store or host. -/
inductive ReadCut : Config E Host → Host → Label E Host → Config E Host → Config E Host → Prop where
  | mk {cfg : Config E Host} {other : Host} {thread frames rest}
      {next : Host → P E Host (Ret E)}
      (focused : cfg.ctl = ⟨thread, .prog (.op .hostGet next), frames⟩ :: rest)
      (different : next cfg.host ≠ next other) :
      ReadCut cfg other .tau
        { cfg with ctl := ⟨thread, .prog (next cfg.host), frames⟩ :: rest }
        { replace cfg other with ctl := ⟨thread, .prog (next other), frames⟩ :: rest }

namespace Related

variable (changes : ReturnFrame.Substitutions E Host)

/-- Hosts may differ after earlier transfers, as may the saved program
continuations. The reached store and all other scheduler data agree. -/
def Paired (left right : Config E Host) : Prop :=
  ReturnFrame.Related.Paired changes (replace left right.host) right

/-- A paired step either reaches distinct residual programs at a host read,
or supplies the same return value to the substituted continuations. -/
inductive Boundary : Config E Host → Config E Host → Label E Host → Config E Host → Config E Host → Prop where
  | read {left right label leftNext rightNext alternate} :
      ReadCut left right.host label leftNext alternate → ReturnFrame.Related.Paired changes alternate rightNext →
      Boundary left right label leftNext rightNext
  | returned {left right label leftNext rightNext} :
      ReturnFrame.Related.Returned changes (replace left right.host) right label
        (replace leftNext right.host) rightNext → Boundary left right label leftNext rightNext

end Related

abbrev Paired (first second : ReturnFrame.Continuation E Host) := Related.Paired (ReturnFrame.Only first second)

abbrev Boundary (first second : ReturnFrame.Continuation E Host) := Related.Boundary (ReturnFrame.Only first second)

/-- An interior focus neither reads the host nor returns to a protected
continuation. It can still execute Core or suspend a thread. -/
def InteriorFor (protectedReturn : ReturnFrame.Continuation E Host → Prop) (cfg : Config E Host) : Prop :=
  (∀ thread read frames rest, cfg.ctl ≠ ⟨thread, .prog (.op .hostGet read), frames⟩ :: rest) ∧
  (∀ resume, protectedReturn resume →
    ∀ thread value frames rest, cfg.ctl ≠ ⟨thread, .prog (.pure value), .prog resume :: frames⟩ :: rest)

abbrev Interior (resume : ReturnFrame.Continuation E Host) := InteriorFor (· = resume)

end Silmaril.Wasm.Component.Machine.HostFrame
