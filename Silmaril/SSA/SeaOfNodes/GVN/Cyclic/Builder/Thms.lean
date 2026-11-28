module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.Admission
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Activation.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.FixedPoint.Thms
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Thms

public section

namespace Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder

open Activation (Inputs InputsAgree headerRead sourceWire)
open Diamond (Model Signature Ty ValueSort sortValue)

universe u v w

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {inputs carried : List (ValueSort Data)} {entrySigs headerSigs : List (List (Ty Data))}
variable {out t : ValueSort Data}
variable {loop : Loop.Graph Op inputs carried entrySigs headerSigs out}
variable {m : Model.{u,v,w} Op}

/-- Recovered sources read their exact native origins in the built view. -/
theorem Built.native_source (built : Built loop) (source : Source inputs (sorts loop) t) :
    sourceWire built.view.site source = sourceOrigin loop source :=
  sourceWire_eq built.view.site built.origins source

/-- A typed loop with direct fixed-argument entry operands admits an actual
builder result. Typed prefix scopes ensure the instantaneous order check. -/
theorem build_of_direct_entry [DecidableEq (ValueSort Data)]
    (direct : ∀ {s} (p : RVSDG.Port (Diamond.dataPorts carried) (.value s)),
      ∃ entry : RVSDG.Port inputs s, (loop.phiInputs .entry).get p = .arg (Activation.inputSlot entry)) :
    ∃ built, build? loop = some built :=
  Silmaril.Proofs.SSA.SeaOfNodes.GVN.Cyclic.Builder.build_succeeds direct

variable [DecidableEq (ValueSort Data)] [∀ ins out, DecidableEq (Op ins out)]
variable {input₁ input₂ : Inputs m inputs} {old₁ old₂ : Inputs m carried}

/-- The actual entry column initializes agreement in the generated partition. -/
theorem Built.initial_agrees (built : Built loop) (fixed : InputsAgree m input₁ input₂) :
    built.view.LatchesAgree (FixedPoint.normalize built.graph) m
      (loop.initial m input₁) (loop.initial m input₂) :=
  built.view.initial_agrees (FixedPoint.normalize_stable built.graph).1 fixed

/-- Ordinary header evaluation gives equal typed values for generated
class members when the original latch tuple is related. -/
theorem Built.header_agrees (built : Built loop) (fixed : InputsAgree m input₁ input₂)
    (latches : built.view.LatchesAgree (FixedPoint.normalize built.graph) m old₁ old₂) :
    built.view.ClassesAgree (FixedPoint.normalize built.graph) m input₁ old₁ input₂ old₂ :=
  built.view.header_agrees (FixedPoint.normalize_stable built.graph).1 fixed latches

/-- The generated partition agrees on the ordinary evaluated guard, matches
returns and maintains the latch relation at the next backedge. -/
theorem Built.activation_agrees (built : Built loop) (fixed : InputsAgree m input₁ input₂)
    (latches : built.view.LatchesAgree (FixedPoint.normalize built.graph) m old₁ old₂) :
    headerRead loop m input₁ old₁ loop.predicate = headerRead loop m input₂ old₂ loop.predicate ∧
      built.view.OutcomesAgree (FixedPoint.normalize built.graph) m
        (loop.step m input₁ old₁) (loop.step m input₂ old₂) :=
  built.view.step_agrees (FixedPoint.normalize_stable built.graph).1 fixed latches

variable {result : Deletion.DeletedLoop Op inputs carried entrySigs out}

/-- A native optimization succeeds via a newly built certificate and the
existing shrinking step. -/
theorem optimize?_eq_some_iff :
    optimize? loop = some result ↔
      ∃ built, build? loop = some built ∧ Pass.step? built.view = some result :=
  Option.bind_eq_some_iff

/-- The native driver removes exactly one header binding on success. -/
theorem optimize_count (accepted : optimize? loop = some result) :
    result.headerSigs.length + 1 = headerSigs.length := by
  obtain ⟨built, _, step⟩ := optimize?_eq_some_iff.mp accepted
  exact Pass.step_count built.view step

/-- The native driver preserves every bounded evaluation on success. -/
theorem optimize_evalBackedges (accepted : optimize? loop = some result)
    (input : Inputs m inputs) (budget : Nat) :
    result.graph.evalBackedges m budget input = loop.evalBackedges m budget input := by
  obtain ⟨built, _, step⟩ := optimize?_eq_some_iff.mp accepted
  exact Pass.step_evalBackedges built.view step m input budget

/-- The native driver preserves and reflects every finite return on success. -/
theorem optimize_returns (accepted : optimize? loop = some result)
    (input : Inputs m inputs) (value : sortValue m.value out) :
    result.graph.Returns m input value ↔ loop.Returns m input value := by
  obtain ⟨built, _, step⟩ := optimize?_eq_some_iff.mp accepted
  exact Pass.step_returns built.view step m input value

end Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Builder
