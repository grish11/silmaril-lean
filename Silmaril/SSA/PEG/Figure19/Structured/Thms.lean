module

public import Silmaril.SSA.PEG.Figure19.Structured.Defs
public import Silmaril.SSA.PEG.Figure19.Thms
public import Silmaril.SSA.PEG.Simple.Structured.Thms
public import Silmaril.SSA.PEG.Simple.Structured.Figure19.Thms

public section

namespace Silmaril.SSA.PEG.Figure19.Structured

open PEG.Simple.Structured (translate translate_returns translate_rank)
open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {t : Ty Data}
variable {p : Simple.Program P true params t} {neg : P [.bool] .bool}

/-- The compiler proof discharges the semantic gate. Acceptance
reduces to the bounded Figure 19 check. -/
theorem check_isSome (p : Simple.Program P true params t) (neg : P [.bool] .bool) (fuel : Nat) :
    (check p neg fuel).isSome = (Figure19.check (translate p neg) .inward fuel).isSome := by
  unfold check checkGuarded
  cases Figure19.check (translate p neg) .inward fuel <;> simp [translate_rank]

/-- An admitted compiler table retains the frontend's successful-return
observation. The checked rank supplies demand well-foundedness. -/
theorem observe_of_returns (checked : Guarded (translate p neg) .inward)
    (m : Interpretation.{u,v,w} P) (input : Tuple m.Value params)
    (negation : ∀ b : Bool, m.run neg (.cons ⟨b⟩ .nil) = some ⟨!b⟩)
    {value : m.Value t} (ran : p.Returns m input value) (i) :
    (translate p neg).observe m ((translate p neg).denote m input checked.demandWellFounded) i =
      .cons (some value) .nil :=
  translate_returns p neg m input negation ran i

end Silmaril.SSA.PEG.Figure19.Structured
