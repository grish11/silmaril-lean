module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Kleisli.Thms

/-! # Free-type Kleisli models of witnessed LetCase equations -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli

open CategoryTheory Silmaril.Elgot
open Isotope.Semantics (BoundEnv FreeEnv InstructionModel)
open Isotope.LetCase.LocallyNameless (Derivation Tm)
open LetIter.Semantics.Categorical (ofTypeModel ofInstructionModel)

abbrev value := Ty.denote (Empty.elim : Empty → Type)

local notation "Γ₀" => (Ctx.nil : Ctx Empty (Ty Empty))

def noFree : FreeEnv value Γ₀ := fun x => x.elim

variable {m : Type → Type} [Monad m] {P : InstrSig (Ty Empty) Bool}

def run (M : InstructionModel value P.Instr m) {n : Nat} {β : BoundCtx (Ty Empty) n}
    {t : Tm Empty P.Instr n} {A : Ty Empty} (d : Derivation P.Instr Γ₀ β t A)
    (ρ : BoundEnv value β) : m (value A) :=
  d.denote value M noFree ρ

variable [LawfulMonad m]

abbrev J := CategoryTheory.Kleisli.Adjunction.toKleisli (ofTypeMonad m)

noncomputable abbrev types := ofTypeModel value
noncomputable abbrev instructions (M : InstructionModel value P.Instr m) := ofInstructionModel value M

noncomputable def algebra (M : InstructionModel value P.Instr m) : CaseAlgebra P :=
  freydCaseAlgebra (J (m := m)) types (instructions M)

variable [Iterate m] [LawfulElgotMonad m]

/-- Admit a presentation to the existing room using the original LambdaSSA
region-witness coherence condition. -/
noncomputable def validated (M : InstructionModel value P.Instr m)
    (coherent : letI := instructions M
      LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := P.Instr) (J (m := m)) types) :
    (grammarRoom (J (m := m)) P).Mod :=
  ShrinkHoms.toShrinkHoms (Discrete.mk
    ((expandFreyd (J (m := m)) types (instructions M) coherent).validate (J (m := m))))

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli
