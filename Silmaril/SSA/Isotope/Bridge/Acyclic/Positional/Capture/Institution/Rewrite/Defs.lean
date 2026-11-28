module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Empty.Defs

/-! # Native LetCase derivability on witnessed captured equations -/

@[expose] public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite

open Isotope.LetCase.LocallyNameless (Derivation Equiv)
open LambdaSSA.Acyclic (Operand)
open LambdaSSA.Acyclic.Positional.Capture.Reverse (Program)
open LambdaSSA.Region (packedExitType)

/-- The existing native typed rewrite relation on the actual packed terms. -/
def Derivable {τ ε : Type} [TypeFormers τ] {P : InstrSig τ ε}
    (pe : ε) (e : GrammarEquation P) : Prop :=
  Equiv pe (Ctx.nil : Ctx Empty τ) e.1.bound
    (grammarCase e).2.1.1 (grammarCase e).2.2.1 (packedExitType e.1.exits)

/-- Evaluate an entry of unit type, then send its packet to outward position
zero. The tail of the ordered exit interface can be chosen independently. -/
def returnUnit {τ Φ : Type} [TypeFormers τ] [HasTy Φ τ]
    {n : Nat} {β : BoundCtx τ n} (L : List τ) (a : Operand Φ β (unit : τ)) :
    Program Φ β (unit :: L) :=
  ⟨unit, a, .jump ⟨.bv 0, .bv⟩ (.exit (i := 0) rfl)⟩

namespace EmptySequencing

abbrev signature := LetIter.Semantics.Categorical.AbortCounterexample.signature

local notation "T" => Ty Empty
local notation "U" => (Ty.unit : T)
local notation "Γ₀" => (Ctx.nil : Ctx Empty T)
local notation "β₀" => (BoundCtx.nil : BoundCtx T 0)

/-- The operand of abort invokes the effectful primitive of empty result. -/
def scrutinee : Derivation signature.Instr Γ₀ β₀ (.op true .unit) (Ty.empty : T) :=
  .op .unit

def direct : Operand signature.Instr β₀ U :=
  ⟨.abort (.op true .unit), .abort scrutinee⟩

def sequenced : Operand signature.Instr β₀ U :=
  ⟨.let₁ (.op true .unit) (.abort (.bv 0)), .let₁ scrutinee (.abort .bv)⟩

/-- The two entries feed the same outward position after evaluating their
unit operand. The remaining ordered exits are arbitrary. -/
def equation (tail : List T) : GrammarEquation signature :=
  ⟨⟨0, β₀, U :: tail⟩, returnUnit tail direct, returnUnit tail sequenced⟩

end EmptySequencing
end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite
