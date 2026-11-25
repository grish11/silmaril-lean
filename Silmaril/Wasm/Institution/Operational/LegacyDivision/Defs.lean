module

public import Silmaril.Logic.Operational.SOS.Thms
public import Silmaril.Wasm.Execution.Runtime
public import Silmaril.Wasm.Numerics.Integer

/-!
# Flat scalar rules over the native legacy administrative syntax

The parameters choose the public constructors that represent literals, integer
division and `nop`. The rule instances use the shared numeric kernel. Their
definition is independent of the native pure and machine reduction relations.

Wasm 1.0 source provenance is recorded in `specs/spectec/manifest.json` and
`NOTICES/WebAssembly-spec/README.md`. The separate value-prefix and suffix-only
trap rules follow the public native V1 and Lime1 administrative semantics.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.LegacyDivision

open Silmaril.Logic.Operational Silmaril.Logic.Operational.SOS Silmaril.Semantics.SOS
open Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Runtime

structure Syntax (I : Type) where
  value : Value → AdminInstr I
  divide : IntType → Signedness → AdminInstr I
  nop : AdminInstr I

variable {I : Type}

def Syntax.values (S : Syntax I) (vs : List Value) : List (AdminInstr I) := vs.map S.value

inductive Allowed (S : Syntax I) : AdminInstr I → Prop where
  | value (v : Value) : Allowed S (S.value v)
  | divide (t : IntType) (sign : Signedness) : Allowed S (S.divide t sign)
  | nop : Allowed S S.nop
  | trap : Allowed S .trap

def Admitted (S : Syntax I) (code : List (AdminInstr I)) : Prop := ∀ a ∈ code, Allowed S a

/-- The native pure redexes of the slice. Traps may also discard a nonempty
prefix of values or, with no saved, a nonempty suffix. -/
inductive Redex (S : Syntax I) : List (AdminInstr I) → List (AdminInstr I) → Prop where
  | divide (t : IntType) (sign : Signedness) (x y z : BitVec t.width)
      (ok : Numerics.intBinOp t (.div sign) x y = .ok z) :
      Redex S [S.value (.int t x), S.value (.int t y), S.divide t sign] [S.value (.int t z)]
  | divTrap (t : IntType) (sign : Signedness) (x y : BitVec t.width) (cause : Numerics.IntTrap)
      (trap : Numerics.intBinOp t (.div sign) x y = .error cause) :
      Redex S [S.value (.int t x), S.value (.int t y), S.divide t sign] [.trap]
  | nop : Redex S [S.nop] []
  | trapValues (v : Value) (vs : List Value) (tail : List (AdminInstr I))
      (supported : Admitted S tail) : Redex S (S.values (v :: vs) ++ [.trap] ++ tail) [.trap]
  | trapTail (a : AdminInstr I) (tail : List (AdminInstr I))
      (supported : Admitted S (a :: tail)) : Redex S (.trap :: a :: tail) [.trap]

abbrev Judgment (I : Type) := List (AdminInstr I) × List (AdminInstr I)

inductive RuleInstance (S : Syntax I) : Rule (Judgment I) → Prop where
  | redex {before after : List (AdminInstr I)} (redex : Redex S before after) :
      RuleInstance S ⟨[], (before, after)⟩
  | context (saved : List Value) (before after tail : List (AdminInstr I))
      (supported : Admitted S tail) :
      RuleInstance S ⟨[(before, after)],
        (S.values saved ++ before ++ tail, S.values saved ++ after ++ tail)⟩

def shape (I : Type) : SOS.Shape.{0} :=
  ⟨⟨List (AdminInstr I), Unit⟩, Judgment I, fun (before, _, after) => (before, after)⟩

def presentation (S : Syntax I) : SOS.Presentation := ⟨shape I, {r | RuleInstance S r}⟩

abbrev DerivesEdge (S : Syntax I) (before after : List (AdminInstr I)) : Prop :=
  (presentation S).Derives (before, after)

abbrev DerivesPath (S : Syntax I) := Relation.ReflTransGen (DerivesEdge S)

end Silmaril.Wasm.Institution.Operational.LegacyDivision
