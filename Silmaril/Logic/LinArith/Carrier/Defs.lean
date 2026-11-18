module

public import Silmaril.Logic.LinArith.Defs
public import Silmaril.Logic.SAT.Carrier.Defs

@[expose] public section

/-!
# Farkas certificates over WIT words: the problem language and the acceptor

The typed component interface of the Farkas acceptor:

```wit
record ineq { coeffs: list<tuple<u32, s64>>, bound: s64 }
check: func(system: list<ineq>, y: list<s64>) -> bool
```

An `ineq` value is read as the existing `Silmaril.Logic.LinArith.Ineq` (`IneqW.decode`): each
coefficient pair `(j, a)` is the variable `j.toNat` (a `u32`, unsigned) with the coefficient
`a.toInt` (an `s64`, two's complement), and the bound is `bound.toInt`; the inequality is
`∑ a · x_j ≤ bound`, repeated variables adding up (`Ineq.coeff`). Every typed value reads as a
system: there is no malformed problem at this interface (`decodeSystem` is total). The
multipliers `y` read as integers (`decodeCert`).

* `Infeasible`: the systems with no solution over any ordered field (in `Type`), for example
  `ℚ` and `ℝ`;
* `farkasCheck S y`: the existing certificate check `LinArith.checkCert` of the read system and
  multipliers (one multiplier per inequality, nonnegative, the weighted left-hand sides cancel,
  the weighted bounds add up to a negative number). Its accepted problems are
  `SAT.Carrier.Accepts farkasCheck`, the existential projection over certificates.

`farkasCheck_sound` (`…Carrier.Thms`): accepted systems are infeasible. No completeness is
claimed. The readings are injective, and lossless on values in range (`decodeSystem_encode`).
A Silmaril addition.
-/

namespace Silmaril.Logic.LinArith.Carrier

/-- A WIT `u32` value. -/
abbrev U32 := BitVec 32

/-- A WIT `s64` value (two's complement). -/
abbrev S64 := BitVec 64

/-- `record ineq { coeffs: list<tuple<u32, s64>>, bound: s64 }`. -/
structure IneqW where
  /-- The `(variable, coefficient)` pairs. -/
  coeffs : List (U32 × S64)
  /-- The right-hand side. -/
  bound : S64
  deriving DecidableEq, Repr

/-- A system as `list<ineq>`. -/
abbrev SystemW := List IneqW

/-- An `ineq` value as an inequality. -/
def IneqW.decode (r : IneqW) : Ineq :=
  ⟨r.coeffs.map fun p => (p.1.toNat, p.2.toInt), r.bound.toInt⟩

/-- **The system** of a `list<ineq>` value. -/
def decodeSystem (S : SystemW) : System := S.map IneqW.decode

/-- **The multipliers** of a `list<s64>` value. -/
def decodeCert (y : List S64) : List ℤ := y.map BitVec.toInt

/-- The words of an inequality (variables modulo `2³²`, integers modulo `2⁶⁴`). -/
def IneqW.encode (r : Ineq) : IneqW :=
  ⟨r.coeffs.map fun p => (BitVec.ofNat 32 p.1, BitVec.ofInt 64 p.2), BitVec.ofInt 64 r.bound⟩

/-- An integer that an `s64` represents exactly. -/
def InRange64 (a : ℤ) : Prop := -2 ^ 63 ≤ a ∧ a < 2 ^ 63

/-- An inequality the interface represents exactly: variables below `2³²`, coefficients and
bound in the `s64` range. -/
def IneqInRange (r : Ineq) : Prop :=
  (∀ p ∈ r.coeffs, p.1 < 2 ^ 32 ∧ InRange64 p.2) ∧ InRange64 r.bound

/-- **The systems with no solution over any ordered field** (in `Type`). -/
def Infeasible : Set SystemW :=
  {S | ∀ (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K],
    ¬ Feasible K (decodeSystem S)}

/-- **The Farkas acceptor**: the existing certificate check of the read system and multipliers. -/
def farkasCheck (S : SystemW) (y : List S64) : Bool :=
  checkCert (decodeSystem S) (decodeCert y)

end Silmaril.Logic.LinArith.Carrier
