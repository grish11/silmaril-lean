module

/-!
# AArch64 condition flags: `NZCV`, `addWithCarry`, `condHolds`

The four A64 condition flags (PSTATE.N, Z, C, V), the flag-setting addition
`AddWithCarry` used by ADDS, SUBS and CMP, and the condition test `ConditionHolds`
used by CSEL, CSINV and B.cond.

Sources (Arm A64 ISA XML 2026-09, Arm ARM DDI 0487 M.d):

* `AddWithCarry`: `shared_pseudocode.xml`, `shared/functions/integer/AddWithCarry`.
* `ConditionHolds`: `shared_pseudocode.xml`, `shared/functions/system/ConditionHolds`.
* Flag meanings: Arm ARM B1.3 "Process state, PSTATE".
* Condition codes: Arm ARM C1.2.4, Table C1-1.

This is a handwritten model. It follows the Arm text; it makes no claim of equivalence
with the ASL or with any other model.

Each definition comes twice. `addWithCarry` and `condHolds` are the definitions the
machine model runs: `addWithCarry` uses fixed-width bit operations. The `Spec` namespace
restates them independently: `Spec.addWithCarry` is Arm's `AddWithCarry` over `Nat` and
`Int`, and `Spec.condHolds` is Table C1-1. `Silmaril.Machine.AArch64.Flags.Thms` proves
that each pair agrees.
-/

@[expose] public section

namespace Silmaril.Machine.AArch64

/-- The A64 condition flags PSTATE.{N, Z, C, V} (Arm ARM B1.3). All four are always
defined after a flag-setting instruction, so each is a plain `Bool`. -/
structure NZCV where
  /-- Negative: the result, read as a two's complement integer, is negative. -/
  n : Bool
  /-- Zero: the result is zero. -/
  z : Bool
  /-- Carry: the unsigned addition carried out of the top bit. -/
  c : Bool
  /-- Overflow: the signed addition overflowed. -/
  v : Bool
deriving DecidableEq, Repr, Inhabited

/-- `AddWithCarry` (Arm A64 ISA XML 2026-09, `shared/functions/integer/AddWithCarry`),
computed with bit operations on the operands and the wrapped result `r`:

* `c` is the carry out of the top bit: at least two of `x`'s top bit, `y`'s top bit and
  the carry into the top bit are set, where the carry into the top bit is the XOR of
  the three top bits of `x`, `y` and `r`;
* `v` is set when `x` and `y` have the same sign and `r` has the other sign.

ADDS is `addWithCarry x y false`. SUBS and CMP are `addWithCarry x (~~~y) true`.
`Spec.addWithCarry` is Arm's arithmetic definition; `addWithCarry_eq_spec` proves the
two equal at every width greater than zero. -/
def addWithCarry {w : Nat} (x y : BitVec w) (carryIn : Bool) : BitVec w × NZCV :=
  let r := x + y + (BitVec.ofBool carryIn).setWidth w
  (r, { n := r.msb
        z := r == 0#w
        c := ((x &&& y) ||| ((x ||| y) &&& ~~~r)).msb
        v := ((x ^^^ r) &&& (y ^^^ r)).msb })

/-- `ConditionHolds` (Arm A64 ISA XML 2026-09, `shared/functions/system/ConditionHolds`):
`cond[3:1]` selects a base test, and `cond[0] = 1` inverts it, except for `1111`. -/
def condHolds (cond : BitVec 4) (f : NZCV) : Bool :=
  let base : Bool :=
    match (cond.extractLsb' 1 3).toNat with
    | 0 => f.z                   -- '000': EQ or NE
    | 1 => f.c                   -- '001': CS or CC
    | 2 => f.n                   -- '010': MI or PL
    | 3 => f.v                   -- '011': VS or VC
    | 4 => f.c && !f.z           -- '100': HI or LS
    | 5 => f.n == f.v            -- '101': GE or LT
    | 6 => f.n == f.v && !f.z    -- '110': GT or LE
    | _ => true                  -- '111': AL
  if cond.getLsbD 0 && cond != 0b1111#4 then !base else base

/-! ## Independent specifications -/

namespace Spec

/-- Arm's `AddWithCarry`, transcribed over `Nat` and `Int`:

```
let unsigned_sum : integer = UInt(x) + UInt(y) + UInt(carry_in);
let signed_sum : integer = SInt(x) + SInt(y) + UInt(carry_in);
let result : bits(N) = unsigned_sum[N-1:0];
let c : bit = if UInt(result) == unsigned_sum then '0' else '1';
let v : bit = if SInt(result) == signed_sum then '0' else '1';
```

N and Z are stated by their meaning in Arm ARM B1.3 (the result is negative as a two's
complement integer; the result is zero), not through `result[N-1]` and `IsZero`. -/
def addWithCarry {w : Nat} (x y : BitVec w) (carryIn : Bool) : BitVec w × NZCV :=
  let unsignedSum : Nat := x.toNat + y.toNat + carryIn.toNat
  let signedSum : Int := x.toInt + y.toInt + carryIn.toNat
  let result : BitVec w := BitVec.ofNat w unsignedSum
  (result, { n := decide (result.toInt < 0)
             z := decide (result.toNat = 0)
             c := !decide (result.toNat = unsignedSum)
             v := !decide (result.toInt = signedSum) })

/-- The condition codes of Arm ARM DDI 0487 M.d, C1.2.4, Table C1-1, one row per `cond`.
NV (`1111`) behaves as AL (the table's footnote b). -/
def condHolds (cond : BitVec 4) (f : NZCV) : Bool :=
  match cond.toNat with
  | 0 => f.z                       -- 0000 EQ: Z == 1
  | 1 => !f.z                      -- 0001 NE: Z == 0
  | 2 => f.c                       -- 0010 CS/HS: C == 1
  | 3 => !f.c                      -- 0011 CC/LO: C == 0
  | 4 => f.n                       -- 0100 MI: N == 1
  | 5 => !f.n                      -- 0101 PL: N == 0
  | 6 => f.v                       -- 0110 VS: V == 1
  | 7 => !f.v                      -- 0111 VC: V == 0
  | 8 => f.c && !f.z               -- 1000 HI: C == 1 && Z == 0
  | 9 => !(f.c && !f.z)            -- 1001 LS: !(C == 1 && Z == 0)
  | 10 => f.n == f.v               -- 1010 GE: N == V
  | 11 => f.n != f.v               -- 1011 LT: N != V
  | 12 => !f.z && f.n == f.v       -- 1100 GT: Z == 0 && N == V
  | 13 => !(!f.z && f.n == f.v)    -- 1101 LE: !(Z == 0 && N == V)
  | _ => true                      -- 1110 AL, 1111 NV: always

end Spec

end Silmaril.Machine.AArch64
