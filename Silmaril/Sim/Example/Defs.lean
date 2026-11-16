module

public import Silmaril.Sim.Institution.Defs

/-!
# A toy ISA and a partial simulator for it (header)

A sanity check that the framework is usable and not vacuous: a three-location ISA
(`r0`, `r1`, an "adjust flag" `af`) with `inc` (`r0 += 1`, `af` *undefined*: any value) and
`mov` (`r1 := r0`). The reference `ref` is relational on total states (the undefined flag is
nondeterminism); the simulator `sim` works on partial states, reads only `r0`, and reports
`af` as undefined (`none`) after `inc`. `Thms` proves `sim` sound and transfers a property of
the two-instruction program `inc; mov` from the simulator to the ISA.
-/

@[expose] public section

namespace Silmaril.Sim.Example

open Silmaril.Sim Silmaril.Sim.Institution

/-- Locations. -/
inductive Loc where
  | r0
  | r1
  | af

/-- Instruction forms. -/
inductive Ins where
  | inc
  | mov

/-- The signature: two forms, no syscalls, three locations. -/
abbrev sig : Sig Nat := ⟨Ins, Empty, Loc⟩

/-- The reference ISA: total states; `inc` leaves `af` unconstrained. -/
def ref : Machine sig.Cmd Loc Nat where
  St := Loc → Nat
  view s := PState.ofTotal s
  step
    | .inl .inc => fun s t => t .r0 = s .r0 + 1 ∧ t .r1 = s .r1
    | .inl .mov => fun s t => t .r1 = s .r0 ∧ t .r0 = s .r0 ∧ t .af = s .af
    | .inr e => e.elim

/-- The result of `inc` on a partial state with `r0 = n`. -/
def incOut (n : Nat) (p : PState Loc Nat) : PState Loc Nat
  | .r0 => some (n + 1)
  | .r1 => p .r1
  | .af => none

/-- The result of `mov` on a partial state with `r0 = n`. -/
def movOut (n : Nat) (p : PState Loc Nat) : PState Loc Nat
  | .r0 => some n
  | .r1 => some n
  | .af => p .af

/-- The simulator: steps only when `r0` is defined. -/
def sim : PRel sig.Cmd Loc Nat
  | .inl .inc => fun p p' => ∃ n, p .r0 = some n ∧ p' = incOut n p
  | .inl .mov => fun p p' => ∃ n, p .r0 = some n ∧ p' = movOut n p
  | .inr e => e.elim

/-- The program `inc; mov`. -/
def prog : sig.Program := Prog.block [.inl .inc, .inl .mov]

/-- The property: from `r0 = 0`, some run ends with `r1 = 1`. -/
def φ : Sen sig := .angelic (fun p => p .r0 = some 0) prog (fun _ q => q .r1 = some 1)

end Silmaril.Sim.Example

end
