module

public import Silmaril.Wasi.Component.Consequence.Checkers.Defs
public import Silmaril.Logic.Consequence.Gentzen.Defs
public import Silmaril.Logic.Consequence.Gentzen.Core.Thms
public import Silmaril.Logic.Consequence.Signed.Defs

/-! # Gentzen sequents from component UNSAT and TAUTO checkers

A component exporting a list checker `f(list<T>) -> bool` (protocol 1 with no assumptions:
`listCheck f dec`, a `Reading Unit (List F)`) gives a Prop predicate on lists, `checkerOf T r`:
some play answers `true` for the list. Read as an **UNSAT checker** or as a **TAUTO checker**, it
gives a Gentzen sequent relation through the conversions of `Silmaril.Consequence.Gentzen`:

* `unsatSeq T r neg := Gentzen.viaUnsat (checkerOf T r) neg`: `Γ ⊢ Δ` iff the component accepts
  `Γ ++ Δ.map neg`;
* `tautSeq T r neg := Gentzen.viaTauto (checkerOf T r) neg`: `Γ ⊢ Δ` iff it accepts
  `Γ.map neg ++ Δ`.

Which reading is right is not a property of the component: the same component can be sound as an
UNSAT checker and as a TAUTO checker for different reasons, or for neither. Soundness of the
component (`CheckSound`, `TautSound`) is always a **hypothesis** of the adapter theorems, unless
it is proved for a specification strategy.

**Signed formulas** (`Silmaril.Consequence.Signed`): signed satisfaction is the core
`Silmaril.Consequence.Gentzen.signedSat v`, which reads `pos a` as `v m a` and `neg a` as its
negation; the sign flip `-` satisfies both negation laws exactly. The former local name
`signedSat` is a deprecated `abbrev` for it. The specification **clash checker** (`clashChecker`)
accepts a list exactly when it contains some `x` and `-x`. It is a specification strategy (`answerChecker`), not a compiled component;
`signedU32?` and `clashEnc` are its concrete `list<variant { pos(u32), neg(u32) }>` encoding.

New definitions (no source).
-/

@[expose] public section

namespace Silmaril.Wasi.Consequence

open Silmaril.Consequence (Signed)
open Silmaril.Wasm.Component (Val)

universe v

variable {F : Type}

/-- **A list checker**: protocol 1 whose only argument is a list, decoded by `dec`. -/
def listCheck (f : FnName) (dec : List Val → Option (List F)) : Reading Unit (List F) :=
  exportCheck f fun args => (dec args).map ((), ·)

/-- The predicate a list checker reading gives: some play accepts the list. -/
def checkerOf (T : Set (List WEv)) (r : Reading Unit (List F)) : List F → Prop :=
  fun Γ => Accepted T r () Γ

/-- **The UNSAT reading**: `Γ ⊢ Δ` iff `Γ ++ Δ.map neg` is accepted. -/
def unsatSeq (T : Set (List WEv)) (r : Reading Unit (List F)) (neg : F → F) :
    Silmaril.Consequence.Gentzen.Seq F :=
  Silmaril.Consequence.Gentzen.viaUnsat (checkerOf T r) neg

/-- **The TAUTO reading**: `Γ ⊢ Δ` iff `Γ.map neg ++ Δ` is accepted. -/
def tautSeq (T : Set (List WEv)) (r : Reading Unit (List F)) (neg : F → F) :
    Silmaril.Consequence.Gentzen.Seq F :=
  Silmaril.Consequence.Gentzen.viaTauto (checkerOf T r) neg

/-! ## Signed formulas -/

/-- Signed satisfaction: the core `Silmaril.Consequence.Gentzen.signedSat`, under its former
local name (reducible, so terms stated with either name are interchangeable). -/
@[deprecated Silmaril.Consequence.Gentzen.signedSat +typeChanged
  (since := "2026-11-16")]
abbrev signedSat {M A : Type} (v : M → A → Prop) : M → Signed A → Prop :=
  Silmaril.Consequence.Gentzen.signedSat v

/-- A list contains some formula and its negation. -/
def Clash {A : Type} (Γ : List (Signed A)) : Prop := ∃ x ∈ Γ, -x ∈ Γ

instance {A : Type} [DecidableEq A] (Γ : List (Signed A)) : Decidable (Clash Γ) :=
  inferInstanceAs (Decidable (∃ x ∈ Γ, -x ∈ Γ))

/-- **The clash checker**: accepts a list exactly when it contains some `x` and `-x`. -/
def clashChecker {A : Type} [DecidableEq A] (enc : Unit × List (Signed A) → List Val) :
    Silmaril.Games.Strategy (nsig ∅) (nsig {checkFn}) :=
  answerChecker enc fun q => decide (Clash q.2)

/-- A signed `u32`: `variant { pos(u32), neg(u32) }`. -/
def signedU32? : Val → Option (Signed (BitVec 32))
  | .variant 0 (some (.u32 a)) => some (.pos a)
  | .variant 1 (some (.u32 a)) => some (.neg a)
  | _ => none

/-- The encoding of a signed `u32`. -/
def signedU32 : Signed (BitVec 32) → Val
  | .pos a => .variant 0 (some (.u32 a))
  | .neg a => .variant 1 (some (.u32 a))

/-- The encoding of a clash query: one `list<variant { pos(u32), neg(u32) }>` argument. -/
def clashEnc (q : Unit × List (Signed (BitVec 32))) : List Val := [.record (q.2.map signedU32)]

/-- The decoding of a clash query. -/
def clashDec (args : List Val) : Option (List (Signed (BitVec 32))) :=
  Accept.args1 (fun v => (Accept.ofRecord? v).bind (·.mapM signedU32?)) args

/-- The clash checker at signed `u32`s. -/
def clashU32 : Silmaril.Games.Strategy (nsig ∅) (nsig {checkFn}) := clashChecker clashEnc

end Silmaril.Wasi.Consequence
