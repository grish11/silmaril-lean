module

public import Silmaril.Wasm.Abstract.FunctorP.Defs
public import Silmaril.Wasm.Abstract.LegalFunctor.Defs
public import Silmaril.Wasm.Abstract.BodyTrace.Defs

/-!
# Wasm legality for the canonical play object, and the legal operational equivalence

`StratLegal` (#616) puts a body's play object on a **legal interface** `legalSig E L`, given a
legality predicate `L` on the answers of the import calls. This topic gives the concrete Wasm `L`
for the call events of the exposed denotation `ExposePStruct.denL`, and the operational
equivalence that the legal play object is faithful for.

**The call events.** `denL` calls through `StoreCall.CallSig H`. A call event (`FunctorP.ACall`,
lifted by `BodyTrace.liftSig`) is `(a, args, s)`: the callee address `a`, the arguments `args`
(bottom first) and **the store `s` at the call**. Its answer is `(s₂, fl)`: the store after the
call and the callee's flow. The op carries the store, so legality can read the callee's type from
it, and needs no hidden state.

**Legality** (`LegalAns`, `wasmL`). An answer `(s₂, fl)` to the call `(a, args, s)` is legal when,
if the call fits (`TypedCat.ArgsFit s a args`: `args` has the callee's parameter count) and is
made from a world store (`Γ.Good s`), the answer keeps the world (`Γ.Good s₂`) and its returned
values `fl.retVals` number at least the callee's declared results. The callee's type is read from
the op's store `s.funcs[a]?`; under `Γ.Good s` that is `Γ.funcs[a]?`. Answers that return no
values (a trap or an exception) only need to keep the world.

*Why this form.* It is #623's `Legal Γ C := ArityResp Γ (fitP C)`, read answer by answer:
`LegalStrat.Thms.legal_iff` shows that `Legal Γ C` holds exactly when every answer `C` gives is
`wasmL Γ`-legal. Calls that do not fit, or are made from a store outside the world, are left
unconstrained (every answer is legal), as `fitP` and `ArityResp` leave them. The well-typedness of
the returned values (`TypedCat.TypedAns`) is not asked, as in #623.

**Legal logs** (`LegalLog Γ cs`): every answer of the log `cs` is `wasmL Γ`-legal.

**The legal operational equivalence** (`OpEquivPL Γ es es'`): `FunctorP.OpEquivP` restricted to
legal logs. For every oracle, store, frame and stack (all of them: the questions of the play
object are all configurations and stores, so no restriction to world states is made), and every
**legal** log: the same non-trap logged outcomes (`EvalLXP`), the same logged traps (a trap's
store and frame are not observed), and the same logged pending calls (`ReachXP`). It is defined
from logged runs only. As for `OpEquivP`, silent divergence at a legal log and the infinite
productive streams with legal answers are determined by these: `LegalStrat.Thms` shows that
`OpEquivPL` is exactly equality of the legal play objects, whose divergent and infinite plays are
compared.

**Scope.** The supported checked fragment of `ExposePStruct`/`ExposePTyped` (the checker's
integer, control, call and exception forms), not full Wasm. Equal legal play objects are
`OpEquivPL`; this is not contextual full abstraction. No host-level Core faithfulness is claimed.
The call events are those `denL` already exposes: no internal call-graph observability is added.
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.LegalStrat

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract (CallRel)
open Silmaril.Wasm.Abstract.StoreCall (CallSig)
open Silmaril.Wasm.Abstract.ExposePStruct (Ctx)
open Silmaril.Wasm.Abstract.TypedCat (ArgsFit)
open Silmaril.Wasm.Abstract.BodyTrace (liftSig)
open Silmaril.Wasm.Abstract.CallXP (POut)
open Silmaril.Wasm.Abstract.FunctorP (ACall EvalLXP ReachXP)

variable {H : Type}

/-- **A legal answer** `ans = (s₂, fl)` to the call of the address `a` on `args` in the store `s`:
if the call fits and is made from a world store, the answer keeps the world and returns at least
the callee's declared result count. -/
def LegalAns (Γ : Ctx H) (s : Store H) (a : Nat) (args : List Val) (ans : Store H × Flow) :
    Prop :=
  ArgsFit s a args → Γ.Good s →
    Γ.Good ans.1 ∧ ∀ (fi : FuncInst H) (ps rs : List Validation.CValType) (vs : List Val),
      s.funcs[a]? = some fi → Validation.DefType.funcType? fi.type = some (ps, rs) →
        ans.2.retVals = some vs → rs.length ≤ vs.length

/-- **Wasm legality** on the lifted call events of `denL`: the op `(a, args, s)` carries the
store, and an answer is legal when it is a `LegalAns`. -/
def wasmL (Γ : Ctx H) : (m : (liftSig (CallSig H)).Op) → (liftSig (CallSig H)).Ar m → Prop :=
  fun m n => LegalAns Γ m.down.2.2 m.down.1 m.down.2.1 n.down

/-- The most permissive legal oracle: it gives every legal answer. -/
def legalC (Γ : Ctx H) : CallRel H := fun s a args ans => LegalAns Γ s a args ans

/-- **A legal log**: every answer is `wasmL Γ`-legal. -/
def LegalLog (Γ : Ctx H) (cs : List (ACall H)) : Prop :=
  ∀ c ∈ cs, wasmL Γ (ULift.up c.1) (ULift.up c.2)

/-- **The legal operational equivalence**: at every oracle, store, frame and stack, and every
legal log, the same non-trap logged outcomes, the same logged traps (a trap's store and frame are
not observed) and the same logged pending calls. -/
def OpEquivPL (Γ : Ctx H) (es es' : List BExpr) : Prop :=
  ∀ (C : CallRel H) (s : Store H) (f : Frame) (stk : List Val) (cs : List (ACall H)),
    LegalLog Γ cs →
    (∀ s' f' (o : POut), o ≠ .flow .trap →
      (EvalLXP C s f stk es cs (s', f', o) ↔ EvalLXP C s f stk es' cs (s', f', o))) ∧
    ((∃ s' f', EvalLXP C s f stk es cs (s', f', .flow .trap)) ↔
      ∃ s' f', EvalLXP C s f stk es' cs (s', f', .flow .trap)) ∧
    ∀ y, ReachXP C s f stk es cs y ↔ ReachXP C s f stk es' cs y

end Silmaril.Wasm.Abstract.LegalStrat
