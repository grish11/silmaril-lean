module

public import Silmaril.Wasm.Abstract.Body.Defs
public import Silmaril.Wasm.SSA.Fragment.Defs
public import Silmaril.Games.Abstract.Function.Defs

/-!
# Concrete Wasm bodies as abstract bodies: the structured integer fragment

The first concrete, typed, structure-preserving denotation of actual Wasm
function bodies into the abstract body monad `BodyM`. The concrete bodies are
those of the structured integer fragment of λSSA (`Silmaril.Wasm.SSA.Expr`:
integer operators, locals, `drop`, `nop`, `unreachable`, `block`, `loop`,
`if`, `br`, `br_if`, `return`), the fragment that Core 3.0 execution is proved
to agree with (`Silmaril.Wasm.SSA.behaviours_eq_run`).

**Interface.** Following the typed-block interface of
`Silmaril.Wasm.Abstract.Body`: the locals are frame state passed through the
object (`List WVal`), the module state `S` is threaded unchanged (the fragment
has no memory or globals), and the exits of an expression are the outcome
`Out`: normal completion with the locals and the result (the operand stack of
at most one value), a branch to a de Bruijn label with the locals and its
value, or a return. A trap is the `BodyM` trap effect (payload `PUnit`).

**Denotation, by constructor.** `den`, `denArgs`, `denSeq` are defined by
structural recursion on the syntax, and each constructor is a `BodyM`
operation:

* sequencing (`denSeq`, operands `denArgs`) is Kleisli composition;
* `block` and `if` are composition with the exit copairing `blockK`, which
  sends fallthrough and `br 0` to normal completion and shifts other labels;
* `loop` is Elgot iteration (`Silmaril.Elgot.iter`), with `br 0` the
  continuing summand;
* `unreachable` and trapping operators are `trap`.

Configurations that have no Core run (ill-typed operands, a missing local, an
untyped block result) are `stuck`: silent divergence, matching the Core
behaviours of `behaviours_eq_run`, which are `diverges` exactly when the
fragment has no run.

**Coverage.** Exactly the fragment above. Not covered: floats, memory,
globals, calls and imports, tables, `br_table`, exceptions and handlers,
multi-value blocks and block parameters, and Core code outside the fragment
(CFG or region semantics in general).
-/

@[expose] public section

namespace Silmaril.Wasm.Abstract.FragBody

open Silmaril.Games Silmaril.Wasm.Abstract.Body Silmaril.Wasm.SSA

variable {E : Sig.{0}} {S : Type 1}

/-- Fragment bodies: traps carry no payload. -/
abbrev M (E : Sig.{0}) (S : Type 1) : Type 1 → Type 1 := BodyM E S PUnit.{2}

/-- Locals, as an object. -/
abbrev Loc : Type 1 := ULift.{1} (List WVal)

/-- An expression outcome, as an object. -/
abbrev OutE : Type 1 := ULift.{1} (Out (Option WVal))

/-- An operand-list outcome, as an object. -/
abbrev OutL : Type 1 := ULift.{1} (Out (List WVal))

/-- No run: silent divergence. -/
noncomputable def stuck {X : Type 1} : M E S X :=
  fun _ => ExceptT.mk Silmaril.Elgot.ITree.diverge

/-- An outcome as a body: a trap is the trap effect. -/
def fin {α : Type} : Out α → M E S (ULift.{1} (Out α))
  | .trap => trap ⟨⟩
  | o => pure ⟨o⟩

/-- Normal exit of a construct of type `ty`. -/
noncomputable def exitOk (ty : Option Silmaril.Wasm.IntType) (ls : List WVal) (r : Option WVal) :
    M E S OutE :=
  if ty.isSome && r.isNone then stuck else pure ⟨.ok ls (blockRes ty r)⟩

/-- The exits of `block` and `if`: fallthrough and `br 0` complete normally,
other labels shift, returns pass. -/
noncomputable def blockK (ty : Option Silmaril.Wasm.IntType) : Out (Option WVal) → M E S OutE
  | .ok ls r => exitOk ty ls r
  | .brk 0 ls r => exitOk ty ls r
  | .brk (l + 1) ls r => pure ⟨.brk l ls r⟩
  | .ret r => pure ⟨.ret r⟩
  | .trap => trap ⟨⟩

/-- The exits of `loop`: `br 0` continues (right), the rest leave (left). -/
noncomputable def loopK (ty : Option Silmaril.Wasm.IntType) :
    Out (Option WVal) → M E S (OutE ⊕ Loc)
  | .brk 0 ls _ => pure (.inr ⟨ls⟩)
  | .ok ls r => exitOk ty ls r >>= fun x => pure (.inl x)
  | .brk (l + 1) ls r => pure (.inl ⟨.brk l ls r⟩)
  | .ret r => pure (.inl ⟨.ret r⟩)
  | .trap => trap ⟨⟩

/-- An operator on its evaluated operands. -/
noncomputable def opK (o : Op) : Out (List WVal) → M E S OutE
  | .ok ls vs =>
    match o.eval vs with
    | some (.val v) => pure ⟨.ok ls (some v)⟩
    | some .trap => trap ⟨⟩
    | none => stuck
  | out => fin out.cast

/-- `local.set i` on the outcome of its operand. -/
noncomputable def setK (i : Nat) : Out (Option WVal) → M E S OutE
  | .ok ls (some v) => pure ⟨.ok (ls.set i v) none⟩
  | .ok _ none => stuck
  | out => fin out

/-- `local.tee i` on the outcome of its operand. -/
noncomputable def teeK (i : Nat) : Out (Option WVal) → M E S OutE
  | .ok ls (some v) => pure ⟨.ok (ls.set i v) (some v)⟩
  | .ok _ none => stuck
  | out => fin out

/-- `drop` on the outcome of its operand. -/
noncomputable def dropK : Out (Option WVal) → M E S OutE
  | .ok ls _ => pure ⟨.ok ls none⟩
  | out => fin out

/-- `br l` on its evaluated operands. -/
noncomputable def brK (l : Nat) : Out (List WVal) → M E S OutE
  | .ok ls vs => pure ⟨.brk l ls vs.head?⟩
  | out => fin out.cast

/-- `br_if l` on its evaluated operands (the last is the condition). -/
noncomputable def brIfK (l : Nat) : Out (List WVal) → M E S OutE
  | .ok ls vs =>
    match vs.getLast? with
    | some c =>
      match c.truthy with
      | some b => pure ⟨if b then .brk l ls vs.dropLast.head? else .ok ls vs.dropLast.head?⟩
      | none => stuck
    | none => stuck
  | out => fin out.cast

/-- `return` on its evaluated operands. -/
noncomputable def retK : Out (List WVal) → M E S OutE
  | .ok _ vs => pure ⟨.ret vs.head?⟩
  | out => fin out.cast

/-- Prepend an operand value. -/
def consK (v : WVal) : Out (List WVal) → Out (List WVal)
  | .ok ls vs => .ok ls (v :: vs)
  | out => out

mutual

/-- The abstract body of an expression, on the locals. -/
noncomputable def den : Expr → List WVal → M E S OutE
  | .op o args, ls => denArgs args ls >>= fun r => opK o r.down
  | .localGet i, ls =>
    match ls[i]? with
    | some v => pure ⟨.ok ls (some v)⟩
    | none => stuck
  | .localSet i e, ls => den e ls >>= fun r => setK i r.down
  | .localTee i e, ls => den e ls >>= fun r => teeK i r.down
  | .drop e, ls => den e ls >>= fun r => dropK r.down
  | .nop, ls => pure ⟨.ok ls none⟩
  | .unreachable, _ => trap ⟨⟩
  | .block ty body, ls => denSeq body ls none >>= fun r => blockK ty r.down
  | .loop ty body, ls =>
    Silmaril.Elgot.iter (fun l : Loc => denSeq body l.down none >>= fun r => loopK ty r.down) ⟨ls⟩
  | .if_ ty c t e, ls => den c ls >>= fun r =>
    match r.down with
    | .ok ls₁ (some cv) =>
      match cv.truthy with
      | some true => denSeq t ls₁ none >>= fun r => blockK ty r.down
      | some false => denSeq e ls₁ none >>= fun r => blockK ty r.down
      | none => stuck
    | .ok _ none => stuck
    | out => fin out
  | .br l args, ls => denArgs args ls >>= fun r => brK l r.down
  | .brIf l args, ls => denArgs args ls >>= fun r => brIfK l r.down
  | .return_ args, ls => denArgs args ls >>= fun r => retK r.down

/-- The abstract body of an operand list, left to right. -/
noncomputable def denArgs : List Expr → List WVal → M E S OutL
  | [], ls => pure ⟨.ok ls []⟩
  | e :: es, ls => den e ls >>= fun r =>
    match r.down with
    | .ok ls₁ (some v) => denArgs es ls₁ >>= fun r₂ => pure ⟨consK v r₂.down⟩
    | .ok _ none => stuck
    | out => fin out.cast

/-- The abstract body of a sequence, carrying the last result. -/
noncomputable def denSeq : List Expr → List WVal → Option WVal → M E S OutE
  | [], ls, r => pure ⟨.ok ls r⟩
  | e :: es, ls, _ => den e ls >>= fun o =>
    match o.down with
    | .ok ls₁ r₁ => denSeq es ls₁ r₁
    | out => fin out

end

/-- The call outcome of the body outcome of a function. -/
noncomputable def funcK (res : Option Silmaril.Wasm.IntType) :
    Out (Option WVal) → M E S (ULift.{1} (Option WVal))
  | out =>
    match funcExit res out with
    | some (.ret r) => pure ⟨r⟩
    | some .trap => trap ⟨⟩
    | none => stuck

/-- The abstract body of a fragment function: on arguments of the parameter
types, its body on the arguments and zero locals, then the function exit. -/
noncomputable def denFunc (f : FragFunc) : Hom E S PUnit.{2} (ULift.{1} (List WVal))
    (ULift.{1} (Option WVal)) := fun args =>
  if args.down.map WVal.type = f.params then
    denSeq f.body (f.initLocals args.down) none >>= fun r => funcK f.result r.down
  else stuck

/-! ## Typed interface

The typing of the fragment, Wasm's validation rules restricted to it: a local
context `Γ` (the local types), a label context `Λ` (the value type each label
carries, innermost first; a `loop` label carries none) and the function's
result type `ρ`. An expression of type `r` completes with a value of type `r`
(none: no value). Code that never completes (`unreachable`, `br`, `return`)
has every type. Non-final elements of a body produce no value. Conversions
(`wrap`, `extend`) are not typed here, as for native fragment functions. -/

/-- Operator signatures. -/
inductive OpSig : Op → List Silmaril.Wasm.IntType → Silmaril.Wasm.IntType → Prop
  | const (v : WVal) : OpSig (.const v) [] v.type
  | unInt (t op) : OpSig (.un (.int t op)) [t] t
  | test (t) : OpSig (.un (.test t)) [t] .i32
  | binInt (t op) : OpSig (.bin (.int t op)) [t, t] t
  | rel (t op) : OpSig (.bin (.rel t op)) [t, t] .i32
  | select (t) : OpSig .select [t, t, .i32] t

/-- Values of the types `ts`. -/
def ValsTy (ts : List Silmaril.Wasm.IntType) (vs : List WVal) : Prop := vs.map WVal.type = ts

/-- An optional value of the optional type `r`. -/
def ValTy (r : Option Silmaril.Wasm.IntType) (v : Option WVal) : Prop := v.map WVal.type = r

mutual

/-- `Ty Γ ρ Λ e r`: under locals `Γ`, result `ρ` and labels `Λ`, `e` has type `r`. -/
inductive Ty (Γ : List Silmaril.Wasm.IntType) (ρ : Option Silmaril.Wasm.IntType) :
    List (Option Silmaril.Wasm.IntType) → Expr → Option Silmaril.Wasm.IntType → Prop
  | op {Λ o args ts t} : OpSig o ts t → ArgsTy Γ ρ Λ args ts → Ty Γ ρ Λ (.op o args) (some t)
  | localGet {Λ i t} : Γ[i]? = some t → Ty Γ ρ Λ (.localGet i) (some t)
  | localSet {Λ i e t} : Γ[i]? = some t → Ty Γ ρ Λ e (some t) → Ty Γ ρ Λ (.localSet i e) none
  | localTee {Λ i e t} : Γ[i]? = some t → Ty Γ ρ Λ e (some t) → Ty Γ ρ Λ (.localTee i e) (some t)
  | drop {Λ e t} : Ty Γ ρ Λ e (some t) → Ty Γ ρ Λ (.drop e) none
  | nop {Λ} : Ty Γ ρ Λ .nop none
  | unreachable {Λ r} : Ty Γ ρ Λ .unreachable r
  | block {Λ ty body} : SeqTy Γ ρ (ty :: Λ) body ty → Ty Γ ρ Λ (.block ty body) ty
  | loop {Λ ty body} : SeqTy Γ ρ (none :: Λ) body ty → Ty Γ ρ Λ (.loop ty body) ty
  | if_ {Λ ty c t e} : Ty Γ ρ Λ c (some .i32) → SeqTy Γ ρ (ty :: Λ) t ty →
      SeqTy Γ ρ (ty :: Λ) e ty → Ty Γ ρ Λ (.if_ ty c t e) ty
  | br {Λ l args lt r} : Λ[l]? = some lt → ArgsTy Γ ρ Λ args lt.toList → Ty Γ ρ Λ (.br l args) r
  | brIf {Λ l args lt} : Λ[l]? = some lt → ArgsTy Γ ρ Λ args (lt.toList ++ [.i32]) →
      Ty Γ ρ Λ (.brIf l args) lt
  | return_ {Λ args r} : ArgsTy Γ ρ Λ args ρ.toList → Ty Γ ρ Λ (.return_ args) r

/-- Operands of the types `ts`. -/
inductive ArgsTy (Γ : List Silmaril.Wasm.IntType) (ρ : Option Silmaril.Wasm.IntType) :
    List (Option Silmaril.Wasm.IntType) → List Expr → List Silmaril.Wasm.IntType → Prop
  | nil {Λ} : ArgsTy Γ ρ Λ [] []
  | cons {Λ e es t ts} : Ty Γ ρ Λ e (some t) → ArgsTy Γ ρ Λ es ts → ArgsTy Γ ρ Λ (e :: es) (t :: ts)

/-- A body of type `r`: non-final elements produce no value. -/
inductive SeqTy (Γ : List Silmaril.Wasm.IntType) (ρ : Option Silmaril.Wasm.IntType) :
    List (Option Silmaril.Wasm.IntType) → List Expr → Option Silmaril.Wasm.IntType → Prop
  | nil {Λ} : SeqTy Γ ρ Λ [] none
  | one {Λ e r} : Ty Γ ρ Λ e r → SeqTy Γ ρ Λ [e] r
  | cons {Λ e e' es r} : Ty Γ ρ Λ e none → SeqTy Γ ρ Λ (e' :: es) r → SeqTy Γ ρ Λ (e :: e' :: es) r
  /-- After an element that never completes (`unreachable`, `br`, `return`: it has every
  type), the rest of the body is dead code and unconstrained, as in Wasm validation (a
  polymorphic stack) and the native arity check. -/
  | bot {Λ e es r} : (∀ r', Ty Γ ρ Λ e r') → SeqTy Γ ρ Λ (e :: es) r

end

/-- A typed outcome: the locals keep their types, normal completion and
branches carry values of their types, a return carries the result type. -/
inductive OutTy (Γ : List Silmaril.Wasm.IntType) (ρ : Option Silmaril.Wasm.IntType)
    (Λ : List (Option Silmaril.Wasm.IntType)) {α : Type} (P : α → Prop) : Out α → Prop
  | ok {ls a} : ValsTy Γ ls → P a → OutTy Γ ρ Λ P (.ok ls a)
  | brk {l ls v lt} : Λ[l]? = some lt → ValsTy Γ ls → ValTy lt v → OutTy Γ ρ Λ P (.brk l ls v)
  | ret {v} : ValTy ρ v → OutTy Γ ρ Λ P (.ret v)
  | trap : OutTy Γ ρ Λ P .trap

/-- A fragment function is typed: its body has its result type under its
parameters and locals, with the function label carrying the result. -/
def funcTyped (f : FragFunc) : Prop :=
  SeqTy (f.params ++ f.locals) f.result [f.result] f.body f.result

/-! ## Divergence without stuck configurations

`DivE ls e`: the run of `e` from `ls` diverges, and only through infinitely
many iterations of a loop: either one loop iterates forever (`loopInf`, an
infinite chain of `br 0`s), or a component diverges. Unlike "no
derivation", it never holds of a stuck configuration. -/

mutual

/-- An expression diverges through a loop. -/
inductive DivE : List WVal → Expr → Prop
  | op {ls o args} : DivA ls args → DivE ls (.op o args)
  | localSet {ls i e} : DivE ls e → DivE ls (.localSet i e)
  | localTee {ls i e} : DivE ls e → DivE ls (.localTee i e)
  | drop {ls e} : DivE ls e → DivE ls (.drop e)
  | block {ls ty body} : DivS ls none body → DivE ls (.block ty body)
  | loopBody {ls ty body} : DivS ls none body → DivE ls (.loop ty body)
  | loopBack {ls ls' ty body r} : Seq ls none body (.brk 0 ls' r) → DivE ls' (.loop ty body) →
      DivE ls (.loop ty body)
  | loopInf {ls ty body} (σ : Nat → List WVal) (rs : Nat → Option WVal) : σ 0 = ls →
      (∀ n, Seq (σ n) none body (.brk 0 (σ (n + 1)) (rs n))) → DivE ls (.loop ty body)
  | ifCond {ls ty c t e} : DivE ls c → DivE ls (.if_ ty c t e)
  | ifThen {ls ls₁ ty c t e cv} : Exec ls c (.ok ls₁ (some cv)) → cv.truthy = some true →
      DivS ls₁ none t → DivE ls (.if_ ty c t e)
  | ifElse {ls ls₁ ty c t e cv} : Exec ls c (.ok ls₁ (some cv)) → cv.truthy = some false →
      DivS ls₁ none e → DivE ls (.if_ ty c t e)
  | br {ls l args} : DivA ls args → DivE ls (.br l args)
  | brIf {ls l args} : DivA ls args → DivE ls (.brIf l args)
  | return_ {ls args} : DivA ls args → DivE ls (.return_ args)

/-- Operands diverge. -/
inductive DivA : List WVal → List Expr → Prop
  | head {ls e es} : DivE ls e → DivA ls (e :: es)
  | tail {ls ls₁ e es v} : Exec ls e (.ok ls₁ (some v)) → DivA ls₁ es → DivA ls (e :: es)

/-- A body diverges. -/
inductive DivS : List WVal → Option WVal → List Expr → Prop
  | head {ls r e es} : DivE ls e → DivS ls r (e :: es)
  | tail {ls ls₁ r r₁ e es} : Exec ls e (.ok ls₁ r₁) → DivS ls₁ r₁ es → DivS ls r (e :: es)

end

/-- `loop br 0 end`: a fragment function that loops forever. -/
def spinFunc : FragFunc where
  params := []
  locals := []
  result := none
  body := [.loop none [.br 0 []]]

/-! ## Observed trees -/

/-- The interaction tree of an expression outcome from state `s`: a trap is
the trap, anything else is returned with the state unchanged. -/
def outTree {α : Type} (o : Out α) (s : S) :
    Silmaril.Elgot.ITree.Tree (SigEv E) (Except PUnit.{2} (ULift.{1} (Out α) × S)) :=
  match o with
  | .trap => Silmaril.Elgot.ITree.ret (.error ⟨⟩)
  | o => Silmaril.Elgot.ITree.ret (.ok (⟨o⟩, s))

/-- The interaction tree of a call outcome from state `s`. -/
def callTree (o : FOut) (s : S) :
    Silmaril.Elgot.ITree.Tree (SigEv E) (Except PUnit.{2} (ULift.{1} (Option WVal) × S)) :=
  match o with
  | .ret r => Silmaril.Elgot.ITree.ret (.ok (⟨r⟩, s))
  | .trap => Silmaril.Elgot.ITree.ret (.error ⟨⟩)

/-- The call end of a run outcome. -/
def foutEnd (o : FOut) (s : S) : Silmaril.Games.Abstract.End S (ULift.{1} (Option WVal)) :=
  match o with
  | .ret r => .ret ⟨r⟩ s
  | .trap => .trap

/-- The run outcome of a call end (`none`: divergence). -/
def endFOut : Silmaril.Games.Abstract.End S (ULift.{1} (Option WVal)) → Option FOut
  | .ret r _ => some (.ret r.down)
  | .trap => some .trap
  | .div => none

/-- An expression, as an abstract body on the locals object. -/
noncomputable def denH (e : Expr) : Hom E S PUnit.{2} Loc OutE := fun l => den e l.down

/-- A sequence (from no result), as an abstract body on the locals object. -/
noncomputable def seqH (es : List Expr) : Hom E S PUnit.{2} Loc OutE := fun l => denSeq es l.down none

end Silmaril.Wasm.Abstract.FragBody
