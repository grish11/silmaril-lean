module

public import Silmaril.Wasm.Cfg.Exec.Defs
public import Silmaril.Wasm.Execution.Core.Inversion.Defs
public import Silmaril.Wasm.Abstract.Recursion.Defs

@[expose] public section

/-!
# A structured big-step semantics of Wasm regions, against Core 3.0

`Run P host s f vs code s' f' o` is a compositional big-step semantics of runtime code
`code` (Core 3.0 administrative instructions) with operand stack `vs` (bottom first). It
runs from store `s` and frame `f` to store `s'`, frame `f'` and outcome `o`:

* `normal vs'`: fell through, leaving the stack `vs'`;
* `br l vs'`: branching to the `l`-th enclosing label, with stack `vs'`;
* `ret vs'`: returning, with stack `vs'`;
* `trap`;
* `throw a`: throwing the exception at address `a`;
* `tail vs a c`: a pending tail call of the function at address `a` (`REF.FUNC_ADDR a` and the
  `RETURN_CALL_REF` form `c`, over `vs`), as `Logic.Core.Outcome.tail`; `tailNull vs c`: a
  pending tail call of a null reference.

The rules follow the structure of the code:
* a value is pushed;
* a non-control instruction (`Det.famOf ≠ .control`: numeric, vector, variable, table,
  memory, reference, aggregate, parametric) runs by its own Core 3.0 reduction, to values
  or to a trap;
* `br_if` and `if` read their `i32` condition;
* `block`, `loop` and `if` push a `LABEL` exactly as Core does;
* a `LABEL` runs its body to an outcome and then continues according to it: fall through,
  run the continuation on a branch to the label itself, or pass an outer branch, a return or
  a trap outwards;
* `return_call`, `return_call_ref` and `return_call_indirect` end the region in a pending tail
  call, which passes outwards through labels and handlers as Core's `return_call_ref-label` and
  `-handler` rules do. The call is made when the enclosing `FRAME` is left (frame replacement,
  `return_call_ref-frame-addr`); a region never answers it, and a handler does not catch the
  callee's exceptions. A pending tail call of null traps at the frame (`FrameOut`).

Outcomes carry values, store and frame, and every branch reads data.

The fragment (`Frag`) is call-free: values, non-control instructions,
`block`, `loop`, `if`, `br`, `br_if`, `br_table`, `br_on_null`, `br_on_non_null`, `br_on_cast`,
`br_on_cast_fail`, `return`, `throw`, `throw_ref`, `try_table`, `TRAP`, `LABEL` and `HANDLER`. On it the semantics is
**adequate in both directions** for every profile and host (`Region/Thms.lean`): `Run`
holds exactly when Core 3.0 runs the code to a final form of that outcome. This covers
terminating runs only; divergence is not treated yet.
-/

namespace Silmaril.Wasm.Cfg.Region

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

/-- How control leaves a region. -/
inductive Out where
  | normal (vs : List Val)
  | br (l : Nat) (vs : List Val)
  | ret (vs : List Val)
  | trap
  /-- Throwing the exception at address `a` (`REF.EXN_ADDR a; THROW_REF`). -/
  | throw (a : Nat)
  /-- About to tail-call the function at address `a` (`REF.FUNC_ADDR a` followed by the
  `RETURN_CALL_REF` form `c`), with the values `vs` below the reference. The enclosing `FRAME`
  is replaced by the call (`return_call_ref-frame-addr`); a region does not make the call. -/
  | tail (vs : List Val) (a : Nat) (c : Admin)
  /-- About to tail-call a null reference (`REF.NULL` followed by the `RETURN_CALL_REF` form `c`),
  with the values `vs` below it: the enclosing `FRAME` traps (`return_call_ref-frame-null`). -/
  | tailNull (vs : List Val) (c : Admin)
  deriving Repr

/-- The Core final forms of an outcome. Anything after a `br` or `return` is dead. -/
def Out.Ends : Out → List Admin → Prop
  | .normal vs, c => c = vals vs
  | .br l vs, c => ∃ (x : LabelIdx) (rest : List Admin), x.toNat = l ∧
      c = vals vs ++ .plain (.br x) :: rest
  | .ret vs, c => ∃ rest : List Admin, c = vals vs ++ .plain .return_ :: rest
  | .trap, c => c = [.trap]
  | .throw a, c => c = throwing a
  | .tail vs a r, c => r.IsReturnCallRef ∧ ∃ rest : List Admin,
      c = vals vs ++ .ref (.func a) :: r :: rest
  | .tailNull vs r, c => r.IsReturnCallRef ∧ ∃ rest : List Admin,
      c = vals vs ++ .ref .null :: r :: rest

/-- Source instructions of the fragment. -/
inductive FragI : Instr → Prop where
  | simple {i : Instr} (h : SingleThreaded.Det.famOf (.plain i) ≠ .control) : FragI i
  | const {i : Instr} (h : (Admin.plain i).val? ≠ none) : FragI i
  | block {bt : BlockType} {b : List Instr} (h : ∀ i ∈ b, FragI i) : FragI (.block bt b)
  | loop {bt : BlockType} {b : List Instr} (h : ∀ i ∈ b, FragI i) : FragI (.loop bt b)
  | if_ {bt : BlockType} {t e : List Instr} (ht : ∀ i ∈ t, FragI i) (he : ∀ i ∈ e, FragI i) :
      FragI (.if_ bt t e)
  | br (l : LabelIdx) : FragI (.br l)
  | brIf (l : LabelIdx) : FragI (.brIf l)
  | return_ : FragI .return_
  /-- `br_table`, `br_on_null`, `br_on_non_null`, `br_on_cast`, `br_on_cast_fail`. -/
  | brData {i : Instr} (h : i.IsBrData) : FragI i
  | throw (x : TagIdx) : FragI (.throw x)
  | throwRef : FragI .throwRef
  | tryTable {bt : BlockType} {cs : List Catch} {b : List Instr} (h : ∀ i ∈ b, FragI i) :
      FragI (.tryTable bt cs b)

/-- Runtime instructions of the fragment. -/
inductive FragA : Admin → Prop where
  | val {a : Admin} (h : a.val? ≠ none) : FragA a
  | plain {i : Instr} (h : FragI i) : FragA (.plain i)
  | trap : FragA .trap
  | label {n : Nat} {cont : List Instr} {inner : List Admin} (hc : ∀ i ∈ cont, FragI i)
      (hi : ∀ a ∈ inner, FragA a) : FragA (.label n cont inner)
  | handler {n : Nat} {cs : List Catch} {inner : List Admin} (hi : ∀ a ∈ inner, FragA a) :
      FragA (.handler n cs inner)

/-- Runtime code of the fragment. -/
def Frag (code : List Admin) : Prop := ∀ a ∈ code, FragA a

variable {H : Type}

/-- How the clauses `cs` of a handler treat the exception at address `a`: the first clause that
matches branches to its label with the values it pushes (`some (us, l)`); if none matches, the
exception propagates (`none`). These are the `throw_ref-handler-*` rules. -/
inductive Catches (s : Store H) (f : Frame) (a : Nat) : List Catch → Option (List Val × LabelIdx) → Prop where
  | catch_ {x : TagIdx} {l : LabelIdx} {cs : List Catch} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      Catches s f a (.catch_ x l :: cs) (some (e.fields, l))
  | catchRef {x : TagIdx} {l : LabelIdx} {cs : List Catch} {e : ExnInst}
      (he : s.exns[a]? = some e) (ht : f.module.tags[x.toNat]? = some e.tag) :
      Catches s f a (.catchRef x l :: cs) (some (e.fields ++ [.ref (.exn a)], l))
  | catchAll {l : LabelIdx} {cs : List Catch} : Catches s f a (.catchAll l :: cs) (some ([], l))
  | catchAllRef {l : LabelIdx} {cs : List Catch} :
      Catches s f a (.catchAllRef l :: cs) (some ([.ref (.exn a)], l))
  | next {c : Catch} {cs : List Catch} {r : Option (List Val × LabelIdx)}
      (h : ¬ CatchMatches s f a c) (hr : Catches s f a cs r) : Catches s f a (c :: cs) r
  | empty : Catches s f a [] none

/-- **The region semantics.** -/
inductive RunC (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H) :
    Store H → Frame → List Val → List Admin → Store H → Frame → Out → Prop where
  | nil {s : Store H} {f : Frame} {vs : List Val} : RunC P host C s f vs [] s f (.normal vs)
  | val {s s' : Store H} {f f' : Frame} {vs : List Val} {a : Admin} {v : Val}
      {code : List Admin} {o : Out} (hv : a.val? = some v)
      (h : RunC P host C s f (vs ++ [v]) code s' f' o) : RunC P host C s f vs (a :: code) s' f' o
  /-- A non-control instruction runs by Core reduction to values. -/
  | simple {s s₁ s' : Store H} {f f₁ f' : Frame} {vs vs₁ : List Val} {i : Instr}
      {code : List Admin} {o : Out} (hi : SingleThreaded.Det.famOf (.plain i) ≠ .control)
      (h₁ : Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s₁, f₁, vals vs₁⟩)
      (h : RunC P host C s₁ f₁ vs₁ code s' f' o) : RunC P host C s f vs (.plain i :: code) s' f' o
  /-- A non-control instruction traps. -/
  | simpleTrap {s s₁ : Store H} {f f₁ : Frame} {vs : List Val} {i : Instr} {code : List Admin}
      (hi : SingleThreaded.Det.famOf (.plain i) ≠ .control)
      (h₁ : Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s₁, f₁, [.trap]⟩) :
      RunC P host C s f vs (.plain i :: code) s₁ f₁ .trap
  | trap {s : Store H} {f : Frame} {vs : List Val} {code : List Admin} :
      RunC P host C s f vs (.trap :: code) s f .trap
  | br {s : Store H} {f : Frame} {vs : List Val} {l : LabelIdx} {code : List Admin} :
      RunC P host C s f vs (.plain (.br l) :: code) s f (.br l.toNat vs)
  | ret {s : Store H} {f : Frame} {vs : List Val} {code : List Admin} :
      RunC P host C s f vs (.plain .return_ :: code) s f (.ret vs)
  | brIf {s s' : Store H} {f f' : Frame} {ws : List Val} {k : BitVec 32} {l : LabelIdx}
      {code : List Admin} {o : Out}
      (h : RunC P host C s f ws ((if k = 0 then [] else [.plain (.br l)]) ++ code) s' f' o) :
      RunC P host C s f (ws ++ [.i32 k]) (.plain (.brIf l) :: code) s' f' o
  /-- `throw x` allocates the exception and throws it. -/
  | throw {s : Store H} {f : Frame} {ws vs : List Val} {x : TagIdx} {ta : Nat} {ti : TagInst}
      {ts : Ty (.list .val)} {code : List Admin} (ht : s.tag? f x = some (ta, ti))
      (he : Expand ti.type (.func ts .nil)) (hn : vs.length = ts.length) :
      RunC P host C s f (ws ++ vs) (.plain (.throw x) :: code) (s.addExn ⟨ta, vs⟩) f
        (.throw s.exns.length)
  | throwRefNull {s : Store H} {f : Frame} {ws : List Val} {code : List Admin} :
      RunC P host C s f (ws ++ [.ref .null]) (.plain .throwRef :: code) s f .trap
  | throwRefExn {s : Store H} {f : Frame} {ws : List Val} {a : Nat} {code : List Admin} :
      RunC P host C s f (ws ++ [.ref (.exn a)]) (.plain .throwRef :: code) s f (.throw a)
  | tryTable {s s' : Store H} {f f' : Frame} {ws us : List Val} {bt : BlockType}
      {cs : List Catch} {b : List Instr} {t₁ t₂ : List CValType} {code : List Admin} {o : Out}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
      (h : RunC P host C s f ws
        (.handler t₂.length cs [.label t₂.length [] (vals us ++ expression b)] :: code) s' f' o) :
      RunC P host C s f (ws ++ us) (.plain (.tryTable bt cs b) :: code) s' f' o
  | labelThrow {s s₁ : Store H} {f f₁ : Frame} {vs : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin} {a : Nat}
      (hin : RunC P host C s f [] inner s₁ f₁ (.throw a)) :
      RunC P host C s f vs (.label n cont inner :: code) s₁ f₁ (.throw a)
  /-- The handler's body falls through. -/
  | handlerNormal {s s₁ s' : Store H} {f f₁ f' : Frame} {vs us : List Val} {n : Nat}
      {cs : List Catch} {inner code : List Admin} {o : Out}
      (hin : RunC P host C s f [] inner s₁ f₁ (.normal us))
      (h : RunC P host C s₁ f₁ (vs ++ us) code s' f' o) :
      RunC P host C s f vs (.handler n cs inner :: code) s' f' o
  /-- A branch, a return or a trap passes through a handler. -/
  | handlerBr {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n l : Nat} {cs : List Catch}
      {inner code : List Admin} (hin : RunC P host C s f [] inner s₁ f₁ (.br l us)) :
      RunC P host C s f vs (.handler n cs inner :: code) s₁ f₁ (.br l (vs ++ us))
  | handlerRet {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n : Nat} {cs : List Catch}
      {inner code : List Admin} (hin : RunC P host C s f [] inner s₁ f₁ (.ret us)) :
      RunC P host C s f vs (.handler n cs inner :: code) s₁ f₁ (.ret (vs ++ us))
  | handlerTrap {s s₁ : Store H} {f f₁ : Frame} {vs : List Val} {n : Nat} {cs : List Catch}
      {inner code : List Admin} (hin : RunC P host C s f [] inner s₁ f₁ .trap) :
      RunC P host C s f vs (.handler n cs inner :: code) s₁ f₁ .trap
  /-- A thrown exception is caught by the first matching clause: a branch to its label. -/
  | handlerCatch {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n a : Nat} {l : LabelIdx}
      {cs : List Catch} {inner code : List Admin} (hin : RunC P host C s f [] inner s₁ f₁ (.throw a))
      (hc : Catches s₁ f₁ a cs (some (us, l))) :
      RunC P host C s f vs (.handler n cs inner :: code) s₁ f₁ (.br l.toNat (vs ++ us))
  /-- No clause matches: the exception propagates. -/
  | handlerRethrow {s s₁ : Store H} {f f₁ : Frame} {vs : List Val} {n a : Nat} {cs : List Catch}
      {inner code : List Admin} (hin : RunC P host C s f [] inner s₁ f₁ (.throw a))
      (hc : Catches s₁ f₁ a cs none) :
      RunC P host C s f vs (.handler n cs inner :: code) s₁ f₁ (.throw a)
  /-- A data-dependent branch reads its operands (`BrStep`). -/
  | brData {s s' : Store H} {f f' : Frame} {ws us us' : List Val} {i : Instr} {X : List Admin}
      {code : List Admin} {o : Out} (hb : BrStep s f us i us' X)
      (h : RunC P host C s f (ws ++ us') (X ++ code) s' f' o) :
      RunC P host C s f (ws ++ us) (.plain i :: code) s' f' o
  | block {s s' : Store H} {f f' : Frame} {ws us : List Val} {bt : BlockType} {b : List Instr}
      {t₁ t₂ : List CValType} {code : List Admin} {o : Out}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
      (h : RunC P host C s f ws (.label t₂.length [] (vals us ++ expression b) :: code) s' f' o) :
      RunC P host C s f (ws ++ us) (.plain (.block bt b) :: code) s' f' o
  | loop {s s' : Store H} {f f' : Frame} {ws us : List Val} {bt : BlockType} {b : List Instr}
      {t₁ t₂ : List CValType} {code : List Admin} {o : Out}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
      (h : RunC P host C s f ws (.label t₁.length [.loop bt b] (vals us ++ expression b) :: code)
        s' f' o) :
      RunC P host C s f (ws ++ us) (.plain (.loop bt b) :: code) s' f' o
  | if_ {s s' : Store H} {f f' : Frame} {ws : List Val} {k : BitVec 32} {bt : BlockType}
      {t e : List Instr} {code : List Admin} {o : Out}
      (h : RunC P host C s f ws (.plain (.block bt (if k = 0 then e else t)) :: code) s' f' o) :
      RunC P host C s f (ws ++ [.i32 k]) (.plain (.if_ bt t e) :: code) s' f' o
  /-- The label's body falls through: its values are pushed. -/
  | labelNormal {s s₁ s' : Store H} {f f₁ f' : Frame} {vs us : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin} {o : Out}
      (hin : RunC P host C s f [] inner s₁ f₁ (.normal us))
      (h : RunC P host C s₁ f₁ (vs ++ us) code s' f' o) :
      RunC P host C s f vs (.label n cont inner :: code) s' f' o
  /-- The body branches to the label itself: the continuation runs on the top `n` values. -/
  | labelBr0 {s s₁ s' : Store H} {f f₁ f' : Frame} {vs us₁ us₂ : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin} {o : Out}
      (hin : RunC P host C s f [] inner s₁ f₁ (.br 0 (us₁ ++ us₂))) (hn : us₂.length = n)
      (h : RunC P host C s₁ f₁ vs (vals us₂ ++ expression cont ++ code) s' f' o) :
      RunC P host C s f vs (.label n cont inner :: code) s' f' o
  | labelBrSucc {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n l : Nat}
      {cont : List Instr} {inner code : List Admin}
      (hin : RunC P host C s f [] inner s₁ f₁ (.br (l + 1) us)) :
      RunC P host C s f vs (.label n cont inner :: code) s₁ f₁ (.br l (vs ++ us))
  | labelRet {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin}
      (hin : RunC P host C s f [] inner s₁ f₁ (.ret us)) :
      RunC P host C s f vs (.label n cont inner :: code) s₁ f₁ (.ret (vs ++ us))
  | labelTrap {s s₁ : Store H} {f f₁ : Frame} {vs : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin}
      (hin : RunC P host C s f [] inner s₁ f₁ .trap) :
      RunC P host C s f vs (.label n cont inner :: code) s₁ f₁ .trap

  /-- `return_call x` resolves its callee and ends the region in a pending tail call: Core's
  `return_call` step to `REF.FUNC_ADDR a; RETURN_CALL_REF`. The call itself is made when the
  enclosing `FRAME` is replaced. -/
  | returnCall {s : Store H} {f : Frame} {vs : List Val} {x : FuncIdx} {a : Nat}
      {fi : FuncInst H} {code : List Admin} (hfi : s.func? f x = some (a, fi)) :
      RunC P host C s f vs (.plain (.returnCall x) :: code) s f
        (.tail vs a (.returnCallRefType fi.type))
  /-- `return_call_ref` (in either representation `c`) on a function reference: a pending tail
  call. -/
  | returnCallRef {s : Store H} {f : Frame} {ws : List Val} {a : Nat} {c : Admin}
      {code : List Admin} (hc : c.IsReturnCallRef) :
      RunC P host C s f (ws ++ [.ref (.func a)]) (c :: code) s f (.tail ws a c)
  /-- `return_call_ref` on a null reference: a pending tail call of null. -/
  | returnCallRefNull {s : Store H} {f : Frame} {ws : List Val} {c : Admin} {code : List Admin}
      (hc : c.IsReturnCallRef) :
      RunC P host C s f (ws ++ [.ref .null]) (c :: code) s f (.tailNull ws c)
  /-- `return_call_indirect x y` runs as `table.get x; ref.cast (ref null y);
  return_call_ref y`, the code Core's step rewrites it to. -/
  | returnCallIndirect {s s' : Store H} {f f' : Frame} {vs : List Val} {x : TableIdx}
      {y : TypeIdx} {code : List Admin} {o : Out}
      (h : RunC P host C s f vs (.plain (.tableGet x) :: .plain (.refCast ⟨true, .typeIdx y⟩) ::
        .plain (.returnCallRef y) :: code) s' f' o) :
      RunC P host C s f vs (.plain (.returnCallIndirect x y) :: code) s' f' o
  /-- A pending tail call passes through a label (`return_call_ref-label`). -/
  | labelTail {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin} {a : Nat} {c : Admin}
      (hin : RunC P host C s f [] inner s₁ f₁ (.tail us a c)) :
      RunC P host C s f vs (.label n cont inner :: code) s₁ f₁ (.tail (vs ++ us) a c)
  | labelTailNull {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin} {c : Admin}
      (hin : RunC P host C s f [] inner s₁ f₁ (.tailNull us c)) :
      RunC P host C s f vs (.label n cont inner :: code) s₁ f₁ (.tailNull (vs ++ us) c)
  /-- A pending tail call passes through a handler (`return_call_ref-handler`): the callee
  runs outside it, so the handler does not catch its exceptions. -/
  | handlerTail {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n : Nat}
      {cs : List Catch} {inner code : List Admin} {a : Nat} {c : Admin}
      (hin : RunC P host C s f [] inner s₁ f₁ (.tail us a c)) :
      RunC P host C s f vs (.handler n cs inner :: code) s₁ f₁ (.tail (vs ++ us) a c)
  | handlerTailNull {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n : Nat}
      {cs : List Catch} {inner code : List Admin} {c : Admin}
      (hin : RunC P host C s f [] inner s₁ f₁ (.tailNull us c)) :
      RunC P host C s f vs (.handler n cs inner :: code) s₁ f₁ (.tailNull (vs ++ us) c)

  /-- `call x` asks the oracle `C` for the callee's run, on the top `ps.length` values in
  parameter order. The callee's flow lists its results top first (`Binaryen.Flow`); the top
  `rs.length` of them are pushed. The frame is the caller's. -/
  | call {s s₁ s' : Store H} {f f' : Frame} {ws us vs : List Val} {x : FuncIdx} {a : Nat}
      {fi : FuncInst H} {ps rs : List CValType} {fl : Binaryen.Flow} {code : List Admin}
      {o : Out} (hfi : s.func? f x = some (a, fi)) (hty : DefType.funcType? fi.type = some (ps, rs))
      (hn : us.length = ps.length) (hcall : C s a us (s₁, fl)) (hvs : fl.retVals = some vs)
      (h : RunC P host C s₁ f (ws ++ (vs.take rs.length).reverse) code s' f' o) :
      RunC P host C s f (ws ++ us) (.plain (.call x) :: code) s' f' o
  | callTrap {s s₁ : Store H} {f : Frame} {ws us : List Val} {x : FuncIdx} {a : Nat}
      {fi : FuncInst H} {ps rs : List CValType} {code : List Admin}
      (hfi : s.func? f x = some (a, fi)) (hty : DefType.funcType? fi.type = some (ps, rs))
      (hn : us.length = ps.length) (hcall : C s a us (s₁, .trap)) :
      RunC P host C s f (ws ++ us) (.plain (.call x) :: code) s₁ f .trap
  | callThrow {s s₁ : Store H} {f : Frame} {ws us : List Val} {x : FuncIdx} {a t : Nat}
      {fi : FuncInst H} {ps rs : List CValType} {code : List Admin}
      (hfi : s.func? f x = some (a, fi)) (hty : DefType.funcType? fi.type = some (ps, rs))
      (hn : us.length = ps.length) (hcall : C s a us (s₁, .throw t)) :
      RunC P host C s f (ws ++ us) (.plain (.call x) :: code) s₁ f (.throw t)

/-- The oracle that answers no call. -/
def noCall : Abstract.CallRel H := fun _ _ _ _ => False

/-- An oracle restricted to the calls satisfying `G` (for example typed arguments on a typed
native store). Region runs with `C.guard G` carry `G` at every call they make. -/
def guardCall (G : Store H → Nat → List Val → Prop) (C : Abstract.CallRel H) : Abstract.CallRel H :=
  fun s a us r => G s a us ∧ C s a us r

/-- **Soundness of a call oracle for Core 3.0**: every answer of `C` for a Wasm-typed function
is a Core run of the call (`ref.func a; call_ref`) on its arguments, in any caller frame, to
the corresponding result: the top `rs.length` results (reversed into stack order), a trap, or a
thrown exception. A named hypothesis; the intended instance is `Abstract.closedCall`. -/
def CallSound (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H) : Prop :=
  ∀ (s s₁ : Store H) (f : Frame) (a : Nat) (fi : FuncInst H) (ps rs : List CValType)
    (us : List Val) (fl : Binaryen.Flow),
    s.funcs[a]? = some fi → DefType.funcType? fi.type = some (ps, rs) → us.length = ps.length →
    C s a us (s₁, fl) →
    (∀ vs, fl.retVals = some vs → Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s₁, f, vals (vs.take rs.length).reverse⟩) ∧
    (fl = .trap → Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s₁, f, [.trap]⟩) ∧
    (∀ t, fl = .throw t → Steps P host ⟨s, f, vals us ++ [.ref (.func a), .callRefType fi.type]⟩
        ⟨s₁, f, throwing t⟩)

/-- **The call-free region semantics**: `RunC` with no call answered. -/
abbrev Run (P : Profile) (host : HostSemantics H) := RunC P host noCall

/-- Sequencing with calls answered by `C`: after a first part ends in state `s₁, f₁` with
outcome `o₁`, the second part `B` runs on fall-through; any other outcome skips `B`. -/
def ThenC (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H) (s₁ : Store H)
    (f₁ : Frame) : Out → List Admin → Store H → Frame → Out → Prop
  | .normal us, B, s', f', o => RunC P host C s₁ f₁ us B s' f' o
  | o₁, _, s', f', o => o = o₁ ∧ s' = s₁ ∧ f' = f₁

/-- Call-free sequencing: `ThenC` with no call answered. -/
abbrev Then (P : Profile) (host : HostSemantics H) := ThenC P host noCall

/-- What a `FRAME_n` returns for a body outcome. Falling through needs exactly `n` values; a
`return` keeps the top `n`. A branch out of the frame does not happen in validated code and
has no result. A pending tail call of null traps (`return_call_ref-frame-null`); a pending tail
call of a function replaces the frame by the callee's, so it has no result of this frame. -/
def FrameOut (n : Nat) : Out → List Admin → Prop
  | .normal us, c => us.length = n ∧ c = vals us
  | .ret us, c => ∃ us₁ ws, us = us₁ ++ ws ∧ ws.length = n ∧ c = vals ws
  | .trap, c => c = [.trap]
  | .throw a, c => c = throwing a
  | .tailNull _ _, c => c = [.trap]
  | .br _ _, _ => False
  | .tail _ _ _, _ => False

end Silmaril.Wasm.Cfg.Region

/-! ## Divergence -/

namespace Silmaril.Wasm.Cfg.Region

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

variable {H : Type}

/-- One layer of a diverging region run, with the rest of the divergence in `R`. A label
diverges inside, or its body ends (a terminating `Run`) and the continuation diverges. Every
rule either takes at least one Core step or moves to a strictly smaller code (`val`,
`labelIn`). -/
inductive DivF (P : Profile) (host : HostSemantics H)
    (R : Store H → Frame → List Val → List Admin → Prop) :
    Store H → Frame → List Val → List Admin → Prop where
  | val {s : Store H} {f : Frame} {vs : List Val} {a : Admin} {v : Val} {code : List Admin}
      (hv : a.val? = some v) (h : R s f (vs ++ [v]) code) : DivF P host R s f vs (a :: code)
  | simple {s s₁ : Store H} {f f₁ : Frame} {vs vs₁ : List Val} {i : Instr} {code : List Admin}
      (hi : SingleThreaded.Det.famOf (.plain i) ≠ .control)
      (h₁ : Steps P host ⟨s, f, vals vs ++ [.plain i]⟩ ⟨s₁, f₁, vals vs₁⟩)
      (h : R s₁ f₁ vs₁ code) : DivF P host R s f vs (.plain i :: code)
  | brIf {s : Store H} {f : Frame} {ws : List Val} {k : BitVec 32} {l : LabelIdx}
      {code : List Admin} (h : R s f ws ((if k = 0 then [] else [.plain (.br l)]) ++ code)) :
      DivF P host R s f (ws ++ [.i32 k]) (.plain (.brIf l) :: code)
  | brData {s : Store H} {f : Frame} {ws us us' : List Val} {i : Instr} {X code : List Admin}
      (hb : BrStep s f us i us' X) (h : R s f (ws ++ us') (X ++ code)) :
      DivF P host R s f (ws ++ us) (.plain i :: code)
  | block {s : Store H} {f : Frame} {ws us : List Val} {bt : BlockType} {b : List Instr}
      {t₁ t₂ : List CValType} {code : List Admin}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
      (h : R s f ws (.label t₂.length [] (vals us ++ expression b) :: code)) :
      DivF P host R s f (ws ++ us) (.plain (.block bt b) :: code)
  | loop {s : Store H} {f : Frame} {ws us : List Val} {bt : BlockType} {b : List Instr}
      {t₁ t₂ : List CValType} {code : List Admin}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
      (h : R s f ws (.label t₁.length [.loop bt b] (vals us ++ expression b) :: code)) :
      DivF P host R s f (ws ++ us) (.plain (.loop bt b) :: code)
  | if_ {s : Store H} {f : Frame} {ws : List Val} {k : BitVec 32} {bt : BlockType}
      {t e : List Instr} {code : List Admin}
      (h : R s f ws (.plain (.block bt (if k = 0 then e else t)) :: code)) :
      DivF P host R s f (ws ++ [.i32 k]) (.plain (.if_ bt t e) :: code)
  | tryTable {s : Store H} {f : Frame} {ws us : List Val} {bt : BlockType} {cs : List Catch}
      {b : List Instr} {t₁ t₂ : List CValType} {code : List Admin}
      (hbt : f.module.blockType? bt = some (t₁, t₂)) (hm : us.length = t₁.length)
      (h : R s f ws (.handler t₂.length cs [.label t₂.length [] (vals us ++ expression b)] :: code)) :
      DivF P host R s f (ws ++ us) (.plain (.tryTable bt cs b) :: code)
  | handlerIn {s : Store H} {f : Frame} {vs : List Val} {n : Nat} {cs : List Catch}
      {inner code : List Admin} (h : R s f [] inner) :
      DivF P host R s f vs (.handler n cs inner :: code)
  | handlerNormal {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n : Nat} {cs : List Catch}
      {inner code : List Admin} (hin : Run P host s f [] inner s₁ f₁ (.normal us))
      (h : R s₁ f₁ (vs ++ us) code) : DivF P host R s f vs (.handler n cs inner :: code)
  /-- The label's body diverges. -/
  | labelIn {s : Store H} {f : Frame} {vs : List Val} {n : Nat} {cont : List Instr}
      {inner code : List Admin} (h : R s f [] inner) :
      DivF P host R s f vs (.label n cont inner :: code)
  | labelNormal {s s₁ : Store H} {f f₁ : Frame} {vs us : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin}
      (hin : Run P host s f [] inner s₁ f₁ (.normal us)) (h : R s₁ f₁ (vs ++ us) code) :
      DivF P host R s f vs (.label n cont inner :: code)
  | labelBr0 {s s₁ : Store H} {f f₁ : Frame} {vs us₁ us₂ : List Val} {n : Nat}
      {cont : List Instr} {inner code : List Admin}
      (hin : Run P host s f [] inner s₁ f₁ (.br 0 (us₁ ++ us₂))) (hn : us₂.length = n)
      (h : R s₁ f₁ vs (vals us₂ ++ expression cont ++ code)) :
      DivF P host R s f vs (.label n cont inner :: code)

/-- **Diverging region runs**: the greatest fixed point of `DivF`, as membership in some
`DivF`-closed relation. -/
def RunDiv (P : Profile) (host : HostSemantics H) (s : Store H) (f : Frame) (vs : List Val)
    (code : List Admin) : Prop :=
  ∃ R : Store H → Frame → List Val → List Admin → Prop,
    (∀ s f vs code, R s f vs code → DivF P host R s f vs code) ∧ R s f vs code

/-- **The atomic obligation**: the Core reduction of every non-control instruction, on any
values, store and frame, terminates. Termination includes ending in a trap. This is a named
hypothesis of completeness for divergence, not part of `RunDiv`: `RunDiv` itself never
appeals to Core divergence. -/
def AtomTerm (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ (s : Store H) (f : Frame) (vs : List Val) (i : Instr),
    SingleThreaded.Det.famOf (.plain i) ≠ .control →
      Acc (fun a b => Step P host b a) (⟨s, f, vals vs ++ [.plain i]⟩ : Config H)

end Silmaril.Wasm.Cfg.Region

/-! ## Runs along the basic blocks of a sequence -/

namespace Silmaril.Wasm.Cfg.Region

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type}

/-- A run along a list of basic blocks (`Cfg.Segment`): each block runs (`Run` of its
instructions); falling through moves to the next block with the values it leaves; any other
outcome (a branch, return, trap or exception, decided by the block's terminator) ends the
sequence. -/
inductive SegRun (P : Profile) (host : HostSemantics H) :
    Store H → Frame → List Val → List Segment → Store H → Frame → Out → Prop where
  | nil {s : Store H} {f : Frame} {vs : List Val} : SegRun P host s f vs [] s f (.normal vs)
  | next {s s₁ s' : Store H} {f f₁ f' : Frame} {vs us : List Val} {sg : Segment}
      {segs : List Segment} {o : Out}
      (h : Run P host s f vs (expression sg.instrs) s₁ f₁ (.normal us))
      (hk : SegRun P host s₁ f₁ us segs s' f' o) : SegRun P host s f vs (sg :: segs) s' f' o
  | exit {s s' : Store H} {f f' : Frame} {vs : List Val} {sg : Segment} {segs : List Segment}
      {o : Out} (h : Run P host s f vs (expression sg.instrs) s' f' o) (ho : ∀ us, o ≠ .normal us) :
      SegRun P host s f vs (sg :: segs) s' f' o

end Silmaril.Wasm.Cfg.Region
