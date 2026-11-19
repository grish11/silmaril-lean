module

public import Silmaril.Wasm.Cfg.DanglingExn.Defs
public import Silmaril.Wasm.Cfg.ExampleHostExn.Defs
public import Silmaril.Wasm.Abstract.HostClosingXP.Defs
public import Silmaril.Wasm.Abstract.HostSessionXP.Defs
public import Silmaril.Wasm.Abstract.InstSession.Defs
public import Silmaril.Wasm.Execution.Core.Soundness.Defs
import Silmaril.Proofs.Wasm.Cfg.DanglingExn
import Silmaril.Proofs.Wasm.Cfg.DanglingExnFwd
import Silmaril.Proofs.Wasm.Cfg.DanglingExnRun

@[expose] public section

/-!
# Dangling exception addresses: theorems

A host answer `throw a` whose address names no exception instance of the store
(`Dangling s a`) is not typed (`not_resultTyped_throw`), so the bridge's backward simulation,
which carries Core typing through `HostTyped`, does not cover it. This module classifies what
both semantics do with such an exception, and proves the direction of the bridge that needs no
typing.

**1. Handler resolution, native and Core.** The native side resolves a `try_table` by
`Cfg.Region.Catches`, Core by the `throw_ref-handler-*` rules; both read `s.exns[a]?` through the
same `CatchMatches`.

* `catchMatches_iff`: a tagged clause (`catch`, `catch_ref`) never matches a dangling exception;
  a catch-all clause always does;
* `catches_iff` (native): `Catches s f a cs r ↔ r = danglingCatch a cs`. Tagged clauses are
  skipped; `catch_all l` catches with no payload; `catch_all_ref l` catches and pushes the
  dangling reference `ref.exn a` itself; otherwise the exception is rethrown;
* `step_handler_iff`, `step_handler_nil_iff` (Core, one step, every profile and host): from
  `HANDLER_n{c :: cs} (throwing a)` the only step is `danglingNext n a cs c`; from
  `HANDLER_n{} (throwing a)` it is `throwing a`;
* `steps_handler`, `handler_final` (Core, whole handler): the handler runs to
  `handlerOut a (danglingCatch a cs)`, and every run that stops ends there. This is the native
  resolution `catches_iff`: **native and Core agree** on every handler;
* `evalLXPh_try` (native `EvalLXPh`): a `try_table` body throwing a dangling exception ends as
  `danglingCatch` says: a branch with the payload, or the exception rethrown.

**2. Uses of the reference.** `catch_all_ref` pushes `ref.exn a` as a value.

* `steps_throwRef`: `throw_ref` rethrows it, whatever the values below (`throw_ref-instrs`); the
  rethrown exception is resolved by `catches_iff` again, so a later tagged clause again fails;
* `not_refOk_exn`, `not_valOk_exn`: no reference type types it (`Ref_ok/exn` needs the instance);
  so Core's `ref.test` answers `0` (`step_refTest`) and `ref.cast` traps (`step_refCast`) for every
  target type, `exnref` included. These instructions are outside the checker profile
  (`Interp.XProfile.xInstr`), which has no native counterpart for them;
* `not_resultTyped_throw`: the host answer is not typed (the `HostTyped` failure);
* `not_storeOk_of_global`: a store with the reference in a global is not `StoreOk`. Code in the
  checker profile can do this (`catch_all_ref` then `global.set` into an `exnref` global), so a
  round with a dangling exception can leave a store outside `InvOkXP`.

**3. Aliasing.** Wasm `throw` allocates at `s.exns.length`, the least dangling address, in Core
(`Step.throw`) and natively (`EvalLXPh.throw`) alike. `catches_alloc`: after the allocation a
tagged clause catches the formerly dangling address. On `hxMod` (`ExampleHostExn`, no exception
in `hxStore`): `hx_dangling`, `hx_catches_before` (`catch 0 0` does not catch address `0`),
`hx_core_alloc`, `hx_native_alloc` (both allocate `hxExn v` at address `0`, leaving
`hxThrown v`), `hx_catches_after` (`catch 0 0` now catches address `0` with payload `v`). A
dangling reference kept across that allocation names the new exception. Both semantics read
the store at handler time, so this does not separate them. Aliasing also makes **cyclic
exceptions**: a `throw` whose payload is the reference `ref.exn s.exns.length` (a dangling host
exception caught by `catch_all_ref`) allocates an exception whose field names itself, in Core
(`step_throw_self`) and natively (`evalLXPh_throw_self`) alike, and the resulting store is not
`StoreOk` (`not_storeOk_addExn_self`, the `acyclicExns` clause). A relaxed store invariant for
dangling exceptions therefore cannot keep `acyclicExns` on the actual store.

**4. Fixture.** `callH_dangling_round`: in the CFG session triple, `callH`
(`try_table (catch 0 0) (call 0)`) with the host answering `throw 0` and keeping `hxStore` ends
with the uncaught exception `0` (`callH_caught_existing` catches the same answer from
`hxThrown v`). `callH_dangling_core_U`: the same round is a Core run at the unrestricted universal
host `instHostU hxI`. `ExampleHostExn.trapH_caught` already shows `catch_all` catching any address.

**5. The forward direction.** `fin_sub`, `pend_sub`, `inf_sub`: for a host in the typed host
slice with the checker invariants (`HostSliceT`, `HostSliceE`), possibly throwing dangling
addresses, every finished behaviour, pending call and productive stream of the native session
triple at a question in `InvOkXP` is one of the open Core triple. No `HostTyped` is needed, and
no `StoreOk` either: `fin_sub_of`, `pend_sub_of`, `inf_sub_of` take only the store check
`StoreChkE (ehExt tags) s.funcs`, the tag invariants `TagsOk tags s` and the typed invocation.
`cfgInstTripleU_sub`: on `InstDom`, every behaviour of the CFG instance triple at `instHostU I`
(`cfgInstTripleU`) is one of the instance triple `instTripleS I P`.

**Not claimed.** The converse inclusion (`instTripleS ⊆ cfgInstTripleU` on `InstDom`) is open.
The backward simulation types Core configurations (`ContextTyped`), and with a dangling
reference on the stack, in a local or in a global no Core typing holds
(`not_valOk_exn`). The obstruction is in the proof, not in the semantics: items 1–3 find no
behaviour on which the two sides differ.
-/

namespace Silmaril.Wasm.Cfg.DanglingExn

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
open Silmaril.Wasm.Cfg.Region (Catches)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {s : Store H} {f : Frame}
  {a : Nat}

/-! ## 1. Handler resolution -/

/-- **A dangling exception matches exactly the catch-all clauses.** -/
theorem catchMatches_iff (hd : Dangling s a) {c : Catch} :
    CatchMatches s f a c ↔ c.CatchesAll :=
  Proofs.DanglingExn.catchMatches_iff hd

/-- **Native handler resolution of a dangling exception.** -/
theorem catches_iff (hd : Dangling s a) {cs : List Catch} {r : Option (List Val × LabelIdx)} :
    Catches s f a cs r ↔ r = danglingCatch a cs :=
  Proofs.DanglingExn.catches_iff hd

/-- **Core, one step**: a handler around a dangling exception drops a tagged clause or branches
at a catch-all clause, and does nothing else. -/
theorem step_handler_iff (hd : Dangling s a) {n : Nat} {c : Catch} {cs : List Catch}
    {c' : Config H} :
    Step P host ⟨s, f, [.handler n (c :: cs) (throwing a)]⟩ c' ↔
      c' = ⟨s, f, danglingNext n a cs c⟩ :=
  Proofs.DanglingExn.step_handler_iff hd

/-- **Core, one step**: an empty handler rethrows (any address). -/
theorem step_handler_nil_iff {n : Nat} {c' : Config H} :
    Step P host ⟨s, f, [.handler n [] (throwing a)]⟩ c' ↔ c' = ⟨s, f, throwing a⟩ :=
  Proofs.DanglingExn.step_handler_nil_iff

/-- **Core, the whole handler**: it runs to the native resolution. -/
theorem steps_handler (hd : Dangling s a) (n : Nat) (cs : List Catch) :
    Steps P host ⟨s, f, [.handler n cs (throwing a)]⟩
      ⟨s, f, handlerOut a (danglingCatch a cs)⟩ :=
  Proofs.DanglingExn.steps_handler hd n cs

/-- **Core, the whole handler**: every run that stops ends at the native resolution. -/
theorem handler_final (hd : Dangling s a) (n : Nat) (cs : List Catch) {c' : Config H}
    (h : Steps P host ⟨s, f, [.handler n cs (throwing a)]⟩ c')
    (hst : ∀ c'', ¬ Step P host c' c'') :
    c' = ⟨s, f, handlerOut a (danglingCatch a cs)⟩ :=
  Proofs.DanglingExn.handler_final hd n cs h hst

/-- **Native `try_table`**: a body throwing a dangling exception ends as `danglingCatch` says. -/
theorem evalLXPh_try {s₀ : Store H} {f₀ f₁ : Frame} {stk : List Val} {bt : BlockType}
    {cs : List Catch} {body es : List Binaryen.BExpr} {np nr : Nat} {l : List (Abstract.OCall H)}
    (har : Binaryen.arity f₀ bt = some (np, nr))
    (hbody : Abstract.EvalLXPh s₀ f₀ (stk.take np) body l (s, f₁, .flow (.throw a)))
    (hd : Dangling s a) :
    Abstract.EvalLXPh s₀ f₀ stk (.tryTable bt cs body :: es) l
      (match danglingCatch a cs with
        | some (us, l') => (s, f₁, .flow (.brk l'.toNat (us.reverse ++ stk.drop np)))
        | none => (s, f₁, .flow (.throw a))) :=
  Proofs.DanglingExn.evalLXPh_try har hbody hd

/-! ## 2. Uses of the reference -/

/-- **`throw_ref` rethrows any exception reference**, dropping the values below it. -/
theorem steps_throwRef (ws : List Val) :
    Steps P host ⟨s, f, vals ws ++ throwing a⟩ ⟨s, f, throwing a⟩ :=
  Proofs.DanglingExn.steps_throwRef ws

/-- **No reference type types a dangling exception reference.** -/
theorem not_refOk_exn (hd : Dangling s a) {rt : CRefType} : ¬ RefOk s (.exn a) rt :=
  Proofs.DanglingExn.not_refOk_exn hd

theorem not_valOk_exn (hd : Dangling s a) {t : CValType} : ¬ ValOk s (.ref (.exn a)) t :=
  Proofs.DanglingExn.not_valOk_exn hd

/-- Core's `ref.test` answers `0` on a dangling exception reference, for every target type. -/
theorem step_refTest (hd : Dangling s a) {rt : RefType} :
    Step P host ⟨s, f, [.ref (.exn a), .plain (.refTest rt)]⟩ ⟨s, f, [constI32 0]⟩ :=
  .reference (.testFalse (not_refOk_exn hd))

/-- Core's `ref.cast` traps on a dangling exception reference, for every target type. -/
theorem step_refCast (hd : Dangling s a) {rt : RefType} :
    Step P host ⟨s, f, [.ref (.exn a), .plain (.refCast rt)]⟩ ⟨s, f, [.trap]⟩ :=
  .reference (.castFail (not_refOk_exn hd))

/-- **A dangling host exception is not a typed result.** -/
theorem not_resultTyped_throw (hd : Dangling s a) {ts : List CValType} :
    ¬ ResultTyped s (.throw a) ts :=
  Proofs.DanglingExn.not_resultTyped_throw hd

/-- **A store with a dangling exception reference in a global is not `StoreOk`.** -/
theorem not_storeOk_of_global (hd : Dangling s a) {gi : GlobalInst} (hg : gi ∈ s.globals)
    (hv : gi.value = .ref (.exn a)) : ¬ StoreOk s :=
  Proofs.DanglingExn.not_storeOk_of_global hd hg hv

/-! ## 3. Aliasing -/

/-- The next allocation address is dangling. -/
theorem dangling_length (s : Store H) : Dangling s s.exns.length := Nat.le_refl _

/-- **After an allocation at `s.exns.length`, a tagged clause catches that address.** -/
theorem catches_alloc (e : ExnInst) {x : TagIdx} {l : LabelIdx} {cs : List Catch}
    (ht : f.module.tags[x.toNat]? = some e.tag) :
    Catches (s.addExn e) f s.exns.length (.catch_ x l :: cs) (some (e.fields, l)) :=
  .catch_ (by simp [Store.addExn]) ht

/-- **Aliasing makes cyclic exceptions, Core.** A Wasm `throw` whose payload is the next
allocation address `s.exns.length` (for instance a dangling host exception caught by
`catch_all_ref`) allocates an exception whose field is a reference to itself. -/
theorem step_throw_self {x : TagIdx} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil)) (hn : ts.length = 1) :
    Step P host ⟨s, f, [.ref (.exn s.exns.length), .plain (.throw x)]⟩
      ⟨s.addExn ⟨ta, [.ref (.exn s.exns.length)]⟩, f, throwing s.exns.length⟩ :=
  Step.throw (vs := [.ref (.exn s.exns.length)]) ht he hn.symm

/-- **Aliasing makes cyclic exceptions, natively**: the same allocation. -/
theorem evalLXPh_throw_self {x : TagIdx} {ta : Nat} {ti : TagInst} {ts : Ty (.list .val)}
    (ht : s.tag? f x = some (ta, ti)) (he : Expand ti.type (.func ts .nil)) (hn : ts.length = 1) :
    Abstract.EvalLXPh s f [.ref (.exn s.exns.length)] [.op (.throw x) []] []
      (s.addExn ⟨ta, [.ref (.exn s.exns.length)]⟩, f, .flow (.throw s.exns.length)) := by
  have h := Abstract.EvalLXPh.throw (es := []) (l := []) (stk₁ := [.ref (.exn s.exns.length)])
    .nil ht he (by simp [hn])
  rwa [hn] at h

/-- **A self-referencing exception breaks `StoreOk`** (`acyclicExns`), whatever the rest. -/
theorem not_storeOk_addExn_self (ta : Nat) :
    ¬ StoreOk (s.addExn ⟨ta, [.ref (.exn s.exns.length)]⟩) := fun h =>
  h.acyclicExns s.exns.length (by simp [Store.addExn]) (.refExn (i := 0)
    (e := ⟨ta, [.ref (.exn s.exns.length)]⟩) (by simp [Store.addExn]) rfl)

open Silmaril.Wasm.Cfg.ExampleHostExn

/-- Address `0` is dangling in `hxStore`. -/
theorem hx_dangling : Dangling hxStore 0 := Proofs.DanglingExn.hx_dangling

/-- In `hxStore`, `catch 0 0` does not catch address `0`. -/
theorem hx_catches_before :
    Catches hxStore (Frame.forCall hxMI [] []) 0 [catchE] none :=
  Proofs.DanglingExn.hx_catches_before

/-- Core: `throw $e` with payload `v` allocates `hxExn v` at address `0`. -/
theorem hx_core_alloc {host : HostSemantics Nat} (v : BitVec 32) :
    Step P host ⟨hxStore, Frame.forCall hxMI [] [], [constI32 v, .plain (.throw ⟨0⟩)]⟩
      ⟨hxThrown v, Frame.forCall hxMI [] [], throwing 0⟩ :=
  Proofs.DanglingExn.hx_core_alloc v

/-- Native: the same allocation. -/
theorem hx_native_alloc (v : BitVec 32) :
    Abstract.EvalLXPh hxStore (Frame.forCall hxMI [] []) [.i32 v] [.op (.throw ⟨0⟩) []] []
      (hxThrown v, Frame.forCall hxMI [] [], .flow (.throw 0)) :=
  Proofs.DanglingExn.hx_native_alloc v

/-- In `hxThrown v`, `catch 0 0` catches address `0` with payload `v`. -/
theorem hx_catches_after (v : BitVec 32) :
    Catches (hxThrown v) (Frame.forCall hxMI [] []) 0 [catchE] (some ([.i32 v], l0)) :=
  Proofs.DanglingExn.hx_catches_after v

/-! ## 4. Fixture -/

/-- **`callH` with a dangling host exception, on the CFG closure**: uncaught by `catch 0 0`. -/
theorem callH_dangling_round :
    ([hostAns hxStore (.throw 0) hxStore], End.ret (.inl (.inr 0)) hxStore) ∈
      CfgClosure.cfgSessionTripleC.1 hxStore (1, []) :=
  Proofs.DanglingExn.callH_dangling_round

/-- The unrestricted universal host of `hxI` gives that answer. -/
theorem hx_instHostU_throw : CfgInst.instHostU hxI 0 hxStore [] (.returned hxStore (.throw 0)) :=
  Proofs.DanglingExn.hx_instHostU_throw

/-- **The same round in Core**, at `instHostU hxI`, with exactly that host event. -/
theorem callH_dangling_core_U :
    Abstract.EvRun P (CfgInst.instHostU hxI) (invoke hxStore 1 [])
      [hostAns hxStore (.throw 0) hxStore] ⟨hxStore, {}, throwing 0⟩ :=
  Proofs.DanglingExn.callH_dangling_core_U

/-! ## 5. The forward direction -/

section Fwd

open Silmaril.Wasm.Abstract (coreHostRel InvOkXP sessionTripleXP)
open Silmaril.Wasm.Abstract.NodeBridge (coreTripleSO)
open Silmaril.Wasm.Interp (HostSliceT HostSliceE)

variable {tags : List TagInst} {q : Nat × List Val}

/-- **Finished native session behaviours are open Core behaviours**, from the store check, the
tag invariants and a typed invocation alone (no `StoreOk`, no `HostTyped`). -/
theorem fin_sub_of (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hS : Interp.StoreChkE (Interp.ehExt tags) s.funcs) (hts : Interp.TagsOk tags s)
    (hinv : InvokeOk s q.1 q.2)
    {x : CallBeh (Abstract.wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)}
    (hx : x ∈ (CfgInst.openRestrict (coreHostRel host) sessionTripleXP).1 s q) :
    x ∈ (coreTripleSO P host).1 s q :=
  Proofs.DanglingExn.fin_sub_of hH hE hS hts hinv hx

/-- **Pending native session calls are reached Core callouts**, without `StoreOk`. -/
theorem pend_sub_of (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hS : Interp.StoreChkE (Interp.ehExt tags) s.funcs) (hts : Interp.TagsOk tags s)
    (hinv : InvokeOk s q.1 q.2)
    {x : List (Call (Abstract.wasmHostSig H)) × (Abstract.wasmHostSig H).Op}
    (hx : x ∈ (CfgInst.openRestrict (coreHostRel host) sessionTripleXP).2.1 s q) :
    x ∈ (coreTripleSO P host).2.1 s q :=
  Proofs.DanglingExn.pend_sub_of hH hE hS hts hinv hx

/-- **Productive native session streams are productive Core runs**, without `StoreOk`. -/
theorem inf_sub_of (hH : HostSliceT host) (hE : HostSliceE tags host)
    (hS : Interp.StoreChkE (Interp.ehExt tags) s.funcs) (hts : Interp.TagsOk tags s)
    (hinv : InvokeOk s q.1 q.2)
    {ω : Nat → Call (Abstract.wasmHostSig H)}
    (hx : ω ∈ (CfgInst.openRestrict (coreHostRel host) sessionTripleXP).2.2 s q) :
    ω ∈ (coreTripleSO P host).2.2 s q :=
  Proofs.DanglingExn.inf_sub_of hH hE hS hts hinv hx

/-- **Finished native session behaviours are open Core behaviours** (no `HostTyped`). -/
theorem fin_sub (hH : HostSliceT host) (hE : HostSliceE tags host) (hok : InvOkXP tags s q)
    {x : CallBeh (Abstract.wasmHostSig H) (Store H) ((List Val ⊕ Nat) ⊕ PUnit)}
    (hx : x ∈ (CfgInst.openRestrict (coreHostRel host) sessionTripleXP).1 s q) :
    x ∈ (coreTripleSO P host).1 s q :=
  Proofs.DanglingExn.fin_sub hH hE hok hx

/-- **Pending native session calls are reached Core callouts** (no `HostTyped`). -/
theorem pend_sub (hH : HostSliceT host) (hE : HostSliceE tags host) (hok : InvOkXP tags s q)
    {x : List (Call (Abstract.wasmHostSig H)) × (Abstract.wasmHostSig H).Op}
    (hx : x ∈ (CfgInst.openRestrict (coreHostRel host) sessionTripleXP).2.1 s q) :
    x ∈ (coreTripleSO P host).2.1 s q :=
  Proofs.DanglingExn.pend_sub hH hE hok hx

/-- **Productive native session streams are productive Core runs** (no `HostTyped`). -/
theorem inf_sub (hH : HostSliceT host) (hE : HostSliceE tags host) (hok : InvOkXP tags s q)
    {ω : Nat → Call (Abstract.wasmHostSig H)}
    (hx : ω ∈ (CfgInst.openRestrict (coreHostRel host) sessionTripleXP).2.2 s q) :
    ω ∈ (coreTripleSO P host).2.2 s q :=
  Proofs.DanglingExn.inf_sub hH hE hok hx

/-- **The CFG instance triple at the unrestricted host is contained in the instance triple**, on
the domain: finished behaviours, pending calls and productive streams. -/
theorem cfgInstTripleU_sub {I : Game.ScalarInstance} {s : Store Nat} (hd : CfgInst.InstDom I s)
    (a : I.F.Op) :
    (cfgInstTripleU I).1 s a ⊆ (Abstract.InstSession.instTripleS I P).1 s a ∧
      (cfgInstTripleU I).2.1 s a ⊆ (Abstract.InstSession.instTripleS I P).2.1 s a ∧
      (cfgInstTripleU I).2.2 s a ⊆ (Abstract.InstSession.instTripleS I P).2.2 s a :=
  Proofs.DanglingExn.cfgInstTripleU_sub hd a

end Fwd

end Silmaril.Wasm.Cfg.DanglingExn
