module

public import Silmaril.Wasm.Cfg.DanglingSession.Defs
public import Silmaril.Wasm.Cfg.DanglingBack.Thms
public import Silmaril.Wasm.Cfg.ExampleAlias.Thms
import Silmaril.Proofs.Wasm.Cfg.DanglingSession

@[expose] public section

/-!
# Threaded sessions with dangling host exceptions: theorems

Stage 3b. The instance session `InstSession.instSession I (profile o) s₀ =
threadS (instTripleS I (profile o)) s₀` (the universal host `instHost I`, every answer, dangling
host exceptions included) is the session of the CFG instance triple at the unrestricted host
`cfgInstTripleU I`, from every store of the relaxed domain `InstDomD I s₀` (definitions in
`Silmaril.Wasm.Cfg.DanglingSession.Defs`). Every observation is covered: finished rounds,
pending calls, divergence after a log, productive streams of the current round, and coherent
infinite sequences of rounds.

**1. What a round changes in the real store.** `instHost I` and its restrictions
`instHostQ I Q` (`instHostU`, `instHostL`, `instHostNT`) keep the whole store
(`NodeBridge.storePreserving_instHost`); every change comes from Wasm steps. A host-free Core step
(`step_store`, every profile) keeps the functions and the tags, only appends exceptions (a Wasm
`throw` allocates at `s.exns.length`) and keeps the tag invariants `TagsOk tags`; globals,
memories, tables, structs and arrays are not constrained here. Along a labelled run at
`instHostQ I Q` the same holds (`evRunQ_store`).

**Counterexample: the raw domain is not kept.** On `ExampleAlias` (`alI`, `alStore`, validated,
in `CfgInst.InstDom`), `run()` with `h()` answered by the dangling exception `0` is a finished
round of the instance triple ending in `alEnd` (`al_round`, `reach_alEnd`), whose exception at
`0` names itself: `alEnd` is not `StoreOk`, so not in `InstDom` (`not_instDom_alEnd`). It is in
the relaxed domain (`instDomD_alEnd`). So no session statement can assume `StoreOk` or `InstDom`
at reachable stores.

**2. The real-store invariant.** `InstDomD I s`: the function clauses of `WellFormed`
(`FuncsWF`), checker acceptance at the store's tags, **`ExnsOk s.tags s` on the real store**
(every real exception's tag is a real tag and the instance has its field count), and the relaxed
store invariant `StoreOkD s`. `exn_typed` relates the real exceptions to the witness: the tag is
a real tag of parameter types `ts`, and the fields are, up to exception addresses, values of the
types `ts` on the witness. `acyclicExns` is not asserted. Entry: `instDomD_of_supported` (a
well-formed store in the checker's instruction profile), `instDomD_of_instDom` (`InstDom` with
supported functions). Preservation: `domD_of_round` (every finished round, trap rounds keeping
their store included, every profile), `domD_of_reach`, `funcs_of_reach`.

**3. The forward direction without `StoreOk`.** `DanglingExn.fin_sub_of`/`pend_sub_of`/
`inf_sub_of` take only the store check, `TagsOk` and the typed invocation;
`cfgInstTripleU_sub` uses them on `InstDomD`. The reverse inclusion `sub_cfgInstTripleU` uses
the relaxed instance `DanglingBack.backD` from `configOkD_of_domD`; with both, per question
`agree` (`AgreeAt`, every observation, deterministic profile `profile o`).

**4. Sessions.** `threadS_eq`, `instSession_eq`: `StratSession.threadS_congr` at every store
reachable by the instance session (`Reach`: finitely many finished rounds, returning, throwing or
trapping with their store), each in the domain by `domD_of_reach`, where `agree` gives the
finished rounds, pending calls and productive streams, hence `satP` and the session's finite
plays, pending plays, divergences and infinite plays. The infinite plays of a session are of two
kinds: finitely many finished rounds followed by a productive stream of the current round (at a
reachable store, covered by the third component of `agree`), and **coherent infinite sequences of
finished rounds** (`StratThread.InfRounds`): round `k` runs from the store `s k`, reachable by
the first `k` rounds (`reach_of_infRounds`) and hence in the domain, so the two triples have the
same such sequences (`infRounds_iff`, proved by induction on `k` in both directions; no one-round
equality is used at a store not shown reachable).

**5. What follows.** At the raw instance-session level only: `instSession I (profile o) s₀ =
cfgInstSessionU I s₀` on `InstDomD I s₀`, e.g. at every well-formed store in the checker's
instruction profile. The component semantics `core3SemD` does not feed host throws to instance
sessions, so this is not a statement about `core3SemD` or `CfgLegal.cfgSemD`.
-/

namespace Silmaril.Wasm.Cfg.DanglingSession

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Validation
open Silmaril.Wasm.Cfg.CfgInst Silmaril.Wasm.Cfg.DanglingExn Silmaril.Wasm.Cfg.ExampleAlias
open Silmaril.Wasm.Abstract (wasmHostSig EvRun)
open Silmaril.Wasm.Abstract.NodeBridge (qOf)
open Silmaril.Wasm.Abstract.InstSession (instTripleS instSession Res)
open Silmaril.Wasm.Interp (TagsOk)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)
open Silmaril.Games.Abstract.StratThread (Reach InfRounds)

/-! ## 1. What a round changes in the real store -/

/-- **A host-free Core step keeps the functions and the tags, only appends exceptions, and keeps
the tag invariants.** -/
theorem step_store {H : Type} {P : Numerics.Profile} {tags : List TagInst} {c c' : Config H}
    (h : Step P (fun _ _ _ _ => False) c c') :
    c'.store.funcs = c.store.funcs ∧ c'.store.tags = c.store.tags ∧
      c.store.exns <+: c'.store.exns ∧ (TagsOk tags c.store → TagsOk tags c'.store) :=
  Proofs.DanglingSession.step_store h

/-- **The same along a labelled run at a restricted universal host**, whose answers keep the
store. -/
theorem evRunQ_store {I : ScalarInstance} {Q : Store Nat → Result → Prop} {P : Numerics.Profile}
    {tags : List TagInst} {c c' : Config Nat} {cs : List (Call (wasmHostSig Nat))}
    (h : EvRun P (instHostQ I Q) c cs c') :
    c'.store.funcs = c.store.funcs ∧ c'.store.tags = c.store.tags ∧
      c.store.exns <+: c'.store.exns ∧ (TagsOk tags c.store → TagsOk tags c'.store) :=
  Proofs.DanglingSession.evRunQ_store h

/-! ## The counterexample -/

/-- **`run()` of `alI`, with `h()` answered by the dangling exception `0`, is a finished round of
the instance triple from `alStore` ending in `alEnd`** (every profile). -/
theorem al_round {P : Numerics.Profile} :
    ([⟨⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩, Answer.throw 0⟩],
      .ret (.inl ⟨⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩, .inr 0⟩) alEnd) ∈
      (instTripleS alI P).1 alStore ⟨⟨0, by decide⟩, ⟨[], .nil⟩⟩ :=
  Proofs.DanglingSession.al_round

theorem reach_alEnd {P : Numerics.Profile} : Reach (instTripleS alI P) alStore alEnd :=
  Proofs.DanglingSession.reach_alEnd

/-- **The explicit domain is not kept by the instance session**: `alEnd` is reached from
`alStore ∈ InstDom` and is not in `InstDom`. -/
theorem not_instDom_alEnd : ¬ InstDom alI alEnd := Proofs.DanglingSession.not_instDom_alEnd

theorem instDomD_alStore : InstDomD alI alStore := Proofs.DanglingSession.instDomD_alStore

/-- `alEnd` is in the relaxed domain. -/
theorem instDomD_alEnd : InstDomD alI alEnd := Proofs.DanglingSession.instDomD_alEnd

/-! ## 2. The relaxed domain -/

section Dom

variable {I : ScalarInstance}

theorem funcsWF_of_wf {s : Store Nat} (hw : I.WellFormed s) : FuncsWF I s :=
  Proofs.DanglingSession.funcsWF_of_wf hw

/-- **A well-formed store in the checker's instruction profile is in the relaxed domain.** -/
theorem instDomD_of_supported {s : Store Nat} (hw : I.WellFormed s)
    (hsup : Interp.CheckComplete.StoreSupported s.funcs) : InstDomD I s :=
  Proofs.DanglingSession.instDomD_of_supported hw hsup

/-- The explicit domain with supported functions is in the relaxed domain. -/
theorem instDomD_of_instDom {s : Store Nat} (hd : InstDom I s) (hF : DanglingTyped.FuncsSupp s) :
    InstDomD I s :=
  Proofs.DanglingSession.instDomD_of_instDom hd hF

/-- Every export question of the relaxed domain enters `ConfigOkD`. -/
theorem configOkD_of_domD {s : Store Nat} (hd : InstDomD I s) (a : I.F.Op) :
    DanglingTyped.ConfigOkD (invoke s (qOf I a).1 (qOf I a).2) :=
  Proofs.DanglingSession.configOkD_of_domD hd a

/-- **The real exceptions of the relaxed domain are typed up to exception addresses**: the tag of
an exception instance of `s` is a tag `ti` of `s`, of parameter types `ts`, and its fields are, up
to exception addresses, values of the types `ts` on a witness of `s`. -/
theorem exn_typed {s : Store Nat} (hd : InstDomD I s) {a : Nat} {e : ExnInst}
    (he : s.exns[a]? = some e) :
    ∃ (T : List TagInst) (X : List ExnInst) (ti : TagInst) (ts : Ty (.list .val))
      (fs : List Val), DanglingTyped.GhostOk s T X ∧ s.tags[e.tag]? = some ti ∧
      Expand ti.type (.func ts .nil) ∧ List.Forall₂ (DanglingTyped.ValApprox X.length) e.fields fs ∧
      List.Forall₂ (ValOk (DanglingTyped.gst s T X)) fs ts.toList :=
  Proofs.DanglingSession.exn_typed hd he

/-- **Every finished round of the instance triple from the relaxed domain ends in the relaxed
domain, with the same functions** (every profile). -/
theorem domD_of_round {P : Numerics.Profile} {s s₁ : Store Nat} (hd : InstDomD I s)
    {a : I.F.Op} {c : List (Call I.E)} {b : Res I.exports ⊕ PUnit}
    (hm : (c, .ret b s₁) ∈ (instTripleS I P).1 s a) : InstDomD I s₁ ∧ s₁.funcs = s.funcs :=
  Proofs.DanglingSession.domD_of_round hd hm

/-- **The relaxed domain persists along the instance session.** -/
theorem domD_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDomD I s₀)
    (hr : Reach (instTripleS I P) s₀ s) : InstDomD I s :=
  Proofs.DanglingSession.domD_of_reach hd hr

theorem funcs_of_reach {P : Numerics.Profile} {s₀ s : Store Nat} (hd : InstDomD I s₀)
    (hr : Reach (instTripleS I P) s₀ s) : s.funcs = s₀.funcs :=
  Proofs.DanglingSession.funcs_of_reach hd hr

end Dom

/-! ## 3. Per question -/

section Agree

variable {I : ScalarInstance} {o : GrowOracle}

/-- **Every instance behaviour is a CFG behaviour at the unrestricted host**, on the relaxed
domain, at a deterministic profile. -/
theorem sub_cfgInstTripleU {s : Store Nat} (hd : InstDomD I s) (a : I.F.Op) :
    (instTripleS I (profile o)).1 s a ⊆ (cfgInstTripleU I).1 s a ∧
      (instTripleS I (profile o)).2.1 s a ⊆ (cfgInstTripleU I).2.1 s a ∧
      (instTripleS I (profile o)).2.2 s a ⊆ (cfgInstTripleU I).2.2 s a :=
  Proofs.DanglingSession.sub_cfgInstTripleU hd a

/-- **Every CFG behaviour at the unrestricted host is an instance behaviour**, on the relaxed
domain, at every profile. -/
theorem cfgInstTripleU_sub {P : Numerics.Profile} {s : Store Nat} (hd : InstDomD I s)
    (a : I.F.Op) :
    (cfgInstTripleU I).1 s a ⊆ (instTripleS I P).1 s a ∧
      (cfgInstTripleU I).2.1 s a ⊆ (instTripleS I P).2.1 s a ∧
      (cfgInstTripleU I).2.2 s a ⊆ (instTripleS I P).2.2 s a :=
  Proofs.DanglingSession.cfgInstTripleU_sub hd a

/-- **Per question on the relaxed domain, the two triples agree** on all observations. -/
theorem agree {s : Store Nat} (hd : InstDomD I s) (a : I.F.Op) :
    AgreeAt (instTripleS I (profile o)) (cfgInstTripleU I) s a :=
  Proofs.DanglingSession.agree hd a

end Agree

/-! ## 4. Sessions -/

section Session

variable {I : ScalarInstance} {o : GrowOracle}

/-- **The instance session is the CFG session at the unrestricted host**, from the relaxed
domain. -/
theorem threadS_eq {s₀ : Store Nat} (hd : InstDomD I s₀) :
    StratSession.threadS (instTripleS I (profile o)) s₀ =
      StratSession.threadS (cfgInstTripleU I) s₀ :=
  Proofs.DanglingSession.threadS_eq hd

theorem instSession_eq {s₀ : Store Nat} (hd : InstDomD I s₀) :
    instSession I (profile o) s₀ = cfgInstSessionU I s₀ :=
  Proofs.DanglingSession.instSession_eq hd

/-- Every store of a coherent infinite sequence of rounds is reachable. -/
theorem reach_of_infRounds {E : Sig.{0}} {S A B : Type} {t : ObsTriple E S A B} {s₀ : S}
    {a : ℕ → A} {r : ℕ → List (Call E) × B} {s : ℕ → S} (h : InfRounds t s₀ a r s) :
    ∀ k, Reach t s₀ (s k) :=
  Proofs.DanglingSession.reach_of_infRounds h

/-- **Coherent infinite sequences of rounds agree**, from the relaxed domain. -/
theorem infRounds_iff {s₀ : Store Nat} (hd : InstDomD I s₀) {a : ℕ → I.F.Op}
    {r : ℕ → List (Call I.E) × (Res I.exports ⊕ PUnit)} {s : ℕ → Store Nat} :
    InfRounds (instTripleS I (profile o)) s₀ a r s ↔ InfRounds (cfgInstTripleU I) s₀ a r s :=
  Proofs.DanglingSession.infRounds_iff hd

/-- **At a well-formed store in the checker's instruction profile**, the instance session is the
CFG session at the unrestricted host. -/
theorem instSession_eq_of_supported {s₀ : Store Nat} (hw : I.WellFormed s₀)
    (hsup : Interp.CheckComplete.StoreSupported s₀.funcs) :
    instSession I (profile o) s₀ = cfgInstSessionU I s₀ :=
  instSession_eq (instDomD_of_supported hw hsup)

end Session

end Silmaril.Wasm.Cfg.DanglingSession
