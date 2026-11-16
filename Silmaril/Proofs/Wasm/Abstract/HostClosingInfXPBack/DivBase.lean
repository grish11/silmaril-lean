module

public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.Empty
public import Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack.Handler

/-!
# Divergence after a nonempty log: bookkeeping (proofs)

* **Labelled runs then divergence** (`EvDiv`): through an answered host call (`evDiv_event`), at
  a host call (`evDiv_at_host`), in front of more code (`evDiv_append`), and its log is consistent
  (`evDiv_consistent`). `noDiv_of_evRun` (deterministic profile, typed start): a configuration
  with a labelled run to a configuration with no step does not diverge after any extension of
  that run's log; the uniform way the simulation rules out a finished part.
* **Divergent behaviours of `wasmEvFunDXP`**: a descent in front of a divergent behaviour of its
  target (`div_descend`), logged host-free divergence of a callee's body (`div_logDiv`), the
  descents to a reached call (`descends_reach`) and to a frame-level tail call
  (`descends_tailL`).
* **Host-free divergence of a typed call** in any frame, under values: `FunDivXP`
  (`funDivXP_of_call_diverges`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract
open Silmaril.Wasm.Logic.Core
open Silmaril.Wasm.Interp
open Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Abstract.CallXP
open Silmaril.Wasm.Abstract.XRecursionP Silmaril.Wasm.Abstract.XDivergeP
open Silmaril.Wasm.Binaryen (BExpr liftInstrs)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H}

/-! ## Labelled runs then divergence -/

/-- Two answers of the same host event lead to the same configuration. -/
theorem hEvStep_some_det {K A B : Config H} {e : Call (wasmHostSig H)}
    (hA : HEvStep P host K (some e) A) (hB : HEvStep P host K (some e) B) : A = B := by
  obtain ⟨E, a, hd, -, -, rfl⟩ := hA
  obtain ⟨E', a', hd', -, -, rfl⟩ := hB
  rw [hd] at hd'
  simp only [Option.some.injEq, Prod.mk.injEq] at hd'
  obtain ⟨rfl, -⟩ := hd'
  rfl

/-- A labelled run with no event from a configuration at a host call stays there. -/
theorem evRunN_nil_at_host {k : Nat} {K c : Config H} {x : Ctx × Nat × H × List Val}
    (hd : decompose? K.store K.code = some x) (h : EvRunN P host k K [] c) : c = K := by
  suffices key : ∀ k y cs, EvRunN P host k y cs c → y = K → cs = [] → c = K from
    key _ _ _ h rfl rfl
  clear h
  intro k y cs hy
  induction hy with
  | refl => intro h _; exact h
  | silent hs _ ih =>
    intro hy hcs
    subst hy
    rcases hs with hs | ⟨rfl, -⟩
    · exact (noFree_of_decompose hd hs).elim
    · exact ih rfl hcs
  | event => intro _ hcs; cases hcs

/-- **At a host call, a labelled run whose log starts with the event `e` goes through the answer
of `e`**, strictly fewer steps after it. -/
theorem evRunN_event_det {n : Nat} {K K₁ c : Config H} {e : Call (wasmHostSig H)}
    {q : List (Call (wasmHostSig H))} (he : HEvStep P host K (some e) K₁)
    (h : EvRunN P host n K (e :: q) c) : ∃ m < n, EvRunN P host m K₁ q c := by
  obtain ⟨E, a, hd, hs, -, hK₁⟩ := he
  suffices key : ∀ n y cs, EvRunN P host n y cs c → y = K → cs = e :: q →
      ∃ m < n, EvRunN P host m K₁ q c from key _ _ _ h rfl rfl
  clear h
  intro n y cs hy
  induction hy with
  | refl => intro _ h; cases h
  | @silent m y z c₃ cs hs' hrest ih =>
    intro hy hcs
    subst hy
    rcases hs' with h' | ⟨rfl, -⟩
    · exact (noFree_of_decompose hd h').elim
    · obtain ⟨m', hm', h'⟩ := ih rfl hcs
      exact ⟨m', by omega, h'⟩
  | @event m y z c₃ e' cs hs' hrest _ =>
    intro hy hcs
    subst hy
    obtain ⟨rfl, rfl⟩ := List.cons.inj hcs
    obtain ⟨E', a', hd', -, -, hz⟩ := hs'
    rw [hd] at hd'
    simp only [Option.some.injEq, Prod.mk.injEq] at hd'
    obtain ⟨rfl, rfl, -⟩ := hd'
    have hzK : z = K₁ := by rw [hz, hK₁]
    subst hzK
    exact ⟨m, by omega, hrest⟩

/-- **Through an answered host call**, the rest of the log diverges after it. -/
theorem evDiv_event {n : Nat} {K K₁ : Config H} {e : Call (wasmHostSig H)}
    {rest : List (Call (wasmHostSig H))} (h : EvDiv P host n K (e :: rest))
    (he : HEvStep P host K (some e) K₁) : ∃ m, EvDiv P host m K₁ rest := by
  rcases h with ⟨h, -⟩ | ⟨k, cs₀, e', c₀, c₁, -, hcs, hr, he', hd⟩
  · cases h
  obtain ⟨E, a, hdK, -⟩ := id he
  rcases cs₀ with _ | ⟨x, cs₀⟩
  · simp only [List.nil_append, List.cons.injEq] at hcs
    obtain ⟨rfl, rfl⟩ := hcs
    obtain rfl := evRunN_nil_at_host hdK hr
    exact ⟨0, .inl ⟨rfl, hEvStep_some_det he' he ▸ hd⟩⟩
  · simp only [List.cons_append, List.cons.injEq] at hcs
    obtain ⟨rfl, rfl⟩ := hcs
    obtain ⟨m, -, hm⟩ := evRunN_event_det he hr
    exact ⟨m, .inr ⟨m, cs₀, e', c₀, c₁, le_refl _, rfl, hm, he', hd⟩⟩

theorem evDiv_at_host_aux {k : Nat} {K c₀ c₁ : Config H} {x : Ctx × Nat × H × List Val}
    {cs₀ : List (Call (wasmHostSig H))} {e' : Call (wasmHostSig H)}
    (hdK : decompose? K.store K.code = some x) (hr : EvRunN P host k K cs₀ c₀)
    (he' : HEvStep P host c₀ (some e') c₁) (hd : Diverges P (fun _ _ _ _ => False) c₁) :
    ∃ e rest K₁ m, cs₀ ++ [e'] = e :: rest ∧ HEvStep P host K (some e) K₁ ∧
      EvDiv P host m K₁ rest := by
  induction hr with
  | refl => exact ⟨e', [], c₁, 0, rfl, he', .inl ⟨rfl, hd⟩⟩
  | silent hs _ ih =>
    rcases hs with hs | ⟨rfl, -⟩
    · exact (noFree_of_decompose hdK hs).elim
    · exact ih hdK he'
  | @event n' K K₂ c₃ e cs hs hrest _ =>
    exact ⟨e, cs ++ [e'], K₂, n', rfl, hs, .inr ⟨n', cs, e', c₃, c₁, le_refl _, rfl, hrest, he', hd⟩⟩

/-- **At a host call**, a divergence after a nonempty log answers it first. -/
theorem evDiv_at_host {n : Nat} {K : Config H} {x : Ctx × Nat × H × List Val}
    {cs : List (Call (wasmHostSig H))} (hdK : decompose? K.store K.code = some x)
    (h : EvDiv P host n K cs) :
    ∃ e rest K₁ m, cs = e :: rest ∧ HEvStep P host K (some e) K₁ ∧ EvDiv P host m K₁ rest := by
  rcases h with ⟨rfl, hd⟩ | ⟨k, cs₀, e', c₀, c₁, -, rfl, hr, he', hd⟩
  · obtain ⟨b, hb, -⟩ := hd.unfold
    exact (noFree_of_decompose hdK hb).elim
  · exact evDiv_at_host_aux hdK hr he' hd

/-- The log of a divergence after a log is consistent. -/
theorem evDiv_consistent {n : Nat} {K : Config H} {cs : List (Call (wasmHostSig H))}
    (h : EvDiv P host n K cs) : (coreHostRel host).Consistent cs := by
  rcases h with ⟨rfl, -⟩ | ⟨k, cs₀, e, c₀, c₁, -, rfl, hr, he, -⟩
  · intro c hc; cases hc
  · have hrun : EvRun P host K (cs₀ ++ [e]) c₁ :=
      evRun_trans (evRunN_evRun hr) (.event he (.refl _))
    exact evRun_consistent hrun

theorem consistent_append {a b : List (Call (wasmHostSig H))}
    (h : (coreHostRel host).Consistent (a ++ b)) :
    (coreHostRel host).Consistent a ∧ (coreHostRel host).Consistent b :=
  ⟨fun c hc => h c (List.mem_append_left _ hc), fun c hc => h c (List.mem_append_right _ hc)⟩

/-- A divergent run in front of more code. -/
theorem diverges_append {host' : HostSemantics H} {s : Store H} {f : Frame} {es : List Admin}
    (rest : List Admin) (h : Diverges P host' ⟨s, f, es⟩) :
    Diverges P host' ⟨s, f, es ++ rest⟩ := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun c : Config H => ∃ d : Config H, c = ⟨d.store, d.frame, d.code ++ rest⟩ ∧
      Diverges P host' d) ?_ (a := ⟨s, f, es ++ rest⟩) ⟨⟨s, f, es⟩, rfl, h⟩
  rintro _ ⟨⟨s, f, es⟩, rfl, hd⟩
  obtain ⟨⟨s', f', es'⟩, hb, hd'⟩ := hd.unfold
  refine ⟨⟨s', f', es' ++ rest⟩, ?_, ⟨s', f', es'⟩, rfl, hd'⟩
  simpa [vals] using Silmaril.Wasm.Logic.Core.Step.ctx (P := P) (host := host') [] rest hb

theorem evRunN_append_code {k : Nat} {X Y : Config H} {q : List (Call (wasmHostSig H))}
    (rest : List Admin) (h : EvRunN P host k X q Y) :
    EvRunN P host k ⟨X.store, X.frame, X.code ++ rest⟩ q ⟨Y.store, Y.frame, Y.code ++ rest⟩ := by
  induction h with
  | refl => exact .refl _
  | silent hs _ ih =>
    refine .silent ?_ ih
    simpa [vals] using hEvStep_ctx [] rest hs
  | event hs _ ih =>
    refine .event ?_ ih
    simpa [vals] using hEvStep_ctx [] rest hs

/-- **A divergence after a log in front of more code.** -/
theorem evDiv_append {n : Nat} {s : Store H} {f : Frame} {es : List Admin}
    {cs : List (Call (wasmHostSig H))} (rest : List Admin) (h : EvDiv P host n ⟨s, f, es⟩ cs) :
    EvDiv P host n ⟨s, f, es ++ rest⟩ cs := by
  rcases h with ⟨rfl, hd⟩ | ⟨k, cs₀, e, c₀, c₁, hk, rfl, hr, he, hd⟩
  · exact .inl ⟨rfl, diverges_append rest hd⟩
  · refine .inr ⟨k, cs₀, e, ⟨c₀.store, c₀.frame, c₀.code ++ rest⟩,
      ⟨c₁.store, c₁.frame, c₁.code ++ rest⟩, hk, rfl, evRunN_append_code rest hr, ?_,
      diverges_append rest hd⟩
    simpa [vals] using hEvStep_ctx [] rest he

/-- A host-free run is a run with any host. -/
theorem steps_host {c c' : Config H} (h : Steps P NH c c') : Steps P host c c' := by
  induction h with
  | refl => exact .refl
  | tail _ st ih => exact ih.tail (Step.of_noHost host st)

/-- **A final form under values runs host-free to a configuration with no step.** -/
theorem final_of_ends {oc : Outcome} {code : List Admin} (he : oc.Ends code) (s : Store H)
    (f : Frame) (pre : List Val) :
    ∃ X : Config H, Steps P NH ⟨s, f, vals pre ++ code⟩ X ∧
      ∀ (host' : HostSemantics H) c', ¬ Step P host' X c' := by
  rcases oc with ws | ⟨l, ws⟩ | ws | _ | a | ⟨ws, a, r⟩ | ⟨ws, r⟩
  · refine ⟨_, .refl, fun _ => outcome_ends_stuck (o := .normal (pre ++ ws)) ?_ s f⟩
    simp only [Outcome.Ends] at he ⊢
    simp [he, vals]
  · obtain ⟨x, rest, hx, rfl⟩ := he
    exact ⟨_, .refl, fun _ => outcome_ends_stuck (o := .br l (pre ++ ws))
      ⟨x, rest, hx, by simp [vals]⟩ s f⟩
  · obtain ⟨rest, rfl⟩ := he
    exact ⟨_, .refl, fun _ => outcome_ends_stuck (o := .ret (pre ++ ws)) ⟨rest, by simp [vals]⟩ s f⟩
  · simp only [Outcome.Ends] at he
    subst he
    exact ⟨_, steps_trap s f pre [], fun _ => outcome_ends_stuck (o := .trap) rfl s f⟩
  · simp only [Outcome.Ends] at he
    subst he
    exact ⟨_, by simpa using steps_throwing (P := P) (host := NH) s f pre a [],
      fun _ => outcome_ends_stuck (o := .throw a) rfl s f⟩
  · obtain ⟨hr, rest, rfl⟩ := he
    exact ⟨_, .refl, fun _ => outcome_ends_stuck (o := .tail (pre ++ ws) a r)
      ⟨hr, rest, by simp [vals]⟩ s f⟩
  · obtain ⟨hr, rest, rfl⟩ := he
    exact ⟨_, .refl, fun _ => outcome_ends_stuck (o := .tailNull (pre ++ ws) r)
      ⟨hr, rest, by simp [vals]⟩ s f⟩

section Det

variable {o : GrowOracle}

/-- **A labelled run to a configuration with no step rules out divergence after any extension
of its log** (deterministic profile, typed start). -/
theorem noDiv_of_evRun (hT : HostTyped host) {K X : Config H} {q : List (Call (wasmHostSig H))}
    (hf : EvRun (profile o) host K q X) (hX : ∀ c', ¬ Step (profile o) host X c')
    (ht : Sim.ContextTyped K) {n : Nat} {q' : List (Call (wasmHostSig H))}
    (h : EvDiv (profile o) host n K (q ++ q')) : False := by
  induction hf generalizing n with
  | refl => exact evDiv_stuck hX h
  | @silent K K₁ X q hs _ ih =>
    rcases hs with hs | ⟨rfl, -⟩
    · exact ih hX (ht.steps (.single hs)) (evDiv_through_steps (.single hs) ht h)
    · exact ih hX ht h
  | @event K K₁ X e q hs _ ih =>
    obtain ⟨m, hm⟩ := evDiv_event (by simpa using h) hs
    exact ih hX (ContextTyped.steps_typed hT ht (.single (hEvStep_step hs))) hm

end Det

/-! ## Divergent behaviours of the closure -/

theorem substPre_append' {L M : List (HCall H)} {q q' : List (Call (wasmHostSig H))}
    (h : Shape.SubstPre Cl L q) (h' : Shape.SubstPre Cl M q') :
    Shape.SubstPre Cl (L ++ M) (q ++ q') := by
  induction h with
  | nil => simpa using h'
  | ext _ ih => exact .ext ih
  | int hc _ ih =>
    rw [List.cons_append, List.append_assoc]
    exact .int hc ih

/-- **A descent in front of a divergent behaviour of its target.** -/
theorem div_descend {x y : (wasmHShape H).self.Op} {q q' : List (Call (wasmHostSig H))}
    (hD : Shape.Descends wasmHOpenXP Cl x q y)
    (h : (q', .div) ∈ wasmEvFunDXP y.2.2 (y.1, y.2.1)) :
    (q ++ q', .div) ∈ wasmEvFunDXP x.2.2 (x.1, x.2.1) := by
  rcases h with (hc | ⟨-, g, qq, N, hg0, hgs, hN, hqs⟩) | ⟨-, z, qs, u, q₀, hp, hl, hu, hy⟩
  · exact (wasmEvFunXP_ne_div hc).elim
  · refine .inl (.inr ⟨rfl, fun k => Nat.casesOn k x g, fun k => Nat.casesOn k q qq, N + 1, rfl,
      fun k => ?_, fun k hk => ?_, ?_⟩)
    · rcases k with _ | k
      · have hg0' : g 0 = y := hg0
        rw [← hg0'] at hD
        exact hD
      · exact hgs k
    · rcases k with _ | k
      · omega
      · exact hN k (by omega)
    · dsimp only at hqs ⊢
      rw [hqs, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      rfl
  · refine .inr ⟨rfl, z, q ++ qs, u, q₀, .step hD hp, hl, hu, ?_⟩
    show q ++ q' = (q ++ qs) ++ q₀
    rw [show q' = qs ++ q₀ from hy, List.append_assoc]

/-- **Logged host-free divergence of a callee's body** is a divergent behaviour of the call. -/
theorem div_logDiv {s : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {fn : Func}
    {l : List (OCall H)} {cs : List (Call (wasmHostSig H))} (hf : s.funcs[a]? = some fi)
    (hcode : fi.code = .wasm fn)
    (hl : LogDivXP s (Frame.forCall fi.module us fn.locals) [] (liftInstrs fn.body) l)
    (hq : Shape.SubstPre Cl (l.map OCall.lift) cs) : (cs, .div) ∈ wasmEvFunDXP s (a, us) :=
  .inr ⟨rfl, ⟨a, (us, s)⟩, [], l.map OCall.lift, cs, .refl _, ⟨fi, fn, l, hf, hcode, hl, rfl⟩,
    hq, rfl⟩

/-- **A call reached in a callee's body is a descent**, after the body's resolved calls. -/
theorem descends_reach {s : Store H} {a : Nat} {us : List Val} {fi : FuncInst H} {fn : Func}
    {ps rs : List Validation.CValType} {l : List (OCall H)} {z : (wasmOShape H).self.Op}
    {q : List (Call (wasmHostSig H))} (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hr : ReachLXP s (Frame.forCall fi.module us fn.locals) [] (liftInstrs fn.body) l z)
    (hq : Shape.SubstPre Cl (l.map OCall.lift) q) :
    Shape.Descends wasmHOpenXP Cl ⟨a, (us, s)⟩ q z := by
  obtain ⟨ws, f', hcut⟩ := reachLXP_cut hr
  refine ⟨((l ++ [OCall.mk z.1 z.2.1 z.2.2 (.inl ws) z.2.2]).map OCall.lift,
    endOfFlow .trap z.2.2), .inl ⟨fi, fn, ps, rs, z.2.2, f', .trap, .trap, _, hf, hcode, hty, hcut,
    rfl, rfl⟩, l.map OCall.lift, (.inl ws, z.2.2), [], ?_, hq⟩
  rw [List.map_append]
  rfl

/-- **A body ending in a pending tail call is a descent to the tail callee**, after the body's
resolved calls. -/
theorem descends_tailL {s s₁ : Store H} {a a' n : Nat} {us args : List Val} {fi : FuncInst H}
    {fn : Func} {ps rs : List Validation.CValType} {f₂ : Frame} {l : List (OCall H)}
    {q : List (Call (wasmHostSig H))} (hf : s.funcs[a]? = some fi) (hcode : fi.code = .wasm fn)
    (hty : Validation.DefType.funcType? fi.type = some (ps, rs))
    (hbody : EvalLXPh s (Frame.forCall fi.module us fn.locals) [] (liftInstrs fn.body) l
      (s₁, f₂, .tail a' args n))
    (hq : Shape.SubstPre Cl (l.map OCall.lift) q) :
    Shape.Descends wasmHOpenXP Cl ⟨a, (us, s)⟩ q ⟨a', (args, s₁)⟩ :=
  ⟨((l ++ [OCall.mk a' args s₁ (.inl []) s₁]).map OCall.lift,
    Abstract.tailAns rs.length n (.inl []) s₁),
    .inr (.inl ⟨fi, fn, ps, rs, s₁, s₁, f₂, a', n, args, .inl [], l, hf, hcode, hty, hbody, rfl⟩),
    l.map OCall.lift, (.inl [], s₁), [], by rw [List.map_append]; rfl, hq⟩

/-! ## Host-free divergence of a typed call -/

section Free

variable {o : GrowOracle} {tags : List TagInst}

/-- **A typed call diverging host-free in Core is `FunDivXP`**, in any frame, under values. -/
theorem funDivXP_of_call_diverges {s : Store H} {f : Frame} {pre us : List Val} {a : Nat}
    {cr : Admin} (hcr : cr.IsCallRef) (hcc : CallChkP tags s a us)
    (hct : Sim.ContextTyped ⟨s, f, Interp.callCode pre us a cr []⟩)
    (hd : Diverges (profile o) NH ⟨s, f, Interp.callCode pre us a cr []⟩) : FunDivXP s a us := by
  have hctP : CallTypedP tags s a us := ⟨hcc, f, cr, pre, [], hcr, hct⟩
  obtain ⟨hS, hts, fi, ps, rs, hfi, hty, hn⟩ := id hcc
  refine funDivXP_of_noReach hctP (fun h => ?_) (fun ⟨⟨s₂, fl⟩, hcall⟩ => ?_)
  · obtain ⟨T, hT, hdec⟩ := (hreach_core_both (P := profile o) (host := NH)).2 _ _ _ h hcc
      .hole f pre cr [] hcr
    exact not_diverges_at_host hct hd hT hdec
  · obtain ⟨-, hsnd⟩ := closedCallXP_sound (P := profile o) (host := NH) tags s a us (s₂, fl)
      hcall hts
    obtain ⟨-, hret, htr, hth⟩ := hsnd f fi ps rs cr hS hfi hty hn hcr
    have lift : ∀ {c : List Admin}, Steps (profile o) NH ⟨s, f, vals us ++ [.ref (.func a), cr]⟩
        ⟨s₂, f, c⟩ → Steps (profile o) NH ⟨s, f, Interp.callCode pre us a cr []⟩
          ⟨s₂, f, vals pre ++ c⟩ := fun h => by
      simpa [Interp.callCode] using Steps.ctx pre [] h
    rcases calleeP_flow hcc hcall with ⟨ws, hws⟩ | hab
    · exact not_diverges_at_end (oc := .normal (pre ++ (ws.take rs.length).reverse)) hct hd
        (lift (hret ws hws)) (by simp [Outcome.Ends, vals])
    · cases fl with
      | trap =>
        have hD := Silmaril.Wasm.Abstract.diverges_through_steps (o := o) (lift (htr rfl)) hct hd
        exact trap_not_diverges (r := []) (by simpa using hD)
      | throw t =>
        have hD := Silmaril.Wasm.Abstract.diverges_through_steps (o := o) (lift (hth t rfl)) hct hd
        exact throw_not_diverges (r := []) (by simpa using hD)
      | _ => exact hab.elim

end Free

end Silmaril.Proofs.Wasm.Abstract.HostClosingInfXPBack
