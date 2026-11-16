module

public import Silmaril.Proofs.Wasm.Component.Reference.SessionStrat.Rounds

/-!
# Simple components as session play objects

* `pubPlays_compSession`: the IR plays of `c.toComp.den (modSem P)` at `sigU` are the plays of
  the session object asking questions in range, read at `sigU` (`sessMove`);
* `compSession_inj`: at the deterministic profiles, `RefSessEquivD` is equality of the export
  types and of the session objects (`DStrategy` equality, including divergence and infinite
  plays), through `StratSession.threadS_eq_iff`;
* `mem_inf_compSession`, `sessInf_iff`: the infinite plays are the coherent infinite sequences
  of terminating session rounds, and for typed calls these are the infinite sequences of calls
  whose every finite prefix is a reference session behaviour.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.SessionStrat

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Games.Abstract.StratObs
open Silmaril.Games.Abstract.StratThread (Rounds StoreDet roundsMoves)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val

universe u

/-! ## Moves -/

theorem map_roundsMoves :
    ∀ rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit.{1})),
      (roundsMoves rs).map (sessMove ∘ StratSession.relMove) = twos (E := sigN 0) (rs.map toRound)
  | [] => rfl
  | (a, l, b) :: rs => by
    obtain rfl := calls_nil l
    show sessMove (StratSession.relMove (.inr (.ask a))) ::
        sessMove (StratSession.relMove (.inr (.ans a (.inl b)))) ::
        (roundsMoves rs).map (sessMove ∘ StratSession.relMove) = _
    rw [map_roundsMoves rs]
    rfl

theorem ask_mem_map_sessMove {p : List (Move (sigN 0) sessSig)} {q : Nat × Payload} :
    (Sum.inr (Ev.ask q) : Move (sigN 0) sigU) ∈ p.map sessMove ↔ Sum.inr (Ev.ask q) ∈ p := by
  constructor
  · intro h
    obtain ⟨o, ho, he⟩ := List.mem_map.mp h
    rcases o with e | (q' | ⟨q', x⟩) <;> simp only [sessMove, reduceCtorEq, Sum.inr.injEq,
      Ev.ask.injEq] at he
    subst he
    exact ho
  · intro h
    exact List.mem_map.mpr ⟨_, h, rfl⟩

theorem ask_mem_twos {q : Nat × Payload} :
    ∀ {Lu : List (Round sigU)}, (Sum.inr (Ev.ask q) : Move (sigN 0) sigU) ∈ twos Lu →
      ∃ x ∈ Lu, x.1 = q
  | [], h => nomatch h
  | ⟨q', A⟩ :: Lu, h => by
    rcases List.mem_cons.mp h with h | h
    · simp only [Sum.inr.injEq, Ev.ask.injEq] at h
      exact ⟨_, List.mem_cons_self, h.symm⟩
    rcases List.mem_cons.mp h with h | h
    · cases h
    · obtain ⟨x, hx, e⟩ := ask_mem_twos h
      exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

theorem twos_ask_mem : ∀ {Lu : List (Round sigU)} {x : Round sigU}, x ∈ Lu →
    (Sum.inr (Ev.ask x.1) : Move (sigN 0) sigU) ∈ twos Lu
  | ⟨_, _⟩ :: _, _, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (twos_ask_mem h))

/-! ## Finite agreement -/

variable {P : Profile} {prof : ProfileKind}

/-- **The IR plays are the in-range plays of the session object.** -/
theorem pubPlays_compSession (P : Profile) (c : Simple) (hc : c.Good)
    (hi : ∃ I, c.mod.IsInst I) :
    pubPlays (c.toComp.den (modSem P)) =
      {q | ∃ p ∈ (compSession P c).toStrategy, AskedIn c.exports.length p ∧ p.map sessMove = q} := by
  obtain ⟨I, hI⟩ := hi
  rw [compSession_eq hI]
  have key : ∀ L : List (Round (sigN c.toComp.exports.length)), twos L ∈ c.toComp.den (modSem P) →
      ∃ s', Rounds (compTripleS P c I) I.store ((L.map Round.forget).map ofRound) s' := by
    intro L hL
    obtain ⟨s', hS⟩ := sessRounds_of_den hc hI hL
    exact ⟨s', rounds_of_spec (shaped_iff.mp (sessRounds_shaped hS)).2 (spec_of_sessRounds hS).1⟩
  have himg : ∀ L : List (Round (sigN c.toComp.exports.length)),
      ((roundsMoves ((L.map Round.forget).map ofRound)).map StratSession.relMove).map sessMove =
        (twos L).map forgetMove := by
    intro L
    rw [List.map_map, map_roundsMoves, map_toRound_ofRound, map_forgetMove_twos]
  ext q
  constructor
  · rintro ⟨p', hp', rfl⟩
    rcases den_shape _ c hp' with ⟨L, rfl⟩ | ⟨q₀, L, rfl⟩
    · obtain ⟨s', hR⟩ := key L hp'
      refine ⟨_, StratSession.mem_threadS.mpr ⟨_, StratThread.mem_threadT.mpr
        ⟨_, StratThread.run_idle_iff.mpr ⟨_, rfl, hR⟩⟩, rfl⟩, fun q hq => ?_, himg L⟩
      have h := ask_mem_map_sessMove.mpr hq
      rw [himg, map_forgetMove_twos] at h
      obtain ⟨x, hx, rfl⟩ := ask_mem_twos h
      exact forget_mem_lt hx
    · have hp₀ : twos L ∈ c.toComp.den (modSem P) :=
        (c.toComp.den (modSem P)).of_prefix hp' (List.prefix_append _ _)
      obtain ⟨s', hR⟩ := key L hp₀
      have hrun := (StratThread.run_idle_iff.mpr ⟨_, rfl, hR⟩).append
        (.cons (StratThread.TStep.ask _ (q₀.1.val, q₀.2)) (.nil _))
      have himg' : (((roundsMoves ((L.map Round.forget).map ofRound)) ++
          ([Sum.inr (Ev.ask (q₀.1.val, q₀.2))] :
            List (Move (sigN 0) (sig1 (Nat × Payload) (Payload ⊕ PUnit.{1}))))).map
              StratSession.relMove).map sessMove =
          (twos L ++ ([Sum.inr (Ev.ask q₀)] :
            List (Move (sigN 0) (sigN c.toComp.exports.length)))).map forgetMove := by
        rw [List.map_append, List.map_append, himg, List.map_append]
        rfl
      refine ⟨_, StratSession.mem_threadS.mpr ⟨_, StratThread.mem_threadT.mpr ⟨_, hrun⟩, rfl⟩,
        fun q hq => ?_, himg'⟩
      have h := ask_mem_map_sessMove.mpr hq
      rw [himg', List.map_append, map_forgetMove_twos] at h
      rcases List.mem_append.mp h with h | h
      · obtain ⟨x, hx, rfl⟩ := ask_mem_twos h
        exact forget_mem_lt hx
      · simp only [List.map_cons, List.map_nil, List.mem_singleton, forgetMove, Sum.inr.injEq,
          Ev.ask.injEq] at h
        subst h
        show q₀.1.val < c.exports.length
        rw [← toComp_length]
        exact q₀.1.isLt
  · rintro ⟨p, hp, hask, rfl⟩
    obtain ⟨p₀, ⟨y, hy⟩, rfl⟩ := StratSession.mem_threadS.mp hp
    obtain ⟨rs, s', hR, hshape⟩ := trun_shape noPlainTrap_compTripleS hy
    obtain ⟨hspec, -, hsh⟩ := spec_of_rounds hR
    have hlt : ∀ x ∈ rs.map toRound, x.1.1 < c.exports.length := by
      intro x hx
      refine hask x.1 (ask_mem_map_sessMove.mp ?_)
      rw [List.map_map]
      have hmem : (Sum.inr (Ev.ask x.1) : Move (sigN 0) sigU) ∈
          (roundsMoves rs).map (sessMove ∘ StratSession.relMove) := by
        rw [map_roundsMoves]
        exact twos_ask_mem hx
      rcases hshape with ⟨rfl, -⟩ | ⟨a, rfl, -⟩
      · exact hmem
      · rw [List.map_append]
        exact List.mem_append_left _ hmem
    obtain ⟨L, hL, hLe⟩ := den_of_sessRounds hc hI
      (sessRounds_of_spec (shaped_iff.mpr ⟨hlt, hsh⟩) hspec)
    rcases hshape with ⟨rfl, -⟩ | ⟨a, rfl, -⟩
    · refine ⟨twos L, hL, ?_⟩
      rw [map_forgetMove_twos, hLe, List.map_map, map_roundsMoves]
    · have ha : a.1 < c.toComp.exports.length := by
        rw [toComp_length]
        refine hask a (List.mem_map.mpr ⟨.inr (.ask a), ?_, rfl⟩)
        simp
      let q' : (sigN c.toComp.exports.length).Op := (⟨a.1, ha⟩, a.2)
      refine ⟨twos L ++ [.inr (.ask q')], ?_, ?_⟩
      · exact (c.toComp.den (modSem P)).receptive hL (path_twos _) (Step.ask q') trivial
      · rw [List.map_append, map_forgetMove_twos, hLe, List.map_append, List.map_append,
          List.map_map, map_roundsMoves]
        rfl

/-! ## Transfer between two components -/

section Transfer

variable {c c' : Simple} {len : c.exports.length = c'.exports.length}
  {I I' : Silmaril.Wasm.Game.ScalarInstance}

/-- A specification session on typed calls is completed rounds. -/
theorem rounds_of_sessSpec {calls : List (Fin c.exports.length × List IVal)}
    {outs : List (Option (List IVal))} {s s' : Store Nat}
    (hspec : SessSpec P c I s (specCalls c calls) outs s') (ht : TypedCalls c calls) :
    Rounds (compTripleS P c I) s ((sessLu calls outs).map ofRound) s' ∧
      sessCalls c (sessLu calls outs) = calls ∧ sessOuts c (sessLu calls outs) = outs := by
  have hS := sessRounds_of_sessSpec hspec
  have hlen : calls.length = outs.length := by simpa [specCalls] using sessSpec_length hspec
  obtain ⟨e₁, e₂⟩ := sessCalls_sessLu ht hlen
  refine ⟨rounds_of_spec (shaped_iff.mp (sessRounds_shaped hS)).2 ?_, e₁, e₂⟩
  rw [e₁, e₂]
  exact hspec

theorem typedQ_cast' (hty : SameTy c c' len) {q : Nat × Payload} {j : Fin c.exports.length}
    {vs : List IVal} (hq : c.sessQ q = some (j, vs)) : c'.sessQ q = some (Fin.cast len j, vs) := by
  rw [sessQ_eq, typedQ_cast hty, ← sessQ_eq, hq]
  rfl

/-- Session observations move completed rounds. -/
theorem rounds_transfer (hc : c.Adequate) (hc' : c'.Adequate) (hty : SameTy c c' len)
    (hI : c.mod.IsInst I) (hI' : c'.mod.IsInst I')
    (hsub : ∀ calls, TypedCalls c calls →
      sessObs P prof c calls ⊆ sessObs P prof c' (castCalls len calls))
    {rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))} {s : Store Nat}
    (h : Rounds (compTripleS P c I) I.store rs s) :
    ∃ s', Rounds (compTripleS P c' I') I'.store rs s' := by
  obtain ⟨hspec, ht, hsh⟩ := spec_of_rounds h
  have href := hsub _ ht (sess_specToRef P prof c hc hI _ _ s ht hspec)
  obtain ⟨I'', outs', s', hI'', hspec', heq⟩ :=
    sess_refToSpec P prof c' hc' _ (typedCalls_cast hty ht) href
  obtain rfl := refOuts_inj heq
  obtain rfl := isInst_unique hI'' hI'
  rw [← sessCalls_cast hty, ← sessOuts_cast hty] at hspec'
  have hR := rounds_of_spec (shapedU_cast hty hsh) hspec'
  rw [map_ofRound_toRound] at hR
  exact ⟨s', hR⟩

/-- Completed rounds move session observations. -/
theorem obs_transfer (hc : c.Adequate) (hc' : c'.Adequate) (hty : SameTy c c' len)
    (hI : c.mod.IsInst I) (hI' : c'.mod.IsInst I')
    (hR : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s,
      Rounds (compTripleS P c I) I.store rs s → ∃ s', Rounds (compTripleS P c' I') I'.store rs s')
    (calls : List (Fin c.exports.length × List IVal)) (ht : TypedCalls c calls) :
    sessObs P prof c calls ⊆ sessObs P prof c' (castCalls len calls) := by
  intro o ho
  obtain ⟨I'', outs, s, hI'', hspec, rfl⟩ := sess_refToSpec P prof c hc calls ht ho
  obtain rfl := isInst_unique hI'' hI
  obtain ⟨hR₀, e₁, e₂⟩ := rounds_of_sessSpec hspec ht
  obtain ⟨s', hR'⟩ := hR _ _ hR₀
  obtain ⟨hspec', -, -⟩ := spec_of_rounds hR'
  rw [map_toRound_ofRound, sessCalls_cast hty, sessOuts_cast hty, e₁, e₂] at hspec'
  exact sess_specToRef P prof c' hc' hI' _ outs s' (typedCalls_cast hty ht) hspec'

/-- Diverging session calls move divergent rounds. -/
theorem div_rounds_transfer (hty : SameTy c c' len) (hI : c.mod.IsInst I)
    (hI' : c'.mod.IsInst I')
    (hsub : ∀ calls j vs, TypedCalls c calls → ValTy.checkList c.exports[j].ty.params vs = true →
      sessDivs P c calls j vs ⊆ sessDivs P c' (castCalls len calls) (Fin.cast len j) vs)
    {rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))} {s : Store Nat}
    {a : Nat × Payload} {l : List (Call (sigN 0))}
    (h : Rounds (compTripleS P c I) I.store rs s) (hd : (l, End.div) ∈ (compTripleS P c I).1 s a) :
    ∃ s', Rounds (compTripleS P c' I') I'.store rs s' ∧
      (l, End.div) ∈ (compTripleS P c' I').1 s' a := by
  obtain ⟨j, vs, hq, hdiv⟩ := div_iff.mp hd
  obtain ⟨hspec, ht, hsh⟩ := spec_of_rounds h
  obtain ⟨I'', s', hI'', hspec', hdiv'⟩ :=
    hsub _ j vs ht hdiv.typed ⟨I, s, hI, hspec, hdiv⟩
  obtain rfl := isInst_unique hI'' hI'
  rw [← sessCalls_cast hty, ← sessOuts_cast hty] at hspec'
  have hR := rounds_of_spec (shapedU_cast hty hsh) hspec'
  rw [map_ofRound_toRound] at hR
  exact ⟨s', hR, div_iff.mpr ⟨Fin.cast len j, vs, typedQ_cast' hty hq, hdiv'⟩⟩

/-- Divergent rounds move diverging session calls. -/
theorem divs_transfer (hty : SameTy c c' len) (hI : c.mod.IsInst I) (hI' : c'.mod.IsInst I')
    (hD : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s a l,
      Rounds (compTripleS P c I) I.store rs s → (l, End.div) ∈ (compTripleS P c I).1 s a →
      ∃ s', Rounds (compTripleS P c' I') I'.store rs s' ∧
        (l, End.div) ∈ (compTripleS P c' I').1 s' a)
    (calls : List (Fin c.exports.length × List IVal)) (j : Fin c.exports.length) (vs : List IVal)
    (ht : TypedCalls c calls) (hv : ValTy.checkList c.exports[j].ty.params vs = true) :
    sessDivs P c calls j vs ⊆ sessDivs P c' (castCalls len calls) (Fin.cast len j) vs := by
  rintro outs ⟨I'', s, hI'', hspec, hdiv⟩
  obtain rfl := isInst_unique hI'' hI
  obtain ⟨hR, e₁, e₂⟩ := rounds_of_sessSpec hspec ht
  have hq : c.sessQ (j.val, .vals vs) = some (j, vs) := by
    rw [sessQ_eq]
    exact typedQ_typed j.isLt hv
  obtain ⟨s', hR', hd'⟩ := hD _ _ _ [] hR (div_iff.mpr ⟨j, vs, hq, hdiv⟩)
  obtain ⟨j', vs', hq', hdiv'⟩ := div_iff.mp hd'
  rw [typedQ_cast' hty hq] at hq'
  cases hq'
  obtain ⟨hspec', -, -⟩ := spec_of_rounds hR'
  rw [map_toRound_ofRound, sessCalls_cast hty, sessOuts_cast hty, e₁, e₂] at hspec'
  exact ⟨I', s', hI', hspec', hdiv'⟩

end Transfer

/-! ## Bisimilarity from transfers -/

/-- **Store-deterministic triples without plain traps whose completed and divergent rounds
transfer both ways are bisimilar.** -/
theorem obsEq_of_transfer {E : Sig.{u}} {S S' A B : Type u} {t : ObsTriple E S A B}
    {t' : ObsTriple E S' A B} {s₀ : S} {s₀' : S'} (ht : StoreDet t) (ht' : StoreDet t')
    (hn : ∀ s a c, (c, End.trap) ∉ t.1 s a) (hn' : ∀ s a c, (c, End.trap) ∉ t'.1 s a)
    (hpend : ∀ s s', satP t s = satP t' s') (hinf : ∀ s s', t.2.2 s = t'.2.2 s')
    (hR : ∀ rs s, Rounds t s₀ rs s → ∃ s', Rounds t' s₀' rs s')
    (hR' : ∀ rs s', Rounds t' s₀' rs s' → ∃ s, Rounds t s₀ rs s)
    (hD : ∀ rs s a c, Rounds t s₀ rs s → (c, End.div) ∈ t.1 s a →
      ∃ s', Rounds t' s₀' rs s' ∧ (c, End.div) ∈ t'.1 s' a)
    (hD' : ∀ rs s' a c, Rounds t' s₀' rs s' → (c, End.div) ∈ t'.1 s' a →
      ∃ s, Rounds t s₀ rs s ∧ (c, End.div) ∈ t.1 s a) :
    StratThread.ObsEq t t' s₀ s₀' := by
  refine ⟨fun s s' => ∃ rs, Rounds t s₀ rs s ∧ Rounds t' s₀' rs s', ?_, ⟨[], .nil _, .nil _⟩⟩
  rintro s s' ⟨rs, h, h'⟩
  refine ⟨fun a c => iff_of_false (hn _ _ _) (hn' _ _ _), fun a c => ⟨fun hd => ?_, fun hd => ?_⟩,
    hpend s s', hinf s s', fun a c b s₁ hb => ?_, fun a c b s₁' hb => ?_⟩
  · obtain ⟨s'', h'', hd''⟩ := hD rs s a c h hd
    rwa [rounds_functional ht' h' h'']
  · obtain ⟨s'', h'', hd''⟩ := hD' rs s' a c h' hd
    rwa [rounds_functional ht h h'']
  · have h₁ : Rounds t s₀ (rs ++ [(a, c, b)]) s₁ := rounds_snoc.mpr ⟨s, h, hb⟩
    obtain ⟨s₁', h₁'⟩ := hR _ _ h₁
    obtain ⟨s₂, h₂, hb'⟩ := rounds_snoc.mp h₁'
    obtain rfl := rounds_functional ht' h' h₂
    exact ⟨s₁', hb', rs ++ [(a, c, b)], h₁, h₁'⟩
  · have h₁' : Rounds t' s₀' (rs ++ [(a, c, b)]) s₁' := rounds_snoc.mpr ⟨s', h', hb⟩
    obtain ⟨s₁, h₁⟩ := hR' _ _ h₁'
    obtain ⟨s₂, h₂, hb'⟩ := rounds_snoc.mp h₁
    obtain rfl := rounds_functional ht h h₂
    exact ⟨s₁, hb', rs ++ [(a, c, b)], h₁, h₁'⟩

/-! ## The injection -/

theorem div_right {c c' : Simple} (h : RefSessEquivD P prof c c') :
    ∀ (calls' : List (Fin c'.exports.length × List IVal)) (j' : Fin c'.exports.length)
      (vs : List IVal), TypedCalls c' calls' → ValTy.checkList c'.exports[j'].ty.params vs = true →
      sessDivs P c' calls' j' vs ⊆
        sessDivs P c (castCalls h.len.symm calls') (Fin.cast h.len.symm j') vs := by
  intro calls' j' vs ht' hv'
  have ej : Fin.cast h.len (Fin.cast h.len.symm j') = j' := Fin.ext rfl
  have hv : ValTy.checkList c.exports[Fin.cast h.len.symm j'].ty.params vs = true := by
    have e1 : c'.exports[j'].ty = c.exports[Fin.cast h.len.symm j'].ty :=
      h.ty (Fin.cast h.len.symm j')
    rw [← e1]
    exact hv'
  have e := h.div (castCalls h.len.symm calls') (Fin.cast h.len.symm j') vs
    (typedCalls_cast (sameTy_symm h.ty) ht') hv
  rw [castCalls_cast h.len.symm calls', ej] at e
  exact e.symm.le

/-- **The injection of adequate simple components into session objects**, at the deterministic
profiles. -/
theorem compSession_inj (o : GrowOracle) (prof : ProfileKind) {c c' : Simple}
    (hc : c.Adequate) (hc' : c'.Adequate) :
    RefSessEquivD (profile o) prof c c' ↔
      SameTypes c c' ∧ compSession (profile o) c = compSession (profile o) c' := by
  obtain ⟨I, hI⟩ := hc.inst.inst
  obtain ⟨I', hI'⟩ := hc'.inst.inst
  rw [compSession_eq hI, compSession_eq hI']
  have hpend : ∀ s s', satP (compTripleS (profile o) c I) s = satP (compTripleS (profile o) c' I') s' :=
    fun s s' => by funext a; rw [satP_compTripleS, satP_compTripleS]
  constructor
  · intro h
    refine ⟨sameTypes_iff.mpr ⟨h.len, h.ty⟩, StratSession.threadS_eq_of_obsEq
      (obsEq_of_transfer (storeDet_compTripleS o) (storeDet_compTripleS o) noPlainTrap_compTripleS
        noPlainTrap_compTripleS hpend (fun _ _ => rfl) ?_ ?_ ?_ ?_)⟩
    · intro rs s hr
      exact rounds_transfer hc hc' h.ty hI hI' (fun calls ht => (h.obs calls ht).le) hr
    · intro rs s hr
      exact rounds_transfer hc' hc (sameTy_symm h.ty) hI' hI (obs_right h.toRefSessEquiv) hr
    · intro rs s a l hr hd
      exact div_rounds_transfer h.ty hI hI' (fun calls j vs ht hv => (h.div calls j vs ht hv).le)
        hr hd
    · intro rs s a l hr hd
      exact div_rounds_transfer (sameTy_symm h.ty) hI' hI (div_right h) hr hd
  · rintro ⟨hst, heq⟩
    obtain ⟨len, hty⟩ := sameTypes_iff.mp hst
    have hT := StratThread.threadT_eq_of_obsEq
      ((StratSession.threadS_eq_iff (storeDet_compTripleS o) (storeDet_compTripleS o)
        noPlainTrap_compTripleS noPlainTrap_compTripleS).mp heq)
    have hR : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s,
        Rounds (compTripleS (profile o) c I) I.store rs s →
        ∃ s', Rounds (compTripleS (profile o) c' I') I'.store rs s' := fun rs s h =>
      StratThread.mem_rounds.mp (hT ▸ StratThread.mem_rounds.mpr ⟨s, h⟩)
    have hR' : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s,
        Rounds (compTripleS (profile o) c' I') I'.store rs s →
        ∃ s', Rounds (compTripleS (profile o) c I) I.store rs s' := fun rs s h =>
      StratThread.mem_rounds.mp (hT.symm ▸ StratThread.mem_rounds.mpr ⟨s, h⟩)
    have hD : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s a l,
        Rounds (compTripleS (profile o) c I) I.store rs s →
        (l, End.div) ∈ (compTripleS (profile o) c I).1 s a →
        ∃ s', Rounds (compTripleS (profile o) c' I') I'.store rs s' ∧
          (l, End.div) ∈ (compTripleS (profile o) c' I').1 s' a := fun rs s a l h hd =>
      StratThread.mem_div.mp (hT ▸ StratThread.mem_div.mpr ⟨s, h, hd⟩)
    have hD' : ∀ (rs : List ((Nat × Payload) × List (Call (sigN 0)) × (Payload ⊕ PUnit))) s a l,
        Rounds (compTripleS (profile o) c' I') I'.store rs s →
        (l, End.div) ∈ (compTripleS (profile o) c' I').1 s a →
        ∃ s', Rounds (compTripleS (profile o) c I) I.store rs s' ∧
          (l, End.div) ∈ (compTripleS (profile o) c I).1 s' a := fun rs s a l h hd =>
      StratThread.mem_div.mp (hT.symm ▸ StratThread.mem_div.mpr ⟨s, h, hd⟩)
    refine ⟨⟨len, hty, fun calls ht => Set.Subset.antisymm
      (obs_transfer hc hc' hty hI hI' hR calls ht) ?_⟩, fun calls j vs ht hv =>
        Set.Subset.antisymm (divs_transfer hty hI hI' hD calls j vs ht hv) ?_⟩
    · have h := obs_transfer (prof := prof) hc' hc (sameTy_symm hty) hI' hI hR'
        (castCalls len calls) (typedCalls_cast hty ht)
      rwa [castCalls_cast] at h
    · have ej : Fin.cast len.symm (Fin.cast len j) = j := Fin.ext rfl
      have h := divs_transfer (sameTy_symm hty) hI' hI hD' (castCalls len calls) (Fin.cast len j)
        vs (typedCalls_cast hty ht) (by rw [hty]; exact hv)
      rwa [castCalls_cast, ej] at h

/-! ## Infinite plays -/

theorem mem_inf_compSession (o : GrowOracle) {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : c.mod.IsInst I) {J : Set (List (Move (sigN 0) sessSig))} :
    J ∈ (compSession (profile o) c).inf ↔
      ∃ a r s, StratThread.InfRounds (compTripleS (profile o) c I) I.store a r s ∧
        J = StratSession.sroundsPlay a r := by
  rw [compSession_eq hI, StratSession.mem_inf_iff_of_storeDet (storeDet_compTripleS o)]
  refine or_iff_right ?_
  rintro ⟨_, _, _, _, _, hω, _⟩
  simp [compTripleS] at hω

theorem sessLu_cons {n : Nat} (q : Fin n × List IVal) (o : Option (List IVal))
    (cs : List (Fin n × List IVal)) (os : List (Option (List IVal))) :
    sessLu (q :: cs) (o :: os) = ⟨(q.1.val, .vals q.2), o.map .vals⟩ :: sessLu cs os := by
  obtain ⟨j, vs⟩ := q
  rfl

theorem sessLu_ofFn {n : Nat} : ∀ {k : Nat} (f : Fin k → Fin n × List IVal)
    (g : Fin k → Option (List IVal)),
    sessLu (List.ofFn f) (List.ofFn g) =
      List.ofFn fun i => (⟨((f i).1.val, .vals (f i).2), (g i).map .vals⟩ : Round sigU)
  | 0, _, _ => rfl
  | _ + 1, f, g => by
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, sessLu_cons]
    exact congrArg (List.cons _) (sessLu_ofFn (fun i => f i.succ) (fun i => g i.succ))

theorem optAns_outAns (o : Option (List IVal)) : optAns (outAns o) = o.map .vals := by
  cases o <;> rfl

theorem map_toRound_streamTake {n : Nat} (a : ℕ → Fin n × List IVal) (out : ℕ → Option (List IVal))
    (k : ℕ) :
    (streamTake (fun i => ((((a i).1 : Nat), Payload.vals (a i).2),
        (([] : List (Call (sigN 0))), outAns (out i)))) k).map toRound =
      sessLu (streamTake a k) (streamTake out k) := by
  simp only [streamTake]
  rw [sessLu_ofFn, List.map_ofFn]
  refine congrArg List.ofFn (funext fun i => ?_)
  show (⟨_, optAns (outAns (out i))⟩ : Round sigU) = ⟨_, (out i).map .vals⟩
  rw [optAns_outAns]

/-- **Infinite typed sessions**: the infinite play of typed calls answered by terminating
outcomes is an infinite play of the session object iff every finite prefix is a reference
session behaviour. -/
theorem sessInf_iff (o : GrowOracle) (prof : ProfileKind) {c : Simple} (hc : c.Adequate)
    (a : ℕ → Fin c.exports.length × List IVal) (out : ℕ → Option (List IVal))
    (ht : ∀ k, ValTy.checkList c.exports[(a k).1].ty.params (a k).2 = true) :
    StratSession.sroundsPlay (fun k => (((a k).1 : Nat), Payload.vals (a k).2))
        (fun k => ([], outAns (out k))) ∈ (compSession (profile o) c).inf ↔
      ∀ k, refOuts (streamTake out k) ∈ sessObs (profile o) prof c (streamTake a k) := by
  obtain ⟨I, hI⟩ := hc.inst.inst
  have htc : ∀ k, TypedCalls c (streamTake a k) := fun k q hq => by
    simp only [streamTake, List.mem_ofFn] at hq
    obtain ⟨i, rfl⟩ := hq
    exact ht i
  rw [compSession_eq hI]
  constructor
  · intro hJ k
    have hm := (StratSession.threadS (compTripleS (profile o) c I) I.store).inf_sub hJ
      ⟨k, List.prefix_refl _⟩
    obtain ⟨s, hR⟩ := (StratSession.mem_srounds_of_noPlainTrap noPlainTrap_compTripleS).mp hm
    obtain ⟨hspec, -, -⟩ := spec_of_rounds hR
    rw [map_toRound_streamTake] at hspec
    have hlen : (streamTake a k).length = (streamTake out k).length := by simp [streamTake]
    obtain ⟨e₁, e₂⟩ := sessCalls_sessLu (htc k) hlen
    rw [e₁, e₂] at hspec
    exact sess_specToRef _ prof c hc hI _ _ s (htc k) hspec
  · intro h
    have hr : ∀ k, ∃ s, Rounds (compTripleS (profile o) c I) I.store
        (streamTake (fun i => ((((a i).1 : Nat), Payload.vals (a i).2),
          (([] : List (Call (sigN 0))), outAns (out i)))) k) s := by
      intro k
      obtain ⟨I'', outs, s, hI'', hspec, heq⟩ := sess_refToSpec _ prof c hc _ (htc k) (h k)
      obtain rfl := refOuts_inj heq
      obtain rfl := isInst_unique hI'' hI
      obtain ⟨hR, -, -⟩ := rounds_of_sessSpec hspec (htc k)
      rw [← map_toRound_streamTake, map_ofRound_toRound] at hR
      exact ⟨s, hR⟩
    obtain ⟨s, hs⟩ := infRounds_of_rounds (storeDet_compTripleS o) hr
    exact StratSession.InfRounds.mem_sinf hs

end Silmaril.Proofs.Wasm.Component.Reference.SessionStrat
