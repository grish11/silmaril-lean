module

public import Silmaril.Wasm.Abstract.PubView.Defs
public import Silmaril.Wasm.Abstract.PubModule.Thms
public import Silmaril.Games.Abstract.StratObs.Thms

/-!
# The public interaction of an export through a store view (proofs)

* Call prefixes of a viewed triple are the views of the call prefixes (`satP_view`): the log map
  is pointwise, so a viewed prefix of a viewed log lifts to a prefix of the log (`lift_callPre`).
* Under `HostView`, the pending calls of the view of a triple whose pending calls are its call
  prefixes left pending by the host are the viewed call prefixes left pending by some store with
  that view (`view_pending_eq`). The Core public triple has this property (`pub_pending_eq`, from
  the public `coreTriple_pending_eq`), so its view is determined by its saturation
  (`eq_of_sat_eq`).
* The view of the Core public triple, read back from Core runs (`mem_v1_ret`, `mem_v1_trap`,
  `mem_v1_div`, `mem_v2`, `mem_v3`): two views are equal iff the exports are `PubEquivV`
  (`viewTriple_eq_iff`). Two Core public triples are equal iff the exports are `PubEquiv`
  (`corePubTriple_eq_iff`), and for injective `π` the view of triples is injective
  (`viewTriple_injective`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.PubView

open Silmaril.Games Silmaril.Games.Abstract Silmaril.Wasm.Execution.Core Silmaril.Wasm.Abstract

universe u

variable {H O : Type} {π : Store H → O} {P : Silmaril.Wasm.Numerics.Profile}
  {host : HostSemantics H} {Ok : Store H → Nat × List Val → Prop}

/-! ## Viewing logs -/

theorem map_callPre {c d : List (Call (wasmHostSig H))} {m : (wasmHostSig H).Op}
    (h : StratObs.CallPre c m d) :
    StratObs.CallPre (c.map (viewCall π)) (viewOp π m) (d.map (viewCall π)) := by
  obtain ⟨n, c', rfl⟩ := h
  exact ⟨(π n.1, n.2), c'.map (viewCall π), by rw [List.map_append, List.map_cons]; rfl⟩

theorem lift_callPre {d : List (Call (wasmHostSig H))} {c : List (Call (viewSig H O))}
    {m : (viewSig H O).Op} (h : StratObs.CallPre c m (d.map (viewCall π))) :
    ∃ c₀ m₀, StratObs.CallPre c₀ m₀ d ∧ c₀.map (viewCall π) = c ∧ viewOp π m₀ = m := by
  obtain ⟨n, c', h⟩ := h
  obtain ⟨d₁, d₂, rfl, h₁, h₂⟩ := List.map_eq_append_iff.1 h
  obtain ⟨e, d₃, rfl, he, -⟩ := List.map_eq_cons_iff.1 h₂
  exact ⟨d₁, e.1, ⟨e.2, d₃, rfl⟩, h₁, congrArg Sigma.fst he⟩

theorem streamTake_view (ω : Nat → Call (wasmHostSig H)) (k : Nat) :
    streamTake (viewCall π ∘ ω) k = (streamTake ω k).map (viewCall π) := by
  unfold streamTake; rw [List.map_ofFn]; rfl

/-- **Call prefixes commute with the view.** -/
theorem satP_view (T : ObsTriple (wasmHostSig H) PUnit (List Val) ((List Val ⊕ Nat) × Store H))
    (u : PUnit) (vs : List Val) :
    StratObs.satP (viewTriple π T) u vs =
      (fun x => (x.1.map (viewCall π), viewOp π x.2)) '' StratObs.satP T u vs := by
  ext ⟨c, m⟩
  constructor
  · rintro (⟨x, hx, hxe⟩ | ⟨d, m', ⟨⟨d₀, m₀⟩, h₀, he⟩, hp⟩ | ⟨d, e, ⟨⟨d₀, e₀⟩, h₀, he⟩, hp⟩ |
      ⟨ω', ⟨ω, hω, rfl⟩, k, hk, hm⟩)
    · exact ⟨x, .inl hx, hxe⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨c₀, m₁, hp₀, rfl, rfl⟩ := lift_callPre hp
      exact ⟨(c₀, m₁), .inr (.inl ⟨d₀, m₀, h₀, hp₀⟩), rfl⟩
    · simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      obtain ⟨c₀, m₁, hp₀, rfl, rfl⟩ := lift_callPre hp
      exact ⟨(c₀, m₁), .inr (.inr (.inl ⟨d₀, e₀, h₀, hp₀⟩)), rfl⟩
    · dsimp only at hk hm
      refine ⟨(streamTake ω k, (ω k).1), .inr (.inr (.inr ⟨ω, hω, k, rfl, rfl⟩)), ?_⟩
      rw [← hk, ← hm, streamTake_view]; rfl
  · rintro ⟨⟨c₀, m₀⟩, h, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    rcases h with h | ⟨d, m', h, hp⟩ | ⟨d, e, h, hp⟩ | ⟨ω, hω, k, hk, hm⟩
    · exact .inl ⟨_, h, rfl⟩
    · exact .inr (.inl ⟨d.map (viewCall π), viewOp π m', ⟨(d, m'), h, rfl⟩, map_callPre hp⟩)
    · exact .inr (.inr (.inl ⟨d.map (viewCall π), viewEnd π e, ⟨(d, e), h, rfl⟩,
        map_callPre hp⟩))
    · dsimp only at hk hm
      refine .inr (.inr (.inr ⟨viewCall π ∘ ω, ⟨ω, hω, rfl⟩, k, ?_, ?_⟩))
      · rw [streamTake_view, hk]
      · rw [← hm]; rfl

/-! ## Pending calls through the view -/

/-- Some store with the view `m.2.1` makes the host leave the call pending. -/
def HostPendsV (π : Store H → O) (host : HostSemantics H) (m : (viewSig H O).Op) : Prop :=
  ∃ s₁, π s₁ = m.2.1 ∧ HostPends host (m.1, s₁, m.2.2)

theorem view_pending_eq (hV : HostView π host)
    {T : ObsTriple (wasmHostSig H) PUnit (List Val) ((List Val ⊕ Nat) × Store H)}
    {u : PUnit} {vs : List Val}
    (hT : T.2.1 u vs = {x | x ∈ StratObs.satP T u vs ∧ HostPends host x.2}) :
    (viewTriple π T).2.1 u vs =
      {y | y ∈ StratObs.satP (viewTriple π T) u vs ∧ HostPendsV π host y.2} := by
  rw [satP_view]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [hT] at hx
    exact ⟨⟨x, hx.1, rfl⟩, x.2.2.1, rfl, hx.2⟩
  · rintro ⟨⟨x, hx, rfl⟩, s₁, hs, hp⟩
    refine ⟨x, ?_, rfl⟩
    rw [hT]
    exact ⟨hx, (hV x.2.1 s₁ x.2.2.1 x.2.2.2 hs).1 hp⟩

theorem eq_of_sat_eq {E : Sig.{u}} {S A B : Type u} {t t' : ObsTriple E S A B}
    {R : E.Op → Prop}
    (ht : ∀ s a, t.2.1 s a = {x | x ∈ StratObs.satP t s a ∧ R x.2})
    (ht' : ∀ s a, t'.2.1 s a = {x | x ∈ StratObs.satP t' s a ∧ R x.2})
    (h : StratObs.sat t = StratObs.sat t') : t = t' := by
  have h2 : StratObs.satP t = StratObs.satP t' := congrArg (fun t => t.2.1) h
  refine Prod.ext (congrArg (fun t => t.1) h)
    (Prod.ext (funext fun s => funext fun a => ?_) (congrArg (fun t => t.2.2) h))
  rw [ht, ht', h2]

/-! ## The Core public triple -/

theorem satP_pubTriple
    {T : ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat)}
    (s : Store H) (a : Nat) (u : PUnit) (vs : List Val) :
    StratObs.satP (pubTriple T s a) u vs = StratObs.satP T s (a, vs) := by
  ext x
  constructor
  · rintro (h | h | ⟨d, e, ⟨e', h, -⟩, hp⟩ | h)
    exacts [.inl h, .inr (.inl h), .inr (.inr (.inl ⟨d, e', h, hp⟩)), .inr (.inr (.inr h))]
  · rintro (h | h | ⟨d, e, h, hp⟩ | h)
    exacts [.inl h, .inr (.inl h), .inr (.inr (.inl ⟨d, pubEnd e, ⟨e, h, rfl⟩, hp⟩)),
      .inr (.inr (.inr h))]

theorem pub_pending_eq (s : Store H) (a : Nat) (u : PUnit) (vs : List Val) :
    (pubTriple (coreTriple P host Ok) s a).2.1 u vs =
      {x | x ∈ StratObs.satP (pubTriple (coreTriple P host Ok) s a) u vs ∧ HostPends host x.2} := by
  rw [satP_pubTriple]; exact coreTriple_pending_eq s (a, vs)

theorem corePubTriple_eq_iff {s s' : Store H} {a a' : Nat} :
    pubTriple (coreTriple P host Ok) s a = pubTriple (coreTriple P host Ok) s' a' ↔
      PubEquiv P host Ok s a s' a' := by
  rw [← pubStrat_eq_iff]
  unfold pubStrat
  rw [StratObs.toDStrat_eq_iff]
  exact ⟨fun h => congrArg _ h, eq_of_sat_eq (pub_pending_eq s a) (pub_pending_eq s' a')⟩

/-! ## Injective views -/

theorem viewCall_injective (hπ : Function.Injective π) :
    Function.Injective (viewCall (H := H) π) := by
  rintro ⟨⟨hh, s₁, us⟩, s₂, r⟩ ⟨⟨hh', s₁', us'⟩, s₂', r'⟩ h
  simp only [viewCall, viewOp, Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at h
  obtain ⟨⟨rfl, h1, rfl⟩, h2, rfl⟩ := h
  rw [hπ h1, hπ h2]

theorem viewOp_injective (hπ : Function.Injective π) : Function.Injective (viewOp (H := H) π) := by
  rintro ⟨hh, s₁, us⟩ ⟨hh', s₁', us'⟩ h
  simp only [viewOp, Prod.mk.injEq] at h
  obtain ⟨rfl, h1, rfl⟩ := h
  rw [hπ h1]

theorem viewEnd_injective {B : Type} (hπ : Function.Injective π) :
    Function.Injective (viewEnd (B := B) π) := by
  rintro (⟨⟨b, s₁⟩, ⟨⟩⟩ | _ | _) (⟨⟨b', s₁'⟩, ⟨⟩⟩ | _ | _) h
  · simp only [viewEnd, End.ret.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, h₁⟩, -⟩ := h
    rw [hπ h₁]
  all_goals first | rfl | simp [viewEnd] at h

theorem viewTriple_injective (hπ : Function.Injective π) :
    Function.Injective (viewTriple (H := H) π) := by
  intro T T' h
  have h1 : (viewTriple π T).1 = (viewTriple π T').1 := congrArg Prod.fst h
  have h2 : (viewTriple π T).2.1 = (viewTriple π T').2.1 := congrArg (fun t => t.2.1) h
  have h3 : (viewTriple π T).2.2 = (viewTriple π T').2.2 := congrArg (fun t => t.2.2) h
  have hl := List.map_injective_iff.2 (viewCall_injective hπ)
  refine Prod.ext (funext fun u => funext fun vs => ?_)
    (Prod.ext (funext fun u => funext fun vs => ?_) (funext fun u => funext fun vs => ?_))
  · exact Set.image_injective.2 (fun x y hxy => Prod.ext (hl (congrArg Prod.fst hxy))
      (viewEnd_injective hπ (congrArg Prod.snd hxy))) (congrFun (congrFun h1 u) vs)
  · exact Set.image_injective.2 (fun x y hxy => Prod.ext (hl (congrArg Prod.fst hxy))
      (viewOp_injective hπ (congrArg Prod.snd hxy))) (congrFun (congrFun h2 u) vs)
  · exact Set.image_injective.2 (fun ω ω' hω => funext fun k => viewCall_injective hπ
      (congrFun hω k)) (congrFun (congrFun h3 u) vs)

/-! ## Reading back the view of the Core public triple -/

theorem mem_view1
    {T : ObsTriple (wasmHostSig H) (Store H) (Nat × List Val) (List Val ⊕ Nat)}
    {s : Store H} {a : Nat} {u : PUnit} {vs : List Val}
    {x : CallBeh (viewSig H O) PUnit ((List Val ⊕ Nat) × O)} :
    x ∈ (viewTriple π (pubTriple T s a)).1 u vs ↔
      ∃ d e, (d, e) ∈ T.1 s (a, vs) ∧ d.map (viewCall π) = x.1 ∧ viewEnd π (pubEnd e) = x.2 := by
  constructor
  · rintro ⟨⟨d, e'⟩, ⟨e, h, he⟩, rfl⟩
    dsimp only at h he
    subst he
    exact ⟨d, e, h, rfl, rfl⟩
  · rintro ⟨d, e, h, h1, h2⟩
    exact ⟨(d, pubEnd e), ⟨e, h, rfl⟩, Prod.ext h1 h2⟩

variable {s : Store H} {a : Nat} {u : PUnit} {vs : List Val} {l : List (Call (viewSig H O))}

theorem mem_v1_ret {ws : List Val} {o : O} {u' : PUnit} :
    (l, .ret ((.inl ws : List Val ⊕ Nat), o) u') ∈
        (viewTriple π (pubTriple (coreTriple P host Ok) s a)).1 u vs ↔
      Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (s₂ : Store H),
        EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ ∧ cs.map (viewCall π) = l ∧
        π s₂ = o := by
  rw [mem_view1]
  constructor
  · rintro ⟨d, e, ⟨hq, h | ⟨rfl, h⟩⟩, h1, h2⟩
    · rcases e with ⟨b | n, s₂⟩ | _ | _
      · simp only [pubEnd, viewEnd, End.ret.injEq, Prod.mk.injEq, Sum.inl.injEq] at h2
        obtain ⟨⟨rfl, rfl⟩, -⟩ := h2
        exact ⟨hq, d, s₂, h, h1, rfl⟩
      · exact (h : False).elim
      · simp [pubEnd, viewEnd] at h2
      · exact (h : False).elim
    · simp [pubEnd, viewEnd] at h2
  · rintro ⟨hq, cs, s₂, h, rfl, rfl⟩
    exact ⟨cs, .ret (.inl ws) s₂, ⟨hq, .inl h⟩, rfl, rfl⟩

theorem mem_v1_retr {n : Nat} {o : O} {u' : PUnit} :
    (l, .ret ((.inr n : List Val ⊕ Nat), o) u') ∈
        (viewTriple π (pubTriple (coreTriple P host Ok) s a)).1 u vs ↔ False := by
  rw [mem_view1, iff_false]
  rintro ⟨d, e, ⟨hq, h | ⟨rfl, h⟩⟩, h1, h2⟩
  · rcases e with ⟨b | n, s₂⟩ | _ | _
    · simp [pubEnd, viewEnd] at h2
    · exact (h : False).elim
    · simp [pubEnd, viewEnd] at h2
    · exact (h : False).elim
  · simp [pubEnd, viewEnd] at h2

theorem mem_v1_trap :
    (l, .trap) ∈ (viewTriple π (pubTriple (coreTriple P host Ok) s a)).1 u vs ↔
      Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (s₂ : Store H),
        EvRun P host (invoke s a vs) cs ⟨s₂, {}, [.trap]⟩ ∧ cs.map (viewCall π) = l := by
  rw [mem_view1]
  constructor
  · rintro ⟨d, e, ⟨hq, h | ⟨rfl, h⟩⟩, h1, h2⟩
    · rcases e with ⟨b, s₂⟩ | _ | _
      · simp [pubEnd, viewEnd] at h2
      · obtain ⟨s₂, h⟩ := h
        exact ⟨hq, d, s₂, h, h1⟩
      · exact (h : False).elim
    · simp [pubEnd, viewEnd] at h2
  · rintro ⟨hq, cs, s₂, h, rfl⟩
    exact ⟨cs, .trap, ⟨hq, .inl ⟨s₂, h⟩⟩, rfl, rfl⟩

theorem mem_v1_div :
    (l, .div) ∈ (viewTriple π (pubTriple (coreTriple P host Ok) s a)).1 u vs ↔
      Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (c : Config H),
        EvRun P host (invoke s a vs) cs c ∧ Diverges P (fun _ _ _ _ => False) c ∧
        cs.map (viewCall π) = l := by
  rw [mem_view1]
  constructor
  · rintro ⟨d, e, ⟨hq, h | ⟨rfl, c, h, hd⟩⟩, h1, h2⟩
    · rcases e with ⟨b, s₂⟩ | _ | _
      · simp [pubEnd, viewEnd] at h2
      · simp [pubEnd, viewEnd] at h2
      · exact (h : False).elim
    · exact ⟨hq, d, c, h, hd, h1⟩
  · rintro ⟨hq, cs, c, h, hd, rfl⟩
    exact ⟨cs, .div, ⟨hq, .inr ⟨rfl, c, h, hd⟩⟩, rfl, rfl⟩

theorem mem_v2 {hh : H} {o : O} {us : List Val} :
    (l, (hh, o, us)) ∈ (viewTriple π (pubTriple (coreTriple P host Ok) s a)).2.1 u vs ↔
      Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (c : Config H)
        (E : Silmaril.Wasm.SingleThreaded.Ctx) (b : Nat),
        EvRun P host (invoke s a vs) cs c ∧
        Silmaril.Wasm.SingleThreaded.decompose? c.store c.code = some (E, b, hh, us) ∧
        cs.map (viewCall π) = l ∧ π c.store = o ∧ HostPends host (hh, c.store, us) := by
  constructor
  · rintro ⟨⟨cs, hh', s₁, us'⟩, ⟨hq, ⟨c, E, b, hr, hd, hs, hn⟩ | ⟨c, E, b, hr, hd, hs, hn⟩⟩, he⟩
    · simp only [viewOp, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      subst hs
      exact ⟨hq, cs, c, E, b, hr, hd, rfl, rfl, .inl hn⟩
    · simp only [viewOp, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      subst hs
      exact ⟨hq, cs, c, E, b, hr, hd, rfl, rfl, .inr hn⟩
  · rintro ⟨hq, cs, c, E, b, hr, hd, rfl, rfl, hp | hp⟩
    · exact ⟨(cs, hh, c.store, us), ⟨hq, .inl ⟨c, E, b, hr, hd, rfl, hp⟩⟩, rfl⟩
    · exact ⟨(cs, hh, c.store, us), ⟨hq, .inr ⟨c, E, b, hr, hd, rfl, hp⟩⟩, rfl⟩

theorem mem_v3 {ω' : Nat → Call (viewSig H O)} :
    ω' ∈ (viewTriple π (pubTriple (coreTriple P host Ok) s a)).2.2 u vs ↔
      Ok s (a, vs) ∧ ∃ ω : Nat → Call (wasmHostSig H),
        CoreInf P host (invoke s a vs) ω ∧ viewCall π ∘ ω = ω' :=
  ⟨fun ⟨ω, ⟨hq, h⟩, he⟩ => ⟨hq, ω, h, he⟩, fun ⟨hq, ω, h, he⟩ => ⟨ω, ⟨hq, h⟩, he⟩⟩

/-! ## The view triple and `PubEquivV` -/

theorem viewTriple_eq_iff {s' : Store H} {a' : Nat} :
    viewTriple π (pubTriple (coreTriple P host Ok) s a) =
        viewTriple π (pubTriple (coreTriple P host Ok) s' a') ↔
      PubEquivV π P host Ok s a s' a' := by
  constructor
  · intro h vs
    have h1 : ∀ x, x ∈ (viewTriple π (pubTriple (coreTriple P host Ok) s a)).1 PUnit.unit vs ↔
        x ∈ (viewTriple π (pubTriple (coreTriple P host Ok) s' a')).1 PUnit.unit vs :=
      fun x => by rw [h]
    have h2 : ∀ x, x ∈ (viewTriple π (pubTriple (coreTriple P host Ok) s a)).2.1 PUnit.unit vs ↔
        x ∈ (viewTriple π (pubTriple (coreTriple P host Ok) s' a')).2.1 PUnit.unit vs :=
      fun x => by rw [h]
    have h3 : ∀ x, x ∈ (viewTriple π (pubTriple (coreTriple P host Ok) s a)).2.2 PUnit.unit vs ↔
        x ∈ (viewTriple π (pubTriple (coreTriple P host Ok) s' a')).2.2 PUnit.unit vs :=
      fun x => by rw [h]
    refine ⟨fun l ws o => ?_, fun l => ?_, fun l hh o us => ?_, fun l => ?_, fun ω' => ?_⟩
    · exact mem_v1_ret.symm.trans ((h1 (l, .ret (.inl ws, o) PUnit.unit)).trans mem_v1_ret)
    · exact mem_v1_trap.symm.trans ((h1 (l, .trap)).trans mem_v1_trap)
    · exact mem_v2.symm.trans ((h2 (l, hh, o, us)).trans mem_v2)
    · exact mem_v1_div.symm.trans ((h1 (l, .div)).trans mem_v1_div)
    · exact mem_v3.symm.trans ((h3 ω').trans mem_v3)
  · intro h
    refine Prod.ext (funext fun u => funext fun vs => Set.ext fun x => ?_)
      (Prod.ext (funext fun u => funext fun vs => Set.ext fun x => ?_)
        (funext fun u => funext fun vs => Set.ext fun ω' => ?_))
    · obtain ⟨h1, h2, -, h4, -⟩ := h vs
      rcases x with ⟨l, ⟨⟨b | n, o⟩, u'⟩ | _ | _⟩
      · exact mem_v1_ret.trans ((h1 l b o).trans mem_v1_ret.symm)
      · exact mem_v1_retr.trans mem_v1_retr.symm
      · exact mem_v1_trap.trans ((h2 l).trans mem_v1_trap.symm)
      · exact mem_v1_div.trans ((h4 l).trans mem_v1_div.symm)
    · obtain ⟨-, -, h3, -, -⟩ := h vs
      rcases x with ⟨l, hh, o, us⟩
      exact mem_v2.trans ((h3 l hh o us).trans mem_v2.symm)
    · obtain ⟨-, -, -, -, h5⟩ := h vs
      exact mem_v3.trans ((h5 ω').trans mem_v3.symm)

/-! ## The view strategy -/

/-- **The view injection.** -/
theorem viewStrat_eq_iff (hV : HostView π host) {s' : Store H} {a' : Nat} :
    viewStrat π P host Ok s a = viewStrat π P host Ok s' a' ↔ PubEquivV π P host Ok s a s' a' := by
  unfold viewStrat
  rw [StratObs.toDStrat_eq_iff, ← viewTriple_eq_iff]
  exact ⟨eq_of_sat_eq (R := HostPendsV π host)
      (fun _ _ => view_pending_eq hV (pub_pending_eq s a _ _))
      (fun _ _ => view_pending_eq hV (pub_pending_eq s' a' _ _)),
    fun h => congrArg _ h⟩

theorem pubEquivV_of_pubEquiv {s' : Store H} {a' : Nat} (h : PubEquiv P host Ok s a s' a') :
    PubEquivV π P host Ok s a s' a' :=
  viewTriple_eq_iff.1 (congrArg (viewTriple π) (corePubTriple_eq_iff.2 h))

theorem pubStrat_eq_viewStrat_eq {s' : Store H} {a' : Nat}
    (h : pubStrat P host Ok s a = pubStrat P host Ok s' a') :
    viewStrat π P host Ok s a = viewStrat π P host Ok s' a' :=
  congrArg (fun T => StratObs.toDStrat (viewTriple π T))
    (corePubTriple_eq_iff.2 (pubStrat_eq_iff.1 h))

theorem pubEquivV_iff_of_injective (hπ : Function.Injective π) {s' : Store H} {a' : Nat} :
    PubEquivV π P host Ok s a s' a' ↔ PubEquiv P host Ok s a s' a' := by
  rw [← viewTriple_eq_iff, ← corePubTriple_eq_iff]
  exact (viewTriple_injective hπ).eq_iff

theorem viewStrat_mem_ret (vs : List Val) (l : List (Call (viewSig H O))) (ws : List Val)
    (o : O) :
    (.inr (.ask (PUnit.unit, vs)) :: (StratObs.callMoves l ++
        [.inr (.ans (PUnit.unit, vs) (.inl (((.inl ws : List Val ⊕ Nat), o), PUnit.unit)))]) :
        List (Move (viewSig H O) (viewSigPub O))) ∈ (viewStrat π P host Ok s a).toStrategy ↔
      Ok s (a, vs) ∧ ∃ (cs : List (Call (wasmHostSig H))) (s₂ : Store H),
        EvRun P host (invoke s a vs) cs ⟨s₂, {}, vals ws⟩ ∧ cs.map (viewCall π) = l ∧
        π s₂ = o :=
  (StratObs.mem_ret _ vs l _ _).trans mem_v1_ret

theorem viewStrat_mem_inf (vs : List Val) (ω' : Nat → Call (viewSig H O)) :
    StratObs.streamPlay [] (PUnit.unit, vs) ω' ∈ (viewStrat π P host Ok s a).inf ↔
      Ok s (a, vs) ∧ ∃ ω : Nat → Call (wasmHostSig H),
        CoreInf P host (invoke s a vs) ω ∧ viewCall π ∘ ω = ω' :=
  (StratObs.mem_inf (PUnit.unit, vs) ω').trans mem_v3

end Silmaril.Proofs.Wasm.Abstract.PubView
