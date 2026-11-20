module

public import Silmaril.Proofs.Wasm.Component.InstSem.Run
public import Silmaril.Proofs.Wasm.Component.InstSem.Plays

/-!
# The component IR with an instantiation phase: export rounds

Plays of the export phase, assembled from rounds:

* `zip_rounds`, `comp_rounds`: rounds of an upper strategy whose calls are served by rounds of
  the lower one are rounds of the composite (`comp_handler_round` for several rounds);
* `extI_inst_right`: **the new instance answers export calls after instantiation**: if the
  environment `D` is instantiated (serving the new instance's instantiation calls) and the new
  instance `N` then answers export calls `ys` without calls below, the extension does, at the
  shifted positions;
* `liftH_exportsH_fwd_runs`: an export forwarded (`Impl.fwd r`) on top;
* `instProper_rounds`: an instantiation round followed by export rounds follows the protocol.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component

variable {X E F G : Sig.{0}}

/-- **Rounds served by rounds below.** Each upper round `u.2` makes the calls of the lower
rounds `u.1`. -/
theorem zip_rounds : ∀ us : List (List (Round E F) × Round F G),
    (∀ u ∈ us, u.2.cs = u.1.map Round.call) →
    Zip (roundsMoves (us.flatMap Prod.fst)) (roundsMoves (us.map Prod.snd))
      (roundsMoves (us.map fun u => (⟨u.2.q, allCalls u.1, u.2.a⟩ : Round E G)))
  | [], _ => .nil
  | ⟨xs, ⟨g, cs, a⟩⟩ :: us, h => by
    have hc : cs = xs.map Round.call := h _ (.head _)
    subst hc
    have := zip_round (zip_rounds us fun u hu => h u (.tail _ hu)) xs g a
    simpa only [List.flatMap_cons, List.map_cons, roundsMoves, roundsMoves_append] using this

theorem comp_rounds {σ : Strategy E F} {τ : Strategy F G}
    (us : List (List (Round E F) × Round F G)) (hus : ∀ u ∈ us, u.2.cs = u.1.map Round.call)
    (hσ : roundsMoves (us.flatMap Prod.fst) ∈ σ) (hτ : roundsMoves (us.map Prod.snd) ∈ τ) :
    roundsMoves (us.map fun u => (⟨u.2.q, allCalls u.1, u.2.a⟩ : Round E G)) ∈ σ.comp τ :=
  ⟨_, hσ, _, hτ, zip_rounds us hus⟩

/-- An export round of the new instance, at the shifted position `k + e`. -/
def shiftRound (e : Nat) (y : Round sigU sigU) : Round X sigU := ⟨(y.q.1 + e, y.q.2), [], y.a⟩

theorem instSplitH_runs_right (e : Nat) (q : sigU.Op) (n : Option Payload) :
    Prog.Runs (instSplitH e (some (q.1 + e, q.2))) [⟨.inr (some q), n⟩] n := by
  obtain ⟨k, pl⟩ := q
  have h : ¬ k + e < e := by omega
  simp only [instSplitH, h, ↓reduceIte]
  rw [show k + e - e = k by omega]
  exact .call (.pure _)

theorem flatMap_single {α β : Type} (f : α → β) : ∀ l : List α,
    l.flatMap (fun x => [f x]) = l.map f
  | [] => rfl
  | x :: l => by simp only [List.flatMap_cons, List.map_cons, List.singleton_append,
      flatMap_single f l]

theorem lefts_map_inr {Y F₁ F₂ : Sig.{0}} {α : Type} (f : α → Round Y F₂) : ∀ l : List α,
    lefts (F₁ := F₁) (l.map fun y => .inr (f y)) = []
  | [] => rfl
  | _ :: l => lefts_map_inr f l

theorem rights_map_inr {Y F₁ F₂ : Sig.{0}} {α : Type} (f : α → Round Y F₂) : ∀ l : List α,
    rights (F₁ := F₁) (l.map fun y => .inr (f y)) = l.map f
  | [] => rfl
  | y :: l => congrArg (f y :: ·) (rights_map_inr f l)

theorem flatMap_empty {α β : Type} : ∀ l : List α, l.flatMap (fun _ => ([] : List β)) = []
  | [] => rfl
  | _ :: l => by simp only [List.flatMap_cons, List.nil_append, flatMap_empty l]

/-- **The new instance answers export calls after instantiation.** -/
theorem extI_inst_right {e : Nat} {D : Strategy X sigUI} {N : Strategy sigU sigUI}
    (w : List (Call X)) (xs : List (Round X sigU)) (ys : List (Round sigU sigU))
    (hys : ∀ y ∈ ys, y.cs = [])
    (hD : roundsMoves (instRound w .ready :: xs.map exRound) ∈ D)
    (hN : roundsMoves (instRound (F := sigU) (xs.map Round.call) .ready ::
      ys.map (exRound (R := Unit))) ∈ N) :
    roundsMoves (instRound (w ++ allCalls xs) .ready ::
      (ys.map (shiftRound (X := X) e)).map (exRound (R := Unit))) ∈ extI e D N := by
  -- the new instance seen from its environment: export calls of `exH`
  have hN' : roundsMoves ((⟨none, (xs.map (exRound (R := Unit))).map Round.call, .ready⟩ :
      Round sigUI sigUI) :: ys.map fun y => ⟨some y.q, [], y.a⟩) ∈
      (Strategy.ofHandler (exH sigU Unit)).comp N := by
    let us : List (List (Round sigUI sigU) × Round sigU sigUI) :=
      (xs.map fun x => (⟨x.q, [⟨some x.q, x.a⟩], x.a⟩ : Round sigUI sigU),
        instRound (xs.map Round.call) .ready) :: ys.map fun y => ([], exRound y)
    have hc := comp_rounds (σ := Strategy.ofHandler (exH sigU Unit)) (τ := N) us
      (by
        intro u hu
        simp only [us, List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨y, hy, rfl⟩
        · simp only [List.map_map]; rfl
        · simp only [exRound, hys y hy, List.map_nil])
      (by
        refine mem_ofHandler_rounds _ fun r hr => ?_
        obtain ⟨u, hu, hr⟩ := List.mem_flatMap.1 hr
        simp only [us, List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨y, -, rfl⟩
        · simp only [List.mem_map] at hr
          obtain ⟨x, -, rfl⟩ := hr
          exact .call (.pure _)
        · cases hr)
      (by simpa only [us, List.map_cons, List.map_map, Function.comp_def] using hN)
    have hall : allCalls (xs.map fun x => (⟨x.q, [⟨some x.q, x.a⟩], x.a⟩ : Round sigUI sigU)) =
        (xs.map (exRound (R := Unit))).map Round.call := by
      clear hD hN hc
      induction xs with
      | nil => rfl
      | cons x xs ih => simp only [List.map_cons, allCalls, ih]; rfl
    simpa only [us, List.map_cons, List.map_map, Function.comp_def, hall, allCalls, exRound]
      using hc
  -- the routing layer
  let tI : Round sigUI sigUI :=
    ⟨none, ⟨none, InstAns.ready⟩ :: (xs.map (exRound (R := Unit))).map Round.call, .ready⟩
  have hT : roundsMoves (tI :: ys.map fun y => (⟨some (y.q.1 + e, y.q.2), [], y.a⟩ :
      Round sigUI sigUI)) ∈
      ((Strategy.id sigUI).pair ((Strategy.ofHandler (exH sigU Unit)).comp N)).comp
        (Strategy.ofHandler (instSplitH e)) := by
    let us : List (List (Round sigUI (sigUI ⊕ₛ sigUI)) × Round (sigUI ⊕ₛ sigUI) sigUI) :=
      ([sided (.inl ⟨none, [⟨none, InstAns.ready⟩], InstAns.ready⟩),
          sided (.inr ⟨none, (xs.map (exRound (R := Unit))).map Round.call, .ready⟩)],
        ⟨none, [⟨.inl none, InstAns.ready⟩, ⟨.inr none, InstAns.ready⟩], .ready⟩) ::
      ys.map fun y => ([sided (.inr ⟨some y.q, [], y.a⟩)],
        ⟨some (y.q.1 + e, y.q.2), [⟨.inr (some y.q), y.a⟩], y.a⟩)
    have hc := comp_rounds
      (σ := (Strategy.id sigUI).pair ((Strategy.ofHandler (exH sigU Unit)).comp N))
      (τ := Strategy.ofHandler (instSplitH e)) us
      (by
        intro u hu
        simp only [us, List.mem_cons, List.mem_map] at hu
        rcases hu with rfl | ⟨y, -, rfl⟩ <;> rfl)
      (by
        let vs : List (Round sigUI sigUI ⊕ Round sigUI sigUI) :=
          .inl ⟨none, [⟨none, InstAns.ready⟩], InstAns.ready⟩ ::
            .inr ⟨none, (xs.map (exRound (R := Unit))).map Round.call, .ready⟩ ::
            ys.map fun y => .inr ⟨some y.q, [], y.a⟩
        have hv : us.flatMap Prod.fst = vs.map sided := by
          simp only [us, vs, List.flatMap_cons, List.flatMap_map, List.map_cons,
            List.cons_append, List.nil_append, List.map_map, Function.comp_def]
          rw [flatMap_single (fun y : Round sigU sigU =>
            sided (F₁ := sigUI) (.inr (⟨some y.q, [], y.a⟩ : Round sigUI sigUI)))]
        rw [hv]
        refine mem_pair_rounds vs ?_ ?_
        · have hl : lefts vs = [⟨none, [⟨none, InstAns.ready⟩], InstAns.ready⟩] := by
            simp only [vs, lefts]
            rw [lefts_map_inr]
          rw [hl]
          exact mem_id_rounds _ fun r hr => by
            rw [List.mem_singleton] at hr
            subst hr
            rfl
        · have hr : rights vs = ⟨none, (xs.map (exRound (R := Unit))).map Round.call, .ready⟩ ::
              ys.map fun y => ⟨some y.q, [], y.a⟩ := by
            simp only [vs, rights]
            rw [rights_map_inr]
          rw [hr]
          exact hN')
      (by
        refine mem_ofHandler_rounds _ fun r hr => ?_
        simp only [us, List.map_cons, List.map_map, List.mem_cons, List.mem_map,
          Function.comp_def] at hr
        rcases hr with rfl | ⟨y, -, rfl⟩
        · exact instSplitH_runs e .ready
        · exact instSplitH_runs_right e y.q y.a)
    simpa only [us, List.map_cons, List.map_map, Function.comp_def, allCalls, sided, Round.inl,
      Round.inr, List.append_nil, List.singleton_append, List.cons_append, List.nil_append, tI]
      using hc
  -- the environment below
  let us : List (List (Round X sigUI) × Round sigUI sigUI) :=
    (instRound w .ready :: xs.map exRound, tI) ::
      ys.map fun y => ([], ⟨some (y.q.1 + e, y.q.2), [], y.a⟩)
  have hc := comp_rounds (σ := D) us
    (by
      intro u hu
      simp only [us, List.mem_cons, List.mem_map] at hu
      rcases hu with rfl | ⟨y, -, rfl⟩
      · simp only [tI, List.map_cons, List.map_map]; rfl
      · rfl)
    (by
      have : us.flatMap Prod.fst = instRound w .ready :: xs.map exRound := by
        simp only [us, List.flatMap_cons, List.flatMap_map]
        rw [flatMap_empty, List.append_nil]
      rw [this]
      exact hD)
    (by simpa only [us, List.map_cons, List.map_map, Function.comp_def] using hT)
  simpa only [us, tI, extI, List.map_cons, List.map_map, Function.comp_def, allCalls,
    allCalls_map_exRound, shiftRound, exRound, instRound, List.append_nil] using hc

/-- **An export forwarded on top**: `liftH (exportsH e xs)` answers export `j`, implemented by
`Impl.fwd r` with `r < e`, by calling export `r` of the environment. -/
theorem liftH_exportsH_fwd_runs {e r : Nat} {xs : List Export} {j : Nat} {pl : Payload}
    (hx : (xs.map Export.impl)[j]? = some (Impl.fwd r)) (hr : r < e) (n : Option Payload) :
    Prog.Runs (liftH (R := Unit) (exportsH e xs) (some (j, pl))) [⟨some (r, pl), n⟩] n := by
  simp only [liftH, exportsH, implsH, hx, Impl.prog, Impl.fwd, runChain, Target.prog, hr,
    ↓reduceIte, Prog.interp]
  exact .call (.pure _)

theorem upper_roundsMoves_ex {Y : Sig.{0}} {R : Type} :
    ∀ rs : List (Round Y F), ∀ x ∈ upper (roundsMoves (rs.map (exRound (R := R)))), IsExEv x
  | [], _, h => by simp [roundsMoves, upper] at h
  | r :: rs, x, h => by
    simp only [List.map_cons, roundsMoves, exRound, Round.moves, upper, List.cons_append,
      List.filterMap_cons, Sum.getRight?_inr, List.filterMap_append, List.mem_cons,
      List.mem_append] at h
    rcases h with rfl | (h | h) | h
    · rfl
    · rw [List.filterMap_map] at h
      simp [Function.comp_def, Sum.getRight?] at h
    · rcases h with rfl | h
      · rfl
      · cases h
    · exact upper_roundsMoves_ex rs x h

/-- **An instantiation round followed by export rounds follows the protocol.** -/
theorem instProper_rounds {Y : Sig.{0}} (cs : List (Call Y)) (rs : List (Round Y F)) :
    InstProper (roundsMoves (instRound (F := F) (R := Unit) cs .ready :: rs.map exRound)) := by
  refine .inr (.inr (.inr ⟨upper (roundsMoves (rs.map (exRound (R := Unit)))), ?_,
    upper_roundsMoves_ex rs⟩))
  simp only [roundsMoves, instRound, Round.moves, upper, List.cons_append, List.filterMap_cons,
    Sum.getRight?_inr, List.filterMap_append, List.append_assoc]
  have : ∀ l : List (Ev Y),
      List.filterMap Sum.getRight? (l.map (Sum.inl (β := Ev (F.withInst Unit)))) = [] := by
    intro l; induction l with
    | nil => rfl
    | cons x l ih => exact ih
  rw [this]
  rfl

variable {M : Type} [CoreModule M]

/-- **An export phase of the nodes, through the component's exports**: an instantiation round
followed by one export round of the environment's function `r` (question `pl'`, answer `a`, no
calls below), which the component's export `j` runs (`hrun`: called on `pl`, it calls `r` on
`pl'` and answers `a'`), is a play of the component. -/
theorem denI_of_denNodesI_ex (C : CoreSemI M) (I : Iface) (ns : List (Node M))
    (xs : List Export) (cs : List (Call sigU)) {j r : Nat} {pl pl' : Payload}
    {a a' : Option Payload}
    (hrun : Prog.Runs (liftH (R := Unit) (exportsH (envAfter I.length ns) xs) (some (j, pl)))
      [⟨some (r, pl'), a⟩] a')
    (h : roundsMoves [instRound (F := sigU) cs .ready,
      exRound (R := Unit) (⟨(r, pl'), [], a⟩ : Round sigU sigU)] ∈
      denNodesI C I.length ns (withReady (Strategy.ofHandler (maskH I.length)))) :
    roundsMoves [instRound (F := sigU) cs .ready,
      exRound (R := Unit) (⟨(j, pl), [], a'⟩ : Round sigU sigU)] ∈ (Comp.mk I ns xs).denI C := by
  rw [Comp.denI, Comp.denIR]
  refine (mem_instGuard_iff ?_).2 ?_
  · exact instProper_rounds cs [(⟨(j, pl), [], a'⟩ : Round sigU sigU)]
  let us : List (List (Round sigU sigUI) × Round sigUI sigUI) :=
    [([instRound cs .ready], ⟨none, [⟨none, InstAns.ready⟩], InstAns.ready⟩),
      ([exRound (⟨(r, pl'), [], a⟩ : Round sigU sigU)], ⟨some (j, pl), [⟨some (r, pl'), a⟩], a'⟩)]
  have hc := comp_rounds
    (σ := denNodesI C I.length ns (withReady (Strategy.ofHandler (maskH I.length))))
    (τ := Strategy.ofHandler (liftH (exportsH (envAfter I.length ns) xs))) us (by
      intro u hu
      simp only [us, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl <;> rfl)
    (by simpa only [us, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.singleton_append] using h)
    (by
      refine mem_ofHandler_rounds _ fun u hu => ?_
      simp only [us, List.map_cons, List.map_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact .call (.pure _)
      · exact hrun)
  simpa only [us, List.map_cons, List.map_nil, allCalls, instRound, exRound,
    List.append_nil] using hc

/-- **An export phase of the nodes, forwarded to the component's exports** (`Impl.fwd r`). -/
theorem denI_of_denNodesI_fwd (C : CoreSemI M) (I : Iface) (ns : List (Node M))
    (xs : List Export) (cs : List (Call sigU)) {j r : Nat} {pl : Payload} (a : Option Payload)
    (hx : (xs.map Export.impl)[j]? = some (Impl.fwd r)) (hr : r < envAfter I.length ns)
    (h : roundsMoves [instRound (F := sigU) cs .ready,
      exRound (R := Unit) (⟨(r, pl), [], a⟩ : Round sigU sigU)] ∈
      denNodesI C I.length ns (withReady (Strategy.ofHandler (maskH I.length)))) :
    roundsMoves [instRound (F := sigU) cs .ready,
      exRound (R := Unit) (⟨(j, pl), [], a⟩ : Round sigU sigU)] ∈ (Comp.mk I ns xs).denI C :=
  denI_of_denNodesI_ex C I ns xs cs (liftH_exportsH_fwd_runs hx hr a) h

end Silmaril.Proofs.Wasm.Component.InstSem
