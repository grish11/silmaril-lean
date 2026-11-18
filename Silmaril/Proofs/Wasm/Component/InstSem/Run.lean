module

public import Silmaril.Proofs.Wasm.Component.InstSem.Plays
public import Silmaril.Proofs.Wasm.Component.InstSem.Rounds

/-!
# Instantiation runs through the component combinators

Instantiation runs are rounds of the question `inst` (`instRound`); the export calls served by an
instantiated environment are rounds of export questions (`exRound`). This file carries them
through each layer of `Comp.denI`:

* `comp_handler_round`: a round of a strategy whose calls are served by a handler below;
* `comp_liftH_inst`: an instantiation round through a wiring handler on top (`liftH`);
* `extI_inst`: **instantiation in order**: the environment's instantiation round, then the
  export calls it serves for the new instance's instantiation, then (in the environment) export
  calls of later instances; `extI_fail`: a failed environment fails the extension, and the new
  instance is not asked;
* `withReady_maskH_rounds`: the imports are ready at once and forward their calls;
* `coreNodeI_inst`: a core node's instantiation round, its import calls wired by `implsN`;
* `denI_of_denNodesI`: an instantiation round of the nodes is one of the component, under the
  protocol guard.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component

variable {X E F G : Sig.{0}} {R : Type}

/-- The instantiation round with calls `cs` and answer `a`. -/
abbrev instRound (cs : List (Call X)) (a : InstAns R) : Round X (F.withInst R) := ⟨none, cs, a⟩

/-- A round of an export call, at the instantiable interface. -/
def exRound (r : Round X F) : Round X (F.withInst R) := ⟨some r.q, r.cs, r.a⟩

theorem flatMap_calls {G : Sig.{0}} : ∀ cs : List (Call X),
    (cs.flatMap fun c => [.inl (.ask c.1), .inl (.ans c.1 c.2)] : List (Move X G)) =
      (callEvs cs).map .inl
  | [] => rfl
  | ⟨m, n⟩ :: cs => by
    simp only [List.flatMap_cons, callEvs, List.map_cons, flatMap_calls cs]
    rfl

theorem instPlay_eq (cs : List (Call X)) (a : InstAns R) :
    instPlay (F := F) cs a = (instRound (F := F) cs a).moves := by
  simp only [instPlay, flatMap_calls]
  rfl

theorem allCalls_map_exRound : ∀ xs : List (Round X F),
    allCalls (xs.map (exRound (R := R))) = allCalls xs
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, allCalls, exRound, allCalls_map_exRound xs]

/-! ## Handlers -/

/-- **A round whose calls are served by a handler below.** -/
theorem comp_handler_round {g : Handler E F} {σ : Strategy F G} {q : G.Op} {a : G.Ar q}
    (xs : List (Round E F)) (hσ : Round.moves ⟨q, xs.map Round.call, a⟩ ∈ σ)
    (hx : ∀ x ∈ xs, Prog.Runs (g x.q) x.cs x.a) :
    Round.moves ⟨q, allCalls xs, a⟩ ∈ (Strategy.ofHandler g).comp σ := by
  exact ⟨_, mem_ofHandler_rounds xs hx, _, hσ, zip_round₀ xs q a⟩

/-- **An instantiation round through a wiring handler on top**: `inst` is forwarded. -/
theorem comp_liftH_inst {σ : Strategy X (E.withInst R)} (h : Handler E F)
    {cs : List (Call X)} {a : InstAns R} (hσ : (instRound (F := E) cs a).moves ∈ σ) :
    (instRound (F := F) cs a).moves ∈ σ.comp (Strategy.ofHandler (liftH h)) := by
  refine ⟨roundsMoves [instRound (F := E) cs a] ++ [], ?_, Round.moves ⟨none, [⟨none, a⟩], a⟩ ++ [],
    ?_, ?_⟩
  · simpa only [roundsMoves, List.append_nil] using hσ
  · rw [List.append_nil]
    have := mem_ofHandler_rounds (h := liftH (R := R) h)
      [(⟨none, [⟨none, a⟩], a⟩ : Round (E.withInst R) (F.withInst R))]
      (by
        intro r hr
        rw [List.mem_singleton] at hr
        subst hr
        exact .call (.pure _))
    simpa only [roundsMoves, List.append_nil] using this
  · have := zip_round (Zip.nil (α := Ev X) (β := Ev (E.withInst R)) (γ := Ev (F.withInst R)))
      [instRound (F := E) cs a] (none : (F.withInst R).Op) a
    simpa only [allCalls, List.append_nil, List.map_cons, List.map_nil, Round.call] using this

/-! ## Copycat -/

/-- Forwarding rounds are plays of copycat. -/
theorem mem_id_rounds (rs : List (Round E E)) (hr : ∀ r ∈ rs, r.cs = [⟨r.q, r.a⟩]) :
    roundsMoves rs ∈ Strategy.id E := by
  rw [← Strategy.ofHandler_id]
  refine mem_ofHandler_rounds rs fun r h => ?_
  rw [hr r h]
  exact .call (.pure _)

/-! ## Extension of an instantiable environment -/

/-- The round of copycat forwarding an export call. -/
def fwdRound {Y : Sig.{0}} (r : Round Y F) : Round (F.withInst R) (F.withInst R) :=
  ⟨some r.q, [⟨some r.q, r.a⟩], r.a⟩

theorem instSplitH_runs (e : Nat) (a : InstAns Unit) :
    Prog.Runs (instSplitH e none) [⟨.inl none, InstAns.ready⟩, ⟨.inr none, a⟩] a :=
  .call (.call (.pure _))

theorem instSplitH_runs_fail (e : Nat) (r : Unit) :
    Prog.Runs (instSplitH e none) [⟨.inl none, InstAns.fail r⟩] (InstAns.fail r) :=
  .call (.pure _)

theorem instSplitH_runs_left {e : Nat} {q : sigU.Op} (hq : q.1 < e) (n : Option Payload) :
    Prog.Runs (instSplitH e (some q)) [⟨.inl (some q), n⟩] n := by
  simp only [instSplitH, hq, ↓reduceIte]
  exact .call (.pure _)

/-- The rounds of the routing layer of `extI`, for the forwarded export calls `zs`. -/
theorem zip_fwd_rounds : ∀ zs : List (Round X sigU),
    Zip (roundsMoves (zs.map (exRound (R := Unit)))) (roundsMoves (zs.map fwdRound))
      (roundsMoves (zs.map (exRound (R := Unit))))
  | [] => .nil
  | z :: zs => by
    have h := zip_round (zip_fwd_rounds zs) [exRound (R := Unit) z] (some z.q) z.a
    simpa only [List.map_cons, roundsMoves, allCalls, exRound, fwdRound, List.append_nil,
      List.map_nil, Round.call] using h

theorem zip_split_rounds {e : Nat} : ∀ zs : List (Round X sigU), (∀ z ∈ zs, z.q.1 < e) →
    Zip (roundsMoves ((zs.map fun z => .inl (fwdRound (R := Unit) z)).map
        (sided (F₂ := sigUI)))) (roundsMoves (zs.map fun z =>
          (⟨some z.q, [⟨.inl (some z.q), z.a⟩], z.a⟩ : Round (sigUI ⊕ₛ sigUI) sigUI)))
      (roundsMoves (zs.map fwdRound))
  | [], _ => .nil
  | z :: zs, hz => by
    have h := zip_round (zip_split_rounds zs fun z' h' => hz z' (.tail _ h'))
      [sided (F₂ := sigUI) (.inl (fwdRound (R := Unit) z))] (some z.q) z.a
    simpa only [List.map_cons, roundsMoves, allCalls, sided, Round.inl, fwdRound,
      List.append_nil, List.map_nil, Round.call] using h

/-- **Instantiation in order.** If the environment `D` is instantiated by the calls `w`, then
serves the export calls `xs` (the new instance's import calls during its instantiation) and
`zs` (later calls of its own functions), and the new instance `N` instantiates with the calls
`xs` and the answer `a`, then the extension is instantiated by the calls `w` followed by those
of `xs`, answers `a`, and serves `zs`. -/
theorem extI_inst {e : Nat} {D : Strategy X sigUI} {N : Strategy sigU sigUI}
    (w : List (Call X)) (xs zs : List (Round X sigU)) (a : InstAns Unit)
    (hD : roundsMoves (instRound w .ready :: (xs ++ zs).map exRound) ∈ D)
    (hN : (instRound (F := sigU) (xs.map Round.call) a).moves ∈ N)
    (hz : ∀ z ∈ zs, z.q.1 < e) :
    roundsMoves (instRound (w ++ allCalls xs) a :: zs.map exRound) ∈ extI e D N := by
  -- the routing layer `T`
  let tI : Round sigUI sigUI :=
    ⟨none, ⟨none, InstAns.ready⟩ :: (xs.map (exRound (R := Unit))).map Round.call, a⟩
  let us : List (Round sigUI sigUI ⊕ Round sigUI sigUI) :=
    [.inl ⟨none, [⟨none, InstAns.ready⟩], InstAns.ready⟩,
      .inr ⟨none, (xs.map (exRound (R := Unit))).map Round.call, a⟩] ++
      (zs.map fwdRound).map Sum.inl
  have hT : roundsMoves (tI :: zs.map fwdRound) ∈
      ((Strategy.id sigUI).pair ((Strategy.ofHandler (exH sigU Unit)).comp N)).comp
        (Strategy.ofHandler (instSplitH e)) := by
    refine ⟨roundsMoves (us.map sided), ?_, roundsMoves
      ((⟨none, [⟨.inl none, InstAns.ready⟩, ⟨.inr none, a⟩], a⟩ : Round (sigUI ⊕ₛ sigUI) sigUI) ::
        zs.map fun z => ⟨some z.q, [⟨.inl (some z.q), z.a⟩], z.a⟩), ?_, ?_⟩
    · refine mem_pair_rounds us ?_ ?_
      · simp only [us, List.cons_append, List.nil_append, lefts, lefts_map_inl]
        refine mem_id_rounds _ fun r hr => ?_
        simp only [List.mem_cons, List.mem_map] at hr
        rcases hr with rfl | ⟨z, -, rfl⟩
        · rfl
        · rfl
      · simp only [us, List.cons_append, List.nil_append, rights, rights_map_inl]
        let ys : List (Round sigUI sigU) := xs.map fun x => ⟨x.q, [⟨some x.q, x.a⟩], x.a⟩
        have hys : ys.map Round.call = xs.map Round.call := by
          simp only [ys, List.map_map]; rfl
        have hc : allCalls ys = (xs.map (exRound (R := Unit))).map Round.call := by
          simp only [ys]
          clear hD hN hz hys
          induction xs with
          | nil => rfl
          | cons x xs ih => simp only [List.map_cons, allCalls, ih]; rfl
        have := comp_handler_round (g := exH sigU Unit) (σ := N) (q := none) (a := a) ys
          (by rw [hys]; exact hN)
          (by
            intro r hr
            simp only [ys, List.mem_map] at hr
            obtain ⟨x, -, rfl⟩ := hr
            exact .call (.pure _))
        rw [hc] at this
        simpa only [roundsMoves, List.append_nil] using this
    · refine mem_ofHandler_rounds _ fun r hr => ?_
      simp only [List.mem_cons, List.mem_map] at hr
      rcases hr with rfl | ⟨z, hzz, rfl⟩
      · exact instSplitH_runs e a
      · exact instSplitH_runs_left (hz z hzz) z.a
    · have h := zip_round (zip_split_rounds zs hz)
        [sided (.inl ⟨none, [⟨none, InstAns.ready⟩], InstAns.ready⟩),
          sided (.inr ⟨none, (xs.map (exRound (R := Unit))).map Round.call, a⟩)] none a
      simpa only [us, List.cons_append, List.nil_append, List.map_cons, roundsMoves, allCalls,
        sided, Round.inl, Round.inr, Round.call, List.map_nil, List.singleton_append,
        List.append_assoc, List.append_nil, tI, List.map_map, Function.comp_def] using h
  refine ⟨_, hD, _, hT, ?_⟩
  have h := zip_round (zip_fwd_rounds zs) (instRound w .ready :: xs.map exRound) none a
  simpa only [List.map_append, roundsMoves_append, List.map_cons, roundsMoves, allCalls,
    allCalls_map_exRound, Round.call, instRound, tI, List.append_assoc] using h

/-- **A failed environment fails the extension**; the new instance is never asked. -/
theorem extI_fail {e : Nat} {D : Strategy X sigUI} {N : Strategy sigU sigUI}
    (w : List (Call X)) (r : Unit) (hD : (instRound w (InstAns.fail r)).moves ∈ D) :
    (instRound w (InstAns.fail r)).moves ∈ extI e D N := by
  have hT : (Round.moves (⟨none, [⟨none, InstAns.fail r⟩], InstAns.fail r⟩ :
      Round sigUI sigUI)) ∈
      ((Strategy.id sigUI).pair ((Strategy.ofHandler (exH sigU Unit)).comp N)).comp
        (Strategy.ofHandler (instSplitH e)) := by
    let us : List (Round sigUI sigUI ⊕ Round sigUI sigUI) :=
      [.inl ⟨none, [⟨none, InstAns.fail r⟩], InstAns.fail r⟩]
    refine ⟨roundsMoves (us.map sided), ?_, roundsMoves
      [(⟨none, [⟨.inl none, InstAns.fail r⟩], InstAns.fail r⟩ : Round (sigUI ⊕ₛ sigUI) sigUI)],
      ?_, ?_⟩
    · refine mem_pair_rounds us (mem_id_rounds _ fun r hr => ?_) (Strategy.nil_mem _)
      simp only [us, lefts, List.mem_singleton] at hr
      subst hr
      rfl
    · refine mem_ofHandler_rounds _ fun r' hr => ?_
      rw [List.mem_singleton] at hr
      subst hr
      exact instSplitH_runs_fail e r
    · have h := zip_round (Zip.nil (α := Ev sigUI) (β := Ev (sigUI ⊕ₛ sigUI))
        (γ := Ev sigUI)) (us.map sided) none (InstAns.fail r)
      simpa only [us, List.map_cons, List.map_nil, roundsMoves, allCalls, sided, Round.inl,
        Round.call, List.append_nil] using h
  refine ⟨_, hD, _, hT, ?_⟩
  have h := zip_round (Zip.nil (α := Ev X) (β := Ev sigUI) (γ := Ev sigUI))
    [instRound w (InstAns.fail r)] none (InstAns.fail r)
  simpa only [roundsMoves, allCalls, Round.call, List.map_cons, List.map_nil,
    List.append_nil] using h

/-! ## The imports -/

/-- The forwarding round of a host import call. -/
def hostRound (q : sigU.Op) (r : Option Payload) : Round sigU sigU := ⟨q, [⟨q, r⟩], r⟩

/-- **The imports are ready at once and forward their calls.** -/
theorem withReady_maskH_rounds (n : Nat) (zs : List (sigU.Op × Option Payload))
    (hz : ∀ z ∈ zs, z.1.1 < n) :
    roundsMoves (instRound (F := sigU) [] .ready ::
      (zs.map fun z => hostRound z.1 z.2).map exRound) ∈
      withReady (R := Unit) (Strategy.ofHandler (maskH n)) := by
  rw [withReady, ← Strategy.ofHandler_comp]
  refine mem_ofHandler_rounds _ fun r hr => ?_
  simp only [List.mem_cons, List.map_map, List.mem_map] at hr
  rcases hr with rfl | ⟨⟨q, a⟩, hq, rfl⟩
  · exact .pure _
  · have h := hz _ hq
    show Prog.Runs (((maskH n) q).bind fun n' => (Prog.pure n').interp (maskH n)) [⟨q, a⟩] a
    simp only [maskH, Target.prog, h, ↓reduceIte, Prog.bind, Prog.interp]
    exact .call (.pure _)

/-! ## Core nodes and components -/

variable {M : Type} [CoreModule M]

/-- **A core node's instantiation round**: the module's instantiation calls are served by its
wiring `implsN`. -/
theorem coreNodeI_inst (C : CoreSemI M) (e : Nat) (m : M) (args : List Impl)
    (xs : List (Round sigU (CoreIface.sig (CoreModule.imports m)))) (a : InstAns Unit)
    (hS : (instRound (F := CoreIface.sig (CoreModule.exports m)) (xs.map Round.call) a).moves ∈
      C.sem m)
    (hx : ∀ x ∈ xs, Prog.Runs (implsN e args (CoreModule.imports m).length x.q) x.cs x.a) :
    (instRound (F := sigU) (allCalls xs) a).moves ∈ coreNodeI C e m args :=
  comp_handler_round xs (comp_liftH_inst _ hS) hx

/-- **An instantiation round of the nodes is one of the component.** -/
theorem denI_of_denNodesI (C : CoreSemI M) (I : Iface) (ns : List (Node M)) (xs : List Export)
    (cs : List (Call sigU)) (a : InstAns Unit)
    (h : (instRound (F := sigU) cs a).moves ∈
      denNodesI C I.length ns (withReady (Strategy.ofHandler (maskH I.length)))) :
    (instRound (F := sigU) cs a).moves ∈ (Comp.mk I ns xs).denI C := by
  rw [Comp.denI, Comp.denIR]
  refine (mem_instGuard_iff ?_).2 (comp_liftH_inst _ h)
  have hu : upper (instRound (X := sigU) (F := sigU) cs a).moves =
      [.ask none, Ev.ans (E := sigUI) none a] := by
    simp only [instRound, Round.moves, upper, List.filterMap_cons, Sum.getRight?_inr,
      List.filterMap_append, List.filterMap_map, List.filterMap_nil]
    have : ∀ l : List (Ev sigU), List.filterMap (Sum.getRight? ∘ Sum.inl (β := Ev sigUI)) l = [] := by
      intro l; induction l with
      | nil => rfl
      | cons x l ih => exact ih
    rw [this]; rfl
  rcases a with _ | r
  · exact .inr (.inr (.inr ⟨[], hu, fun _ h => nomatch h⟩))
  · exact .inr (.inr (.inl ⟨r, hu⟩))

end Silmaril.Proofs.Wasm.Component.InstSem
