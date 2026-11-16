module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.InfImp
public import Silmaril.Wasm.Abstract.NodeDiv.Thms
public import Silmaril.Wasm.Abstract.NodeTrap.Thms

/-!
# Building the divergences of a linked component: chatter

The converse of `Chatter.chatterReadBack_profile`, at every profile: a specification session
followed by a round of the importer making infinitely many core import calls, each served by the
exporter along one run (`Linked2.sessDivsC`), is an IR divergence, coming from chatter between
the importer's node and the exporter's environment (`Linked2.chatterSrc`).

* **The importer's calls** (`no_trap_of_inf`, `impRel_single`): in an infinite play of the
  instance's read-back session no import call is answered by a trap (a trapped instance makes no
  further call, `NodeTrap.instSession_trapEndsBelow`), so each core import call of the round is
  one component import call. The round's calls so far and the calls of `Linked2.Chatter` are one
  stream (`prependStream`), an infinite play of the read-back session
  (`NodeDiv.mem_inf_spullD_instSession_stream`), then of the importer's IR (`imp_inf_pend`) and of
  its node (`node_inf_build`).
* **The exporter's runs** (`expRunT_prepend`): the exporter serves the import calls of the
  session, of the round so far and of the chatter, one by one along one store sequence; each is
  a round of its instance (`exp_layers`), and they form an infinite play of its read-back session
  (`inf_spullD_cpl`, by `StratSession.mem_inf_iff`), then of its IR (`imp_inf_cpl`) and of its
  environment (`exp_env_inf`).
* **The chatter** (`div_denD_of_sessDivsC`): the visible play stops just after the pending call
  of the linked export; above the exporter's environment, the importer's node calls the wired
  exports forever, the environment answering (`ExtChatter`), and the outer handlers give the IR
  divergence (`top_build`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.Abstract.InstSession (spullD instSession srelabel instTripleS instFinS sAns)
open Silmaril.Wasm.Abstract.NodeDiv (stream)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance
local notation "pS" => Silmaril.Wasm.Abstract.NodeDiv.prependStream
local notation "ImpRel" => Silmaril.Wasm.Component.Reference.ImpRel

/-! ## Streams -/

section Streams

variable {α β : Type}

theorem pS_nil' (c : ℕ → α) (k : ℕ) : pS [] c k = c k := by
  simp [Silmaril.Wasm.Abstract.NodeDiv.prependStream]

theorem pS_zero (x : α) (l : List α) (c : ℕ → α) : pS (x :: l) c 0 = x := by
  simp [Silmaril.Wasm.Abstract.NodeDiv.prependStream]

theorem pS_succ (x : α) (l : List α) (c : ℕ → α) (k : ℕ) :
    pS (x :: l) c (k + 1) = pS l c k := by
  unfold Silmaril.Wasm.Abstract.NodeDiv.prependStream
  by_cases h : k < l.length <;> simp [h]

theorem pS_map (f : α → β) (l : List α) (c : ℕ → α) (k : ℕ) :
    pS (l.map f) (fun k => f (c k)) k = f (pS l c k) := by
  unfold Silmaril.Wasm.Abstract.NodeDiv.prependStream
  by_cases h : k < l.length <;> simp [h]

theorem pS_length_add (l : List α) (c : ℕ → α) (n : ℕ) :
    pS l c (l.length + n) = c n := by
  simp [Silmaril.Wasm.Abstract.NodeDiv.prependStream]

theorem streamTake_prepend (l : List α) (c : ℕ → α) :
    ∀ n, streamTake (pS l c) (l.length + n) = l ++ streamTake c n
  | 0 => by
    rw [Nat.add_zero, streamTake_eq_take (Z := l) (fun k hk => by simp [Silmaril.Wasm.Abstract.NodeDiv.prependStream, hk]) le_rfl,
      List.take_length]
    simp [streamTake]
  | n + 1 => by
    rw [← Nat.add_assoc, streamTake_snoc, streamTake_prepend l c n, streamTake_snoc,
      List.append_assoc, pS_length_add]

theorem streamTake_map (f : α → β) (c : ℕ → α) (n : ℕ) :
    streamTake (fun k => f (c k)) n = (streamTake c n).map f := by
  simp [streamTake, List.map_ofFn]
  rfl

theorem pS_forall₂ {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ {a : ℕ → α} {b : ℕ → β},
      (∀ k, R (a k) (b k)) → ∀ k, R (pS l a k) (pS l' b k)
  | _, _, .nil, _, _, h, k => by
    rw [pS_nil', pS_nil']
    exact h k
  | _, _, .cons hxy _, _, _, _, 0 => by
    rw [pS_zero, pS_zero]
    exact hxy
  | _, _, .cons _ t, _, _, h, k + 1 => by
    rw [pS_succ, pS_succ]
    exact pS_forall₂ t h k

theorem flatten_map_singleton : ∀ l : List α, (l.map fun x => [x]).flatten = l
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, List.flatten_cons, flatten_map_singleton l]
    rfl

end Streams

/-! ## Moves -/

section Moves

variable {E F : Sig.{0}}

theorem refCallMoves_eq : ∀ l : List (Σ m : E.Op, E.Ar m),
    (callMoves l : List (Move E F)) = Silmaril.Games.Abstract.StratObs.callMoves l
  | [] => rfl
  | ⟨m, n⟩ :: l => by
    rw [callMoves, refCallMoves_eq l]
    simp [Silmaril.Games.Abstract.StratObs.callMoves]

/-- The shared events of the rounds `l`: each question, then its answer. -/
def evs (l : List (Round F)) : List (Ev F) := l.flatMap fun x => [.ask x.1, .ans x.1 x.2]

theorem evs_inr : ∀ l : List (Round F), (evs l).map (Sum.inr (α := Ev E)) = twos l
  | [] => rfl
  | ⟨q, a⟩ :: l => by
    simp only [evs, List.flatMap_cons, List.map_append] at *
    rw [show (List.flatMap (fun x : Round F => [Ev.ask x.1, Ev.ans x.1 x.2]) l).map
      (Sum.inr (α := Ev E)) = twos l from evs_inr l]
    rfl

theorem evs_inl : ∀ l : List (Round E), (evs l).map (Sum.inl (β := Ev F)) = callMoves l
  | [] => rfl
  | ⟨q, a⟩ :: l => by
    simp only [evs, List.flatMap_cons, List.map_append] at *
    rw [show (List.flatMap (fun x : Round E => [Ev.ask x.1, Ev.ans x.1 x.2]) l).map
      (Sum.inl (β := Ev F)) = callMoves l from evs_inl l]
    rfl

theorem cch_mk0 (Z : ℕ → Round F) (n : ℕ) :
    cch (fun k => mk0 (E := E) (Z k)) n = twos (streamTake Z n) := by
  simp only [cch]
  rw [streamTake_map mk0 Z]
  exact cplay_mk0 _

theorem length_evs : ∀ l : List (Round F), (evs l).length = 2 * l.length
  | [] => rfl
  | x :: l => by
    have := length_evs l
    simp only [evs, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
      at *
    omega

end Moves

/-! ## The exporter, serving forever -/

section Exp

variable {E : Sig.{0}}

theorem cplay_srelabel {I : SInst} : ∀ l : List (CRound I.E I.F),
    (cplay l).map srelabel = Silmaril.Games.Abstract.StratSession.sroundsMoves
      (l.map fun x => (x.q, x.cs, sAns x.q x.a))
  | [] => rfl
  | r :: l => by
    simp only [cplay, List.map_cons, List.map_append, cplay_srelabel l,
      Silmaril.Games.Abstract.StratSession.sroundsMoves, List.flatMap_cons,
      Silmaril.Games.Abstract.StratSession.sroundMoves, List.cons_append, List.append_assoc]
    rw [← refCallMoves_eq]
    congr 2
    clear cplay_srelabel
    induction r.cs with
    | nil => rfl
    | cons x cs ih =>
      obtain ⟨m, n⟩ := x
      simp only [callMoves, List.map_cons] at *
      rw [ih]
      rfl

theorem rounds_snoc' {S A B : Type} {t : Silmaril.Games.Abstract.ObsTriple E S A B} :
    ∀ {s s₁ s₂ : S} {rs : List (A × List (Σ m : E.Op, E.Ar m) × B)} {a : A}
      {c : List (Σ m : E.Op, E.Ar m)} {b : B},
      Silmaril.Games.Abstract.StratThread.Rounds t s rs s₁ → (c, .ret b s₂) ∈ t.1 s₁ a →
      Silmaril.Games.Abstract.StratThread.Rounds t s (rs ++ [(a, c, b)]) s₂
  | _, _, _, _, _, _, _, .nil _, h => .cons h (.nil _)
  | _, _, _, _, _, _, _, .cons h₁ hr, h => .cons h₁ (rounds_snoc' hr h)

/-- **Rounds of an instance forever, along one run, are an infinite play of its read-back
session.** -/
theorem inf_spullD_cpl {I : SInst} {P : Profile} {S : ℕ → Store Nat} {R : ℕ → CRound I.E I.F}
    (hp : ∀ k, I.Path P (.idle (S k)) (cplay [R k]) (.idle (S (k + 1)))) :
    (cch R).lim ∈ (spullD (instSession I P (S 0))).inf := by
  refine ⟨Chain.isInfPlay_lim (cch_mono R) (cch_unbounded R), ?_⟩
  rw [lim_image]
  refine Silmaril.Games.Abstract.StratSession.mem_inf_iff.2 (.inr
    ⟨fun k => (R k).q, fun k => ((R k).cs, sAns (R k).q (R k).a), ?_, fun k => ⟨S k, ?_⟩⟩)
  · congr 1
    funext n
    show (cplay (streamTake R n)).map srelabel = _
    rw [cplay_srelabel, ← streamTake_map]
  · induction k with
    | zero => exact .nil _
    | succ k ih =>
      rw [streamTake_snoc]
      refine rounds_snoc' ih (.inl ⟨(R k).a, S (k + 1), rfl, ?_⟩)
      have h := hp k
      simp only [cplay] at h
      rw [← refCallMoves_eq]
      exact h

/-- **The exporter's run preserves well-formed stores.** -/
theorem expRunT_wf {P : Profile} {l : Linked2} (hc : l.exp.Good) {I : SInst}
    (hI : l.exp.mod.IsInst I) :
    ∀ {s s' : Store Nat} {ds : List (Round (sigN l.imp.imports.length))},
      Linked2.ExpRunT P l I s ds s' → I.WellFormed s → I.WellFormed s'
  | _, _, _, .nil _, h => h
  | _, _, _, .ret w _ hret hrun, h =>
    expRunT_wf hc hI hrun (hret.wellFormed hI (hc.core _ (List.getElem_mem w.isLt)) h)
  | _, _, _, .trap w _ htrap hrun, h =>
    expRunT_wf hc hI hrun (htrap.wellFormed hI (hc.core _ (List.getElem_mem w.isLt)) h)

/-- **The exporter's runs, one after another**: a run serving the lists `L`, then a run along
the stream `ds`, is a run along the stream of `L` then `ds`. -/
theorem expRunT_prepend {P : Profile} {l : Linked2} {I : SInst} :
    ∀ (L : List (List (Round (sigN l.imp.imports.length)))) {s s' : Store Nat}
      (ds : ℕ → List (Round (sigN l.imp.imports.length))) (st : ℕ → Store Nat),
      Linked2.ExpRunT P l I s L.flatten s' → st 0 = s' →
      (∀ k, Linked2.ExpRunT P l I (st k) (ds k) (st (k + 1))) →
      ∃ S : ℕ → Store Nat, S 0 = s ∧
        ∀ k, Linked2.ExpRunT P l I (S k) (pS L ds k) (S (k + 1))
  | [], _, _, ds, st, h, h0, hk => by
    obtain rfl := expRunT_nil_inv h
    exact ⟨st, h0, fun k => by rw [pS_nil']; exact hk k⟩
  | x :: L, s, _, ds, st, h, h0, hk => by
    rw [List.flatten_cons] at h
    obtain ⟨s₁, h₁, h₂⟩ := expRunT_split _ _ h
    obtain ⟨S, hS0, hS⟩ := expRunT_prepend L ds st h₂ h0 hk
    refine ⟨fun k => Nat.casesOn k s fun k => S k, rfl, fun k => ?_⟩
    cases k with
    | zero =>
      rw [pS_zero]
      show Linked2.ExpRunT P l I s x (S 0)
      rw [hS0]
      exact h₁
    | succ k =>
      rw [pS_succ]
      exact hS k

/-- **The exporter's environment serving forever** (under `Linked2.Adequate`): import calls
`Zs k` served one by one by the exporter's specification along one run from its instance's
store, renamed to the wired exports, are an infinite play of the exporter's environment. -/
theorem exp_env_inf {P : Profile} {l : Linked2} (hl : l.Adequate) {Ie : SInst}
    (hIe : l.exp.mod.IsInst Ie) {Zs : ℕ → Round (sigN l.imp.imports.length)}
    {S : ℕ → Store Nat} (hS0 : S 0 = Ie.store)
    (hS : ∀ k, Linked2.ExpRunT P l Ie (S k) [Zs k] (S (k + 1))) :
    (cch fun k => mk0 (E := sigU) (wireRound l (Zs k))).lim ∈
      (Linked2.expObs (impSemD P) l).inf := by
  have hwf : ∀ k, Ie.WellFormed (S k) := by
    intro k
    induction k with
    | zero => rw [hS0]; exact hIe.1.choose_spec.ok
    | succ k ih => exact expRunT_wf hl.expGood hIe (hS k) ih
  have hlay : ∀ k, ∃ d : LayerI (SimpleI.ofSimple l.exp) Ie, d.Ok (isInst_ofSimple hIe) ∧
      Ie.Path P (.idle (S k)) (cplay [d.r]) (.idle (S (k + 1))) ∧
      d.l₆ = mk0 (wireRound l (Zs k)) := by
    intro k
    obtain ⟨L, hL, hp, hm⟩ := exp_layers hl.expGood hIe (hS k) (hwf k)
    rcases L with _ | ⟨d, _ | ⟨d', L⟩⟩
    · simp at hm
    · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hm
      exact ⟨d, hL d List.mem_cons_self, hp, hm⟩
    · simp at hm
  choose D hD hp hm using hlay
  have hbot := inf_spullD_cpl hp
  rw [hS0] at hbot
  have hv := imp_inf_cpl (isInst_ofSimple hIe) hD hbot
  rw [show (fun k => (D k).l₆) = fun k => mk0 (wireRound l (Zs k)) from funext hm] at hv
  -- the exporter's node
  have hN : (cch fun k => mk0 (E := sigU) (wireRound l (Zs k))).lim ∈
      (Node.denD (impSemD P) 0 l.expNode).inf := by
    rw [Linked2.expNode, Node.denD]
    exact inf_below_cpl (oneCall_implsH 0 []) (fun k => .cons .nil .nil) hv
  -- the pairing, `splitH 0` and `maskH 0`
  have h₅ := inf_pair_cpl (DStrategy.id sigU) hN
  have h₄ := inf_top_cpl (h := splitH 0) (fun k => .call
    (splitH_shift 0 (wireRound l (Zs k)).1.1 (wireRound l (Zs k)).1.2) rfl .nil) h₅
  have h₃ := inf_below_cpl (oneCall_maskH 0) (fun k => .cons .nil .nil) h₄
  rw [show Linked2.expObs (impSemD P) l = DObs.of (DStrategy.ext 0
      (DStrategy.ofHandler (maskH 0)) (Node.denD (impSemD P) 0 l.expNode)) from
    (obs_ext _ _ _).symm]
  exact h₃

end Exp

/-! ## The importer, calling forever -/

section Imp

/-- **No import call of an infinite pending round is answered by a trap**: after a trap from
below, the instance's session makes no further call. -/
theorem no_trap_of_inf {I : SInst} {P : Profile} {s : Store Nat} {cl : List (CRound I.E I.F)}
    {f : I.F.Op} {ω : ℕ → Round I.E}
    (h : (rch cl f ω).lim ∈ (spullD (instSession I P s)).inf) (k : ℕ) :
    (ω k).2 ≠ Silmaril.Wasm.Game.Answer.trap := by
  intro htrap
  have hmem : rch cl f ω (k + 2) ∈ I.strategy P s := by
    rw [← Silmaril.Wasm.Abstract.InstSession.toStrategy_spullD_instSession]
    exact (spullD _).inf_sub h (Chain.mem_lim_self _ _)
  have e : rch cl f ω (k + 2) = (rch cl f ω k ++ [.inl (.ask (ω k).1)]) ++
      [.inl (.ans (ω k).1 (ω k).2), .inl (.ask (ω (k + 1)).1)] ++
        [.inl (.ans (ω (k + 1)).1 (ω (k + 1)).2)] := by
    rw [rch_succ, rch_succ]
    simp [callMoves]
  have hpre : (rch cl f ω k ++ [.inl (.ask (ω k).1)]) ++
      [.inl (.ans (ω k).1 (ω k).2), .inl (.ask (ω (k + 1)).1)] ∈ I.strategy P s :=
    (I.strategy P s).of_prefix hmem (by rw [e]; exact List.prefix_append _ _)
  have hS := (Silmaril.Wasm.Abstract.InstSession.map_srelabel_mem (I := I) (P := P)).2 hpre
  rw [List.map_append] at hS
  obtain ⟨g, hg⟩ := Silmaril.Wasm.Abstract.NodeTrap.instSession_trapEndsBelow s _ (ω k).1 (ω k).2
    _ htrap hS
  cases hg

/-- An import call not answered by a trap is one component import call. -/
theorem impRel_single {c : SimpleI} {I : SInst} {x : Σ e : I.E.Op, I.E.Ar e}
    {ds : List (Round (sigN c.imports.length))} (h : ImpRel c I x ds)
    (hx : x.2 ≠ Silmaril.Wasm.Game.Answer.trap) : ∃ y, ds = [y] := by
  obtain ⟨nm, ft, A, -, hv, hm⟩ := h
  split at hm
  · obtain ⟨rfl, -⟩ := hm
    exact absurd (show x.2 = Silmaril.Wasm.Game.Answer.trap by rw [← hv]; rfl) hx
  · obtain ⟨hk, R, rfl, -⟩ := hm
    exact ⟨_, rfl⟩

variable {P : Profile} {l : Linked2} {Ii : SInst}

/-- **The importer's node on an infinite pending round** (under `Linked2.Adequate`): its IR's
infinite pending round, the import calls renamed to the wired exports. -/
theorem node_inf_build {L : List (LayerI l.imp Ii)} {j : Fin l.imp.exports.length}
    {vs : List IVal} {Y : ℕ → Round (sigN l.imp.imports.length)}
    (hvI : (rch (L.map LayerI.l₆) (j.val, .vals vs) fun k => (Y k).forget).lim ∈
      (l.imp.toComp.denUD (impSemD P)).inf)
    (hall : ∀ x ∈ L.flatMap fun d => d.dss.flatten,
      ∃ w : Fin l.exp.exports.length, l.wire[x.1.1.val]? = some w.val)
    (hY : ∀ k, ∃ w : Fin l.exp.exports.length, l.wire[(Y k).1.1.val]? = some w.val) :
    (rch (L.map LayerI.wiredN) (j.val, .vals vs) fun k => wireRound l (Y k)).lim ∈
      (Node.denD (impSemD P) l.expNode.width l.impNode).inf := by
  have HN : HB (implsH l.exp.exports.length (wireArgs l)) (L.map LayerI.l₆)
      (L.map LayerI.wiredN) :=
    HB.of_map _ _ L fun d hd => .cons (hrounds_wire fun x hx =>
      hall x (List.mem_flatMap.mpr ⟨d, hd, hx⟩)) .nil
  have h := inf_below_pend (oneCall_implsH _ _) HN (j.val, .vals vs)
    (X := fun k => (Y k).forget) (Y := fun k => wireRound l (Y k))
    (fun k => hrounds_wire (ds := [Y k]) fun x hx => by
      rw [List.mem_singleton.mp hx]
      exact hY k) hvI
  rw [Linked2.impNode, Node.denD, expNode_width]
  exact h

end Imp

/-! ## Routing -/

section Route

variable {E F₁ F₂ : Sig.{0}}

theorem side_append :
    ∀ (b : Bool) (x y : List (Move E (F₁ ⊕ₛ F₂))),
      Split.side b (x ++ y) = Split.side (Split.side b x) y
  | b, [], y => rfl
  | b, .inl a :: x, y => by
    simp only [List.cons_append, Split.side]
    exact side_append b x y
  | b, .inr (.ask (.inl q)) :: x, y => by
    simp only [List.cons_append, Split.side]
    exact side_append false x y
  | b, .inr (.ask (.inr q)) :: x, y => by
    simp only [List.cons_append, Split.side]
    exact side_append true x y
  | b, .inr (.ans q r) :: x, y => by
    simp only [List.cons_append, Split.side]
    exact side_append b x y

theorem side_calls : ∀ (b : Bool) (cs : List (Round E)),
    Split.side b (callMoves cs : List (Move E (F₁ ⊕ₛ F₂))) = b
  | _, [] => rfl
  | b, ⟨_, _⟩ :: cs => by
    simp only [callMoves, Split.side]
    exact side_calls b cs

theorem side_rplay_inr (b : Bool) (cl : List (CRound E F₂)) (g : F₂.Op) (cs : List (Round E)) :
    Split.side b (rplay (cl.map (CRound.inr (F₁ := F₁))) (.inr g) cs) = true := by
  simp only [rplay]
  rw [side_append]
  simp only [Split.side]
  exact side_calls true cs

theorem route_calls (e : Nat) : ∀ cs : List (Round sigU),
    (callMoves cs : List (Move sigU sigU)).map (splitRoute e) = callMoves cs
  | [] => rfl
  | ⟨_, _⟩ :: cs => by
    simp only [callMoves, List.map_cons, route_calls e cs]
    rfl

theorem route_ask (e j : Nat) (p : Payload) :
    splitRoute e (.inr (.ask (e + j, p))) = .inr (.ask (.inr (j, p))) := by
  have h₁ : ¬ (e + j < e) := by omega
  have h₂ : e + j - e = j := by omega
  simp only [splitRoute, splitQ, h₁]
  generalize e + j - e = x at h₂ ⊢
  subst h₂
  rfl

theorem route_ans (e j : Nat) (p : Payload) (a : Option Payload) :
    splitRoute e (.inr (.ans (e + j, p) a)) = .inr (.ans (.inr (j, p)) a) := by
  have h₁ : ¬ (e + j < e) := by omega
  have h₂ : e + j - e = j := by omega
  simp only [splitRoute, h₁, ↓reduceIte]
  generalize e + j - e = x at h₂ ⊢
  subst h₂
  rfl

theorem route_cplay_wired {l : Linked2} {Ii : SInst} : ∀ L : List (LayerI l.imp Ii),
    (cplay (L.map LayerI.wired)).map (splitRoute l.exp.exports.length) =
      cplay ((L.map LayerI.wiredN).map (CRound.inr (F₁ := sigU)))
  | [] => rfl
  | d :: L => by
    simp only [List.map_cons, cplay, LayerI.wired, LayerI.wiredN, CRound.inr, List.map_append,
      route_calls, route_cplay_wired L, route_ask, route_ans]

theorem route_rplay_wired {l : Linked2} {Ii : SInst} (L : List (LayerI l.imp Ii)) (j : Nat)
    (p : Payload) :
    (rplay (L.map LayerI.wired) (l.exp.exports.length + j, p) []).map
        (splitRoute l.exp.exports.length) =
      rplay ((L.map LayerI.wiredN).map (CRound.inr (F₁ := sigU))) (.inr (j, p)) [] := by
  simp only [rplay, List.map_append, route_cplay_wired, List.map_cons, callMoves, List.map_nil,
    route_ask]

end Route

/-! ## The theorem -/

/-- **A round of chatter is an IR divergence from chatter** (every profile, under
`Linked2.Adequate`): after a specification session of `calls` with the outcomes `outs`, a round
of the importer on export `j` and `vs`, its import calls so far answered by the exporter, then
making infinitely many core import calls, each answered by the exporter along one run, is an IR
divergence after `sessMoves calls outs` on the pending call, coming from chatter between the
importer's node and the exporter's environment. -/
theorem chatterSrc_of_sessDivsC (P : Profile) {l : Linked2} (hl : l.Adequate)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {j : Fin l.imp.exports.length} {vs : List IVal}
    (h : outs ∈ Linked2.sessDivsC P l calls j vs) :
    Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
      l.irDiv (impSemD P) (l.chatterSrc (impSemD P)) := by
  obtain ⟨Ie, Ii, u, π, hIe, hIi, hS, d, s, t, π₁, rfl, rfl, hOk, hp, hr,
    q, c, ds, st, hq0, hst0, hk⟩ := h
  obtain ⟨L, hL, hpL, hrL, hm⟩ := LinkedSessionRef.sessSpec_rounds hS
  obtain ⟨LL, hLL, e₁, e₂⟩ := layers_of hl.impGood hIi (LinkedSessionIR.rel_u hL)
  obtain ⟨xs, hxs, hf₁, hf₂, hrel⟩ := hOk
  -- the importer's core import calls, one stream: an infinite play of its read-back session
  have hp₀ : Ii.Path P (.idle Ii.store) (cplay (LL.map LayerI.r)) (.idle u) := by
    rw [e₁, LinkedSessionIR.cplay_r]
    exact hpL
  have hbot : (rch (LL.map LayerI.r) d.f (pS d.cs c)).lim ∈
      (spullD (instSession Ii P Ii.store)).inf := by
    have hp' := hp
    rw [Linked2.DivRound.instMoves, refCallMoves_eq] at hp'
    have h₀ := Silmaril.Wasm.Abstract.NodeDiv.mem_inf_spullD_instSession_stream.2
      ⟨u, hp₀, Silmaril.Wasm.Abstract.NodeDiv.instInf_of_calls hp' hq0 fun k => by
        have hk' := (hk k).1
        rw [refCallMoves_eq] at hk'
        exact hk'⟩
    have e : stream (cplay (LL.map LayerI.r)) d.f (pS d.cs c) =
        rch (LL.map LayerI.r) d.f (pS d.cs c) := by
      funext n
      simp only [stream, rch, rplay, refCallMoves_eq]
    rw [e] at h₀
    exact h₀
  -- each core call is one component call
  have hrelω : ∀ k, ImpRel l.imp Ii (pS d.cs c k) (pS d.dss ds k) :=
    pS_forall₂ hrel fun k => (hk k).2.1
  choose Y hY using fun k => impRel_single (hrelω k) (no_trap_of_inf hbot k)
  have hrelY : ∀ k, ImpRel l.imp Ii (pS d.cs c k) [Y k] := fun k => by
    rw [← hY k]
    exact hrelω k
  -- the importer's IR
  have hvI := imp_inf_pend hl.impGood hIi hLL hxs hf₁ hf₂ hrelY hbot
  -- the exporter's runs, one call at a time
  have hcs : (LL.flatMap fun d => d.dss.flatten) = L.flatMap fun d => d.dss.flatten := by
    rw [← LinkedSessionIR.flatMap_u_cs, ← e₂, List.flatMap_map]
    rfl
  have hrun₀ : Linked2.ExpRunT P l Ie Ie.store (LL.flatMap fun d => d.dss.flatten) π := by
    rw [hcs]
    exact hrL
  obtain ⟨S₁, hS₁0, hS₁⟩ := expRunT_prepend d.dss ds st hr hst0 fun k => (hk k).2.2
  have hS₁' : ∀ k, Linked2.ExpRunT P l Ie (S₁ k) [Y k] (S₁ (k + 1)) := fun k => by
    rw [← hY k]
    exact hS₁ k
  obtain ⟨S, hS0, hSk⟩ := expRunT_prepend
    ((LL.flatMap fun d => d.dss.flatten).map fun x => [x]) (fun k => [Y k]) S₁
    (by rw [flatten_map_singleton]; exact hrun₀) hS₁0 hS₁'
  have hZ : ∀ k, Linked2.ExpRunT P l Ie (S k)
      [pS (LL.flatMap fun d => d.dss.flatten) Y k] (S (k + 1)) := fun k => by
    have h₁ := hSk k
    rw [pS_map (fun x => [x])] at h₁
    exact h₁
  have hE := exp_env_inf hl hIe hS0 hZ
  -- the importer's node
  have hN := node_inf_build hvI (LinkedSessionIR.expRunT_wire hrun₀)
    fun k => LinkedSessionIR.expRunT_wire (hS₁' k) _ List.mem_cons_self
  -- the chatter
  have hd : rplay ((LL.map LayerI.wired).map (CRound.hide (E := sigU)))
      (l.exp.exports.length + d.j.val, .vals d.vs) [] ∈ l.chatterSrc (impSemD P) := by
    refine ⟨_, hE, _, hN, twos ((LL.flatMap fun d => d.dss.flatten).map (wireRound l)),
      rplay (LL.map LayerI.wired) (l.exp.exports.length + d.j.val, .vals d.vs) [], ?_,
      ⟨_, path_rplay _ _ _⟩, ?_, ?_, fun k =>
        ⟨evs (streamTake (fun k => wireRound l (Y k)) k), ?_, ?_, ?_⟩⟩
    · have hz := zip_serve_pend (E := sigU) (LL.map LayerI.wired)
        (l.exp.exports.length + d.j.val, .vals d.vs) []
      rw [List.append_nil, flatMap_wired] at hz
      exact hz
    · rw [expNode_width, route_rplay_wired]
      exact side_rplay_inr _ _ _ _
    · rw [expNode_width, route_rplay_wired, halves_rplay_inr]
      exact (Strategy.id sigU).nil_mem
    · rw [length_evs, length_streamTake]
      omega
    · refine ⟨(LL.flatMap fun d => d.dss.flatten).length + k, ?_⟩
      rw [evs_inr, cch_mk0, streamTake_map (wireRound l) Y, streamTake_map (wireRound l),
        streamTake_prepend, List.map_append, twos_append]
    · refine ⟨k, ?_⟩
      rw [expNode_width, route_rplay_wired, halves_rplay_inr, evs_inl]
      rw [← rplay_app, List.nil_append]
      exact List.prefix_refl _
  have hX := top_build (P := P) hd
  have hplay : rplay ((LL.map LayerI.u).map (Linked2.linkRound l)) (l.topQ d.j d.vs) [] =
      Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ d.j d.vs))] := by
    rw [rplay, e₂, LinkedSessionIR.cplay_link, hm]
    rfl
  rw [hplay] at hX
  exact hX

/-- **A round of chatter is an IR divergence** (every profile, under `Linked2.Adequate`). -/
theorem div_denD_of_sessDivsC (P : Profile) {l : Linked2} (hl : l.Adequate)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    {j : Fin l.imp.exports.length} {vs : List IVal}
    (h : outs ∈ Linked2.sessDivsC P l calls j vs) :
    Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))] ∈
      (l.toComp.denD (impSemD P)).div := by
  rw [div_denD_eq_sources]
  exact .inr (chatterSrc_of_sessDivsC P hl h)

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
