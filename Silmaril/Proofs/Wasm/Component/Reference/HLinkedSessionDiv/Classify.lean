module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.Back
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession.IR

/-!
# Diverging calls of `HLinked2.toRef`, backward: the classification

`ldiv_classifyH`: an explicit infinite run `t` from the importer's core activation, on which the
host state `st` occurs at unboundedly late positions, is a finite prefix of served import calls
(their host calls answered as `g` answers, from the host state `h₀` of the activation to `st`)
followed by (i) B diverging host-free, (ii) A diverging inside a wired call, or (iii) **wired**
chatter. The host state is measured by `μ` (for the logging host, the length of the log): an
answered host call increases it (`hgμ`), and along the run the host state is unchanged or `μ`
grows (`hmono`, the host-write invariant of `HostWrite`).

* If a finite chain of served calls reaches (i) or (ii), the run stays from some position on in
  the host state of that round, so `st` is it.
* Otherwise dependent choice (`seq_of_step`) gives infinitely many served calls at strictly
  increasing positions. Infinitely many of them cannot be host calls: `μ` would grow without
  bound along the rounds, while every round is followed on the run by a configuration in `st`,
  so `μ` of every round's host state is at most `μ st`. So from some round `K` on every served
  call is wired, the host state is that of round `K`, and `st` is it: a configuration in `st`
  after round `K` is followed by a later round, and `hmono` both ways gives equality.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionFwd
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionRef
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDivInv
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSession
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine
open Silmaril.Wasm.Execution.Core (Store FuncInst)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Component (ValTy liftArgs lowerArgs Flat checkLower Payload sigN FuncTy)

local notation "STh" => Silmaril.Wasm.SingleThreaded.Thread
local notation "RVal" => Silmaril.Wasm.Component.Reference.Val

variable {P : Profile} {σ : Type} {prof : ProfileKind} {impl : HostImpl (E3 P) σ}
  {g : σ → HostFuncId → List RVal → Option (List RVal × σ)}

/-- Wired import calls with no host call are `ExpRunT` segments of the underlying `Linked2`. -/
theorem expRunH_toT {l : HLinked2} {I : Silmaril.Wasm.Game.ScalarInstance} :
    ∀ {s s' : Store Nat} {ds : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)},
      HLinked2.ExpRunH P l I s ds s' → l.hostCalls ds = [] → Linked2.ExpRunT P l.toL2 I s ds s'
  | _, _, _, .nil _, _ => .nil _
  | _, _, _, .ret (n := n) w hw hR h, hh => by
    have hk : n.val < l.wire.length := (List.getElem?_eq_some_iff.mp hw).1
    rw [hostCalls_cons_wired hk] at hh
    exact .ret w hw hR (expRunH_toT h hh)
  | _, _, _, .trap (n := n) w hw hT h, hh => by
    have hk : n.val < l.wire.length := (List.getElem?_eq_some_iff.mp hw).1
    rw [hostCalls_cons_wired hk] at hh
    exact .trap w hw hT (expRunH_toT h hh)
  | _, _, _, .host (n := n) i hn h, hh => by
    have hw : l.wire.length ≤ n.val := by omega
    have hi : n.val - l.wire.length < l.host.length := by omega
    rw [hostCalls_cons_host hw hi] at hh
    exact absurd hh (List.cons_ne_nil _ _)

theorem hostCalls_append (l : HLinked2)
    (a b : List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)) :
    l.hostCalls (a ++ b) = l.hostCalls a ++ l.hostCalls b := List.filterMap_append

/-- A state of a diverging call in the importer's core activation, at a position of the run. -/
structure DStH (P : Profile) (σ : Type) where
  p : ℕ
  y : CoreSt (E3 P)
  x : Store Nat × STh
  π : Store Nat
  ιe : InstState
  SL : List Subtask
  CL : List (Caller (E3 P))
  TL : List (Runtime.Task (E3 P))
  HL : List Runtime.Thread
  C : List (Option (Activation (E3 P) σ))
  h : σ

variable {l : HLinked2} {Ie Ii : Silmaril.Wasm.Game.ScalarInstance} {u₀ s₀ u : Store Nat}
  {F₀ : List (FuncInst (CanonHost (E3 P)))} {M₀ : Machine.Config (E3 P) σ}
  {th : Option ThreadId} {K : List Flat → Canon.P (E3 P) σ (Ret (E3 P))}
  {segs : List (Seg (E3 P) σ)} {rest : List (Activation (E3 P) σ)} {f : Ii.F.Op}

/-- The run is at the importer's core activation of `z`, `LInv` holding. -/
def DInvH (l : HLinked2) (Ie Ii : Silmaril.Wasm.Game.ScalarInstance) (s₀ u₀ u : Store Nat)
    (F₀ : List (FuncInst (CanonHost (E3 P)))) (M₀ : Machine.Config (E3 P) σ)
    (th : Option ThreadId) (K : List Flat → Canon.P (E3 P) σ (Ret (E3 P)))
    (segs : List (Seg (E3 P) σ)) (rest : List (Activation (E3 P) σ)) (f : Ii.F.Op)
    (t : ℕ → Machine.Config (E3 P) σ) (z : DStH P σ) : Prop :=
  t z.p = coreCfg (extG M₀ z.ιe z.SL z.CL z.TL z.HL z.C z.h) th K segs rest z.y ∧
    ThreadsOk z.ιe ∧
    LInv P l.toW Ie Ii s₀ u F₀ (ownOf s₀) (shOwn (sh s₀) (ownOf u₀)) f z.y z.x z.π

/-- **The classification of a quietly diverging call**: a finite prefix of served import calls
to the host state `st`, then B host-free, A inside a wired call, or wired chatter. -/
theorem ldiv_classifyH (S : HStat P l Ie Ii u F₀ M₀ (ownOf s₀)) (hF : GFrame M₀ th)
    (hH : HostHandlesB prof P impl g l M₀ th K segs rest) (hT : l.HostTyped g)
    (hex : ExitsQuietH prof P impl l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f)
    {t : ℕ → Machine.Config (E3 P) σ} (ht : IRun prof (fun _ _ => false) (DI P impl) t)
    (μ : σ → ℕ) (hgμ : ∀ s fn args rs s', g s fn args = some (rs, s') → μ s < μ s')
    (hmono : ∀ a b, a ≤ b → (t b).host = (t a).host ∨ μ (t a).host < μ (t b).host)
    {st : σ} (hio : ∀ N, ∃ n, N ≤ n ∧ (t n).host = st) {z₀ : DStH P σ}
    (hz₀ : DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z₀) :
    ∃ (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
      (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload)))
      (x : Store Nat × STh) (π : Store Nat),
      Ii.Path P (.running f z₀.x.1 z₀.x.2) (callMoves cs) (.running f x.1 x.2) ∧
      List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs dss ∧
      HLinked2.ExpRunH P l Ie z₀.π dss.flatten π ∧
      HostRun g z₀.h (l.hostCalls dss.flatten) st ∧
      (Linked2.DivB P x.1 x.2 ∨ Linked2.DivA P l.toL2 Ie Ii f x.1 x.2 π ∨
        Linked2.Chatter P l.toL2 Ie Ii f x.1 x.2 π) := by
  classical
  let Pre : DStH P σ → Prop := fun z => ∃ (cs : List (Σ e : Ii.E.Op, Ii.E.Ar e))
    (dss : List (List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload))),
    Ii.Path P (.running f z₀.x.1 z₀.x.2) (callMoves cs) (.running f z.x.1 z.x.2) ∧
    List.Forall₂ (Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii) cs dss ∧
    HLinked2.ExpRunH P l Ie z₀.π dss.flatten z.π ∧
    HostRun g z₀.h (l.hostCalls dss.flatten) z.h
  have hhost : ∀ z, DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z → (t z.p).host = z.h :=
    fun z hz => by rw [hz.1]; rfl
  by_cases hfin : ∃ z, Pre z ∧ DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z ∧
      ((Linked2.DivB P z.x.1 z.x.2 ∧ ∀ n, z.p ≤ n → (t n).host = z.h) ∨
        (Linked2.DivA P l.toL2 Ie Ii f z.x.1 z.x.2 z.π ∧ ∃ p₀, ∀ n, p₀ ≤ n → (t n).host = z.h))
  · obtain ⟨z, ⟨cs, dss, h₁, h₂, h₃, h₄⟩, -, hd⟩ := hfin
    have hst : z.h = st := by
      rcases hd with ⟨-, hc⟩ | ⟨-, p₀, hc⟩
      · obtain ⟨n, hn, hs⟩ := hio z.p
        rw [← hs, hc n hn]
      · obtain ⟨n, hn, hs⟩ := hio p₀
        rw [← hs, hc n hn]
    exact ⟨cs, dss, z.x, z.π, h₁, h₂, h₃, hst ▸ h₄,
      hd.elim (fun h => .inl h.1) (fun h => .inr (.inl h.1))⟩
  -- every round is a served import call
  let T : DStH P σ → (Σ e : Ii.E.Op, Ii.E.Ar e) ×
      List (Σ _ : (sigN l.imp.imports.length).Op, Option Payload) → DStH P σ → Prop :=
    fun z gz z' => (Ii.Path P (.running f z.x.1 z.x.2) (callMoves [gz.1])
        (.running f z'.x.1 z'.x.2) ∧
      Silmaril.Wasm.Component.Reference.ImpRel l.imp Ii gz.1 gz.2 ∧
      HLinked2.ExpRunH P l Ie z.π gz.2 z'.π ∧ HostRun g z.h (l.hostCalls gz.2) z'.h ∧
      ((l.hostCalls gz.2 = [] ∧ z'.h = z.h) ∨ ∃ fn args rs, g z.h fn args = some (rs, z'.h)) ∧
      z.p < z'.p) ∧ DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z'
  have step : ∀ z, (Pre z ∧ DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z) →
      ∃ gz z', T z gz z' ∧ (Pre z' ∧ DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z') := by
    rintro z ⟨⟨cs, dss, h₁, h₂, h₃, h₄⟩, hz⟩
    rcases ldiv_roundH (u₀ := u₀) S hF hH hT hex ht hz.1 hz.2.1 hz.2.2 with h | h |
      ⟨c, ds, p', ιe', SL', CL', TL', HL', C', h', y', x', π', hpp, hp', hte', hI', hpath, hrel,
        hexp, hhr, hor⟩
    · exact absurd ⟨z, ⟨cs, dss, h₁, h₂, h₃, h₄⟩, hz, .inl h⟩ hfin
    · exact absurd ⟨z, ⟨cs, dss, h₁, h₂, h₃, h₄⟩, hz, .inr h⟩ hfin
    let z' : DStH P σ := ⟨p', y', x', π', ιe', SL', CL', TL', HL', C', h'⟩
    have hz' : DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t z' := ⟨hp', hte', hI'⟩
    refine ⟨(c, ds), z', ⟨⟨hpath, hrel, hexp, hhr, hor, hpp⟩, hz'⟩,
      ⟨cs ++ [c], dss ++ [ds], ?_, List.rel_append h₂ (.cons hrel .nil), ?_, ?_⟩, hz'⟩
    · rw [callMoves_append]
      exact path_append h₁ hpath
    · rw [List.flatten_append, List.flatten_singleton]
      exact expRunH_append h₃ hexp
    · rw [List.flatten_append, List.flatten_singleton, hostCalls_append]
      exact hostRun_append h₄ hhr
  obtain ⟨sq, gs, h0, hs⟩ := seq_of_step _ T step
    (⟨⟨[], [], .nil _, .nil, .nil _, .nil _⟩, hz₀⟩ : Pre z₀ ∧ _)
  have hinv : ∀ k, DInvH l Ie Ii s₀ u₀ u F₀ M₀ th K segs rest f t (sq k)
    | 0 => h0 ▸ hz₀
    | k + 1 => (hs k).2
  have hpre : ∀ k, Pre (sq k) := by
    intro k
    induction k with
    | zero => exact h0 ▸ ⟨[], [], .nil _, .nil, .nil _, .nil _⟩
    | succ k ih =>
      obtain ⟨cs, dss, h₁, h₂, h₃, h₄⟩ := ih
      obtain ⟨⟨hp, hr, he, hh, -, -⟩, -⟩ := hs k
      refine ⟨cs ++ [(gs k).1], dss ++ [(gs k).2], ?_, List.rel_append h₂ (.cons hr .nil), ?_, ?_⟩
      · rw [callMoves_append]
        exact path_append h₁ hp
      · rw [List.flatten_append, List.flatten_singleton]
        exact expRunH_append h₃ he
      · rw [List.flatten_append, List.flatten_singleton, hostCalls_append]
        exact hostRun_append h₄ hh
  have hpos : ∀ k, (sq 0).p + k ≤ (sq k).p := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => have := (hs k).1.2.2.2.2.2; omega
  -- `μ` of every round is bounded by `μ st`
  have hbound : ∀ k, μ (sq k).h ≤ μ st := by
    intro k
    obtain ⟨n, hn, hst⟩ := hio (sq k).p
    rcases hmono _ _ hn with e | e
    · rw [← hst, e, hhost _ (hinv k)]
    · rw [← hst]
      rw [hhost _ (hinv k)] at e
      exact e.le
  have hμstep : ∀ k, μ (sq k).h ≤ μ (sq (k + 1)).h := by
    intro k
    rcases (hs k).1.2.2.2.2.1 with ⟨-, e⟩ | ⟨fn, args, rs, hg⟩
    · rw [e]
    · exact (hgμ _ _ _ _ _ hg).le
  have hμmono : ∀ a b, a ≤ b → μ (sq a).h ≤ μ (sq b).h := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact ih.trans (hμstep b)
  by_cases hw : ∃ K₀, ∀ k, K₀ ≤ k → l.hostCalls (gs k).2 = []
  · obtain ⟨K₀, hK⟩ := hw
    obtain ⟨cs, dss, h₁, h₂, h₃, h₄⟩ := hpre K₀
    -- from round `K₀` on the host state is that of round `K₀`
    have hconst : ∀ k, (sq (K₀ + k)).h = (sq K₀).h := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        obtain ⟨⟨-, -, -, hh, -, -⟩, -⟩ := hs (K₀ + k)
        rw [hK _ (Nat.le_add_right _ _)] at hh
        rw [← ih, ← Nat.add_assoc]
        exact (hostRun_nil hh).symm
    have hst : (sq K₀).h = st := by
      obtain ⟨n, hn, hstn⟩ := hio (sq K₀).p
      have hk : n ≤ (sq (K₀ + n)).p := by
        have := hpos (K₀ + n)
        omega
      have e₁ := hhost _ (hinv K₀)
      have e₂ := hhost _ (hinv (K₀ + n))
      rw [hconst n] at e₂
      rcases hmono _ _ hn with a | a <;> rcases hmono _ _ hk with b | b
      · rw [← hstn, a, e₁]
      · rw [← hstn, a, e₁]
      · rw [e₂, hstn] at b
        rw [e₁, hstn] at a
        omega
      · rw [e₂, hstn] at b
        rw [e₁, hstn] at a
        omega
    refine ⟨cs, dss, (sq K₀).x, (sq K₀).π, h₁, h₂, h₃, hst ▸ h₄, .inr (.inr ?_)⟩
    refine ⟨fun k => .running f (sq (K₀ + k)).x.1 (sq (K₀ + k)).x.2, fun k => (gs (K₀ + k)).1,
      fun k => (gs (K₀ + k)).2, fun k => (sq (K₀ + k)).π, rfl, rfl, fun k => ?_⟩
    obtain ⟨⟨hp, hr, he, -, -, -⟩, -⟩ := hs (K₀ + k)
    exact ⟨hp, hr, expRunH_toT he (hK _ (Nat.le_add_right _ _))⟩
  · -- infinitely many host calls: `μ` would grow without bound
    exfalso
    have hun : ∀ m, ∃ k, m ≤ μ (sq k).h := by
      intro m
      induction m with
      | zero => exact ⟨0, Nat.zero_le _⟩
      | succ m ih =>
        obtain ⟨k, hk⟩ := ih
        obtain ⟨j, hj, hne⟩ : ∃ j, k ≤ j ∧ l.hostCalls (gs j).2 ≠ [] := by
          by_contra hc
          exact hw ⟨k, fun j hj => by
            by_contra h'
            exact hc ⟨j, hj, h'⟩⟩
        rcases (hs j).1.2.2.2.2.1 with ⟨e, -⟩ | ⟨fn, args, rs, hg⟩
        · exact absurd e hne
        · exact ⟨j + 1, by have := hgμ _ _ _ _ _ hg; have := hμmono _ _ hj; omega⟩
    obtain ⟨k, hk⟩ := hun (μ st + 1)
    have := hbound k
    omega

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv
