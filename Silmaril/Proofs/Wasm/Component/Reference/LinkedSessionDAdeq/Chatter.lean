module

public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.EnvDiv
public import Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq.ImpCoherent
public import Silmaril.Wasm.Component.DWiringChatter3.Thms
public import Silmaril.Wasm.Component.DWiringMulti.Thms

/-!
# Chatter between the two nodes is a `Chatter` round, at deterministic profiles

`chatterReadBack_profile`: at `profile o`, an IR divergence coming from chatter between the
importer's node and the exporter's environment (`chatterSrc`) after a typed session and a typed
pending call is a specification session followed by a round of the importer that makes infinitely
many core import calls, served by the exporter along one run (`Linked2.Chatter`).

* **Stages** (`chatter_stage`): the chatter (`ExtChatter`) is a finite visible prefix `c₀` above
  an environment prefix `s₀`, then shared moves `w` exchanged forever, `N`'s half of the routed
  `c₀` continuing by `w` in an infinite play of the node. Cutting `w` just after one of the node's
  calls gives a play of the node layer `extTop` at a waiting position (`path_route`,
  `Split.halves_path`, `path_inl_relabel`), interacting with a play of the exporter's environment
  (`zip_hidden`).
* **The read-back of a stage** (`stage_readback`, as in `sessDivsA_of_envDiv`): the outer
  handlers give the session's rounds and the pending call (`top_div`); the node's play is read
  back to a waiting play of the importer's IR, then to its core instance (`imp_wait_readback`);
  the exporter's environment served the hidden calls (`serve_wait`).
* **The stages cohere** (`rplay_ext_inl`, `rounds_eq`, `pend_prefix`): the node's rounds are the
  same at every stage and its calls grow; at `profile o` the core rounds are the same and the core
  calls grow, so they have limit streams (`exists_limit`), and the exporter serves them along one
  run (`exp_plays_stream`).
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Games.Abstract (streamTake)
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.Adequacy
open Silmaril.Proofs.Wasm.Component.Reference.SessionAdequacy
open Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionAdeq
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (GrowOracle profile)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "SInst" => Silmaril.Wasm.Game.ScalarInstance

/-! ## Lists -/

section Lists

variable {E F : Sig.{0}}

theorem callMoves_app : ∀ (A B : List (Round E)),
    (callMoves (A ++ B) : List (Move E F)) = callMoves A ++ callMoves B
  | [], _ => rfl
  | ⟨m, n⟩ :: A, B => by
    show Sum.inl (Ev.ask m) :: Sum.inl (Ev.ans m n) :: callMoves (A ++ B) = _
    rw [callMoves_app A B]
    rfl

theorem length_callMoves : ∀ (cs : List (Round E)),
    (callMoves cs : List (Move E F)).length = 2 * cs.length
  | [] => rfl
  | ⟨m, n⟩ :: cs => by
    show (callMoves cs : List (Move E F)).length + 1 + 1 = _
    rw [length_callMoves cs, List.length_cons]
    omega

theorem length_rplay (cl : List (CRound E F)) (g : F.Op) (cs : List (Round E)) :
    (rplay cl g cs).length = (cplay cl).length + 1 + 2 * cs.length := by
  simp only [rplay, List.length_append, List.length_cons, length_callMoves]
  omega

theorem prefix_of_map_prefix {α β : Type} {f : α → β} (hf : Function.Injective f) :
    ∀ {a b : List α}, a.map f <+: b.map f → a <+: b
  | [], _, _ => List.nil_prefix
  | _ :: _, [], h => by simp at h
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons_prefix_cons] at h
    obtain ⟨hxy, h⟩ := h
    obtain rfl := hf hxy
    exact List.cons_prefix_cons.mpr ⟨rfl, prefix_of_map_prefix hf h⟩

theorem flatten_prefix {α : Type} {a b : List (List α)} (h : a <+: b) : a.flatten <+: b.flatten := by
  obtain ⟨t, rfl⟩ := h
  rw [List.flatten_append]
  exact List.prefix_append _ _

theorem twos_prefix {a b : List (Round F)} (h : a <+: b) :
    (twos a : List (Move E F)) <+: twos b := by
  obtain ⟨t, rfl⟩ := h
  rw [twos_append]
  exact List.prefix_append _ _

theorem streamTake_add' {α : Type} (ω : ℕ → α) (a : ℕ) :
    ∀ n, streamTake ω (a + n) = streamTake ω a ++ streamTake (fun k => ω (a + k)) n
  | 0 => by simp [streamTake]
  | n + 1 => by
    rw [← Nat.add_assoc, streamTake_snoc, streamTake_add' ω a n, streamTake_snoc,
      List.append_assoc]

theorem streamTake_prefix {α : Type} (ω : ℕ → α) {a b : ℕ} (h : a ≤ b) :
    streamTake ω a <+: streamTake ω b := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [streamTake_add']
  exact List.prefix_append _ _

@[simp] theorem length_streamTake {α : Type} (ω : ℕ → α) (n : ℕ) : (streamTake ω n).length = n := by
  simp [streamTake]

/-- Hidden moves at the end of an interaction. -/
theorem zip_hidden {α β γ : Type} {s : List (α ⊕ β)} {t : List (β ⊕ γ)} {p : List (α ⊕ γ)}
    (h : Zip s t p) (w : List β) : Zip (s ++ w.map .inr) (t ++ w.map .inl) p := by
  induction h with
  | nil =>
    induction w with
    | nil => exact .nil
    | cons b w ih => exact .sync b ih
  | left a _ ih => exact .left a ih
  | right c _ ih => exact .right c ih
  | sync b _ ih => exact .sync b ih

end Lists

/-! ## Positions of routed plays -/

section Route

/-- The position of a play above `D`, routed through `splitH e`. -/
def routePos (e : Nat) : Pos sigU sigU → Pos sigU (sigU ⊕ₛ sigU)
  | .idle => .idle
  | .run g => .run (splitQ e g)
  | .wait g m => .wait (splitQ e g) m

theorem path_route {e : Nat} {x z : Pos sigU sigU} {c : List (Move sigU sigU)}
    (h : Path x c z) : Path (routePos e x) (c.map (splitRoute e)) (routePos e z) := by
  induction h with
  | nil => exact .nil _
  | cons st _ ih =>
    refine .cons ?_ ih
    cases st with
    | ask q => exact .ask _
    | call q m => exact .call _ m
    | reply q m n => exact .reply _ m n
    | ret q r =>
      by_cases hq : q.1 < e
      · simp only [routePos, splitRoute, splitQ, hq, ↓reduceIte]
        exact .ret _ _
      · simp only [routePos, splitRoute, splitQ, hq, ↓reduceIte]
        exact .ret _ _

variable {E F : Sig.{0}}

/-- A position with its pending question replaced by `g`. -/
def relabel (g : F.Op) : Pos E F → Pos E F
  | .idle => .idle
  | .run _ => .run g
  | .wait _ m => .wait g m

/-- Lower moves do not depend on the pending question. -/
theorem path_inl_relabel (g : F.Op) :
    ∀ {w : List (Ev E)} {x z : Pos E F}, Path x (w.map .inl) z →
      Path (relabel g x) (w.map .inl) (relabel g z)
  | [], _, _, h => by cases h; exact .nil _
  | _ :: _, _, _, h => by
    cases h with
    | cons st h' =>
      refine .cons ?_ (path_inl_relabel g h')
      cases st with
      | call q m => exact .call g m
      | reply q m n => exact .reply g m n

theorem not_path_idle_inl {w : List (Ev E)} (hw : w ≠ []) {z : Pos E F} :
    ¬ Path .idle (w.map .inl) z := by
  intro h
  obtain ⟨b, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  cases h with
  | cons st _ => cases st

theorem halves_append {F₁ F₂ : Sig.{0}} :
    ∀ (b : Bool) (x y : List (Move E (F₁ ⊕ₛ F₂))),
      Split.halves b (x ++ y) = ((Split.halves b x).1 ++ (Split.halves (Split.side b x) y).1,
        (Split.halves b x).2 ++ (Split.halves (Split.side b x) y).2)
  | b, [], y => by simp [Split.halves, Split.side]
  | false, .inl a :: x, y => by
    simp only [List.cons_append, Split.halves, Split.side, halves_append false x y,
      List.cons_append]
  | true, .inl a :: x, y => by
    simp only [List.cons_append, Split.halves, Split.side, halves_append true x y,
      List.cons_append]
  | b, .inr (.ask (.inl q)) :: x, y => by
    simp only [List.cons_append, Split.halves, Split.side, halves_append false x y,
      List.cons_append]
  | b, .inr (.ask (.inr q)) :: x, y => by
    simp only [List.cons_append, Split.halves, Split.side, halves_append true x y,
      List.cons_append]
  | b, .inr (.ans (.inl q) r) :: x, y => by
    cases b <;>
    simp only [List.cons_append, Split.halves, Split.side, halves_append _ x y, List.cons_append]
  | b, .inr (.ans (.inr q) r) :: x, y => by
    cases b <;>
    simp only [List.cons_append, Split.halves, Split.side, halves_append _ x y, List.cons_append]

theorem halves_true_inl {F₁ F₂ : Sig.{0}} :
    ∀ w : List (Ev E),
      Split.halves true (w.map .inl : List (Move E (F₁ ⊕ₛ F₂))) = ([], w.map .inl)
  | [] => rfl
  | a :: w => by
    simp only [List.map_cons, Split.halves, halves_true_inl w]

theorem map_splitRoute_inl (e : Nat) (w : List (Ev sigU)) :
    (w.map .inl : List (Move sigU sigU)).map (splitRoute e) = w.map .inl := by
  induction w with
  | nil => rfl
  | cons a w ih => simp only [List.map_cons, ih]; rfl

/-- **A stage of chatter**: `c₀` followed by the shared moves `w` and the node's call `m` is a
play of the node layer `extTop e N`, at a waiting position, if `N`'s half of the routed `c₀`
continues by them in a play of `N`. -/
theorem chatter_stage {e : Nat} {N : DStrategy sigU sigU} {c₀ : List (Move sigU sigU)}
    {w : List (Ev sigU)} {m : sigU.Op} (hleg : Legal c₀)
    (hside : Split.side false (c₀.map (splitRoute e)) = true)
    (hid : (Split.halves false (c₀.map (splitRoute e))).1 ∈ Strategy.id sigU)
    (hN : (Split.halves false (c₀.map (splitRoute e))).2 ++ (w ++ [Ev.ask m]).map .inl ∈
      N.toStrategy) :
    c₀ ++ (w ++ [Ev.ask m]).map .inl ∈ (DStrategy.extTop e N).toStrategy ∧
      ∃ g, Path .idle (c₀ ++ (w ++ [Ev.ask m]).map .inl) (.wait g m) := by
  obtain ⟨x, hx⟩ := hleg
  have hr := path_route (e := e) hx
  obtain ⟨y₁, y₂, -, h₂, hrel⟩ := Split.halves_path hr (Split.Rel.idle false)
  rw [hside] at hrel
  obtain ⟨y₃, h₃⟩ := N.toStrategy.legal hN
  obtain ⟨y₂', h₂', h₄⟩ := Path.of_append h₃
  obtain rfl := Path.det h₂ h₂'
  -- the last move is the call of `m`
  have hlast : ∀ {a b : Pos sigU sigU}, Path a ((w ++ [Ev.ask m]).map .inl) b →
      ∃ q, b = .wait q m := by
    intro a b hab
    rw [List.map_append] at hab
    obtain ⟨_, -, hs⟩ := Path.concat_iff.mp hab
    cases hs with
    | call q _ => exact ⟨q, rfl⟩
  have hne : (w ++ [Ev.ask m]) ≠ [] := by simp
  -- the position of `c₀` is not idle; relabel `N`'s continuation
  have hpath : ∃ g, Path .idle (c₀ ++ (w ++ [Ev.ask m]).map .inl) (.wait g m) := by
    cases x with
    | idle =>
      change Split.Rel .idle true y₁ y₂ at hrel
      cases hrel
      exact absurd h₄ (not_path_idle_inl hne)
    | run g =>
      change Split.Rel (.run (splitQ e g)) true y₁ y₂ at hrel
      generalize hsq : splitQ e g = sq at hrel
      cases hrel with
      | runR q =>
        obtain ⟨q', rfl⟩ := hlast h₄
        exact ⟨g, hx.append (path_inl_relabel g h₄)⟩
    | wait g m₀ =>
      change Split.Rel (.wait (splitQ e g) m₀) true y₁ y₂ at hrel
      generalize hsq : splitQ e g = sq at hrel
      cases hrel with
      | waitR q _ =>
        obtain ⟨q', rfl⟩ := hlast h₄
        exact ⟨g, hx.append (path_inl_relabel g h₄)⟩
  refine ⟨DStrategy.mem_extTop_iff.mpr ⟨?_, ?_, ?_, ?_⟩, hpath⟩
  · obtain ⟨g, hg⟩ := hpath
    exact ⟨_, hg⟩
  · obtain ⟨g, hg⟩ := hpath
    exact legal_splitRoute ⟨_, hg⟩
  · rw [List.map_append, map_splitRoute_inl, halves_append, hside, halves_true_inl,
      List.append_nil]
    exact hid
  · rw [List.map_append, map_splitRoute_inl, halves_append, hside, halves_true_inl]
    exact hN

end Route

/-! ## The node's rounds along the stages -/

section Shape

variable {E F : Sig.{0}}

/-- All moves are lower moves. -/
def AllInl (A : List (Move E F)) : Prop := ∀ y ∈ A, ∃ a, y = .inl a

theorem allInl_callMoves (cs : List (Round E)) : AllInl (callMoves cs : List (Move E F)) := by
  intro y hy
  rcases y with a | a
  · exact ⟨a, rfl⟩
  · exact absurd hy (inr_not_mem_callMoves cs)

/-- The rounds before the last upper question, with lower moves only after it, are unique. -/
theorem cplay_inr_tail :
    ∀ {cl cl' : List (CRound E F)} {x x' : Ev F} {A B : List (Move E F)},
      AllInl A → AllInl B → cplay cl ++ .inr x :: A = cplay cl' ++ .inr x' :: B →
      cl = cl' ∧ x = x' ∧ A = B
  | [], [], _, _, _, _, _, _, h => by
    simp only [cplay, List.nil_append, List.cons.injEq, Sum.inr.injEq] at h
    exact ⟨rfl, h.1, h.2⟩
  | [], ⟨q, cs, a⟩ :: cl', _, _, _, _, hA, _, h => by
    simp only [cplay, List.nil_append, List.cons_append, List.cons.injEq, List.append_assoc] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨_, h⟩ := hA (.inr (.ans q a)) (List.mem_append_right _ List.mem_cons_self)
    cases h
  | ⟨q, cs, a⟩ :: cl, [], _, _, _, _, _, hB, h => by
    simp only [cplay, List.nil_append, List.cons_append, List.cons.injEq, List.append_assoc] at h
    obtain ⟨-, h⟩ := h
    obtain ⟨_, h'⟩ := hB (.inr (.ans q a)) (h ▸ List.mem_append_right _ List.mem_cons_self)
    cases h'
  | ⟨q, cs, a⟩ :: cl, ⟨q', cs', a'⟩ :: cl', _, _, _, _, hA, hB, h => by
    simp only [cplay, List.cons_append, List.cons.injEq, Sum.inr.injEq, Ev.ask.injEq,
      List.append_assoc] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, h₁, h₂⟩ := callMoves_inr_inj h
    simp only [Ev.ans.injEq, heq_eq_eq, true_and] at h₁
    subst h₁
    obtain ⟨rfl, rfl, rfl⟩ := cplay_inr_tail hA hB h₂
    exact ⟨rfl, rfl, rfl⟩

theorem callMoves_ask_prefix :
    ∀ {cs cs' : List (Round E)} {m m' : E.Op} {Z : List (Move E F)},
      callMoves cs ++ .inl (.ask m) :: Z = callMoves cs' ++ [.inl (.ask m')] → cs <+: cs'
  | [], _, _, _, _, _ => List.nil_prefix
  | ⟨a, n⟩ :: cs, [], _, _, _, h => by
    simp [callMoves] at h
  | ⟨a, n⟩ :: cs, ⟨a', n'⟩ :: cs', _, _, _, h => by
    simp only [callMoves, List.cons_append, List.cons.injEq, Sum.inl.injEq, Ev.ask.injEq] at h
    obtain ⟨rfl, h₁, h₂⟩ := h
    simp only [Ev.ans.injEq, heq_eq_eq, true_and] at h₁
    subst h₁
    exact List.cons_prefix_cons.mpr ⟨rfl, callMoves_ask_prefix h₂⟩

/-- **A waiting play continued by lower moves**: if it waits again, the complete rounds and the
pending question are the same and the lower calls grow. -/
theorem rplay_ext_inl {cl cl' : List (CRound E F)} {g g' : F.Op} {cs cs' : List (Round E)}
    {m m' : E.Op} {Y : List (Ev E)}
    (h : rplay cl g cs ++ [.inl (.ask m)] ++ Y.map .inl = rplay cl' g' cs' ++ [.inl (.ask m')]) :
    cl = cl' ∧ g = g' ∧ cs <+: cs' := by
  simp only [rplay, List.append_assoc, List.cons_append] at h
  have hA : AllInl (callMoves cs ++ (.inl (.ask m) :: Y.map .inl) : List (Move E F)) := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact allInl_callMoves cs y hy
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨_, rfl⟩
      · obtain ⟨a, -, rfl⟩ := List.mem_map.mp hy
        exact ⟨a, rfl⟩
  have hB : AllInl (callMoves cs' ++ [.inl (.ask m')] : List (Move E F)) := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact allInl_callMoves cs' y hy
    · rw [List.mem_singleton] at hy
      exact ⟨_, hy⟩
  obtain ⟨rfl, hg, hc⟩ := cplay_inr_tail hA hB h
  simp only [Ev.ask.injEq] at hg
  exact ⟨rfl, hg, callMoves_ask_prefix hc⟩

end Shape

/-! ## The read-back of a stage -/

/-- **A stage of the exporter's environment and the node above it, read back** (every profile,
under `Linked2.Adequate`, typed calls and a typed pending call): below the outer handlers of the
session `sessMoves calls outs` and the pending call `topQ j vs`, a play `tN` of the node layer
waiting on the call `m`, interacting with a play `sA` of the exporter's environment, is the
session's rounds `cl` (the node's) and the pending round with the lower calls `csN`; the
environment served them; and the importer's core instance plays rounds `ri` read back from `cl`,
then the lowered question `f` after core import calls `ics` related to `csN`, waiting on a call
`e` that lifts. -/
theorem stage_readback {P : Profile} {l : Linked2} (hl : l.Adequate) {Ii : SInst}
    (hIi : l.imp.mod.IsInst Ii)
    {calls : List (Fin l.imp.exports.length × List IVal)} {outs : List (Option (List IVal))}
    (ht : SimpleI.TypedCalls l.imp calls) (hlen : calls.length = outs.length)
    {j : Fin l.imp.exports.length} {vs : List IVal}
    (hck : ValTy.checkList l.imp.exports[j].ty.params vs = true)
    {s : List (Move (sigN 0) sigU)} {t : List (Move sigU (sigN l.compExports.length))}
    {u : List (Move (sigN 0) sigU)} {v d x : List (Move sigU sigU)}
    (h₁ : Zip u v s)
    (h₂ : Zip s t (Linked2.sessMoves l calls outs ++ [.inr (.ask (l.topQ j vs))]))
    (hu : u ∈ Strategy.ofHandler (widenH 0))
    (ht' : t ∈ Strategy.ofHandler (narrowH l.compExports.length)) (h₃ : Zip d x v)
    (hx : x ∈ Strategy.ofHandler (exportsH (envAfter 0 [l.expNode, l.impNode]) l.compExports))
    {sA tN : List (Move sigU sigU)} {gd m : sigU.Op} (hzA : Zip sA tN d) (hsA : NoInl sA)
    (htN : tN ∈ (DStrategy.extTop l.expNode.width
      (Node.denD (impSemD P) l.expNode.width l.impNode)).toStrategy)
    (htw : Path .idle tN (.wait gd m)) :
    ∃ (cl : List (CRound sigU sigU)) (csN : List (Round sigU)) (ri : List (CRound Ii.E Ii.F))
      (f : Ii.F.Op) (ics : List (Round Ii.E))
      (dss : List (List (Round (sigN l.imp.imports.length)))) (e : Ii.E.Op) (s' : Store Nat)
      (t' : Silmaril.Wasm.SingleThreaded.Thread),
      tN = rplay cl (l.exp.exports.length + j.val, .vals vs) csN ++ [.inl (.ask m)] ∧
      sA = twos (cl.flatMap (·.cs) ++ csN) ++ [.inr (.ask m)] ∧
      List.Forall₂ (fun c co => CRound.toRound c = topR l co) cl (calls.zip outs) ∧
      List.Forall₂ (RdN l Ii) ri cl ∧
      Ii.Path P (.idle Ii.store) (rplay ri f ics ++ [.inl (.ask e)]) (.waiting f s' t' e) ∧
      f.1.val = l.imp.exports[j].core ∧
      f.2.1 = (lowerArgs l.imp.exports[j].ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat ∧
      List.Forall₂ (ImpRel l.imp Ii) ics dss ∧ csN = dss.flatten.map (wireRound l) ∧
      Lifts l Ii e := by
  obtain ⟨cl, csP, rfl⟩ := exists_wplay htw
  obtain ⟨rfl, rfl⟩ := serve_wait hsA hzA
  -- the outer handlers
  obtain ⟨hLd, rfl⟩ := top_div hlen h₁ h₂ hu ht' h₃ rfl hx
  have K : List.Forall₂ (fun c co => CRound.toRound c = topR l co) cl (calls.zip outs) :=
    forall₂_of_map_eq hLd
  have hge : ∀ r ∈ cl, l.exp.exports.length ≤ r.q.1 := by
    intro r hr
    obtain ⟨co, hco⟩ := forall₂_mem_left K r hr
    have h₁ : r.q = (l.exp.exports.length + co.1.1.val, .vals co.1.2) := congrArg Sigma.fst hco
    rw [h₁]
    exact Nat.le_add_right _ _
  -- `splitH` and the pairing
  obtain ⟨a, ha, b, hb, hz₂⟩ := htN
  rw [expNode_width] at hb
  obtain ⟨yb, hyb⟩ := Strategy.mem_ofHandler.mp hb
  obtain ⟨xa, hxa⟩ := ((Strategy.id sigU).pair
    (Node.denD (impSemD P) l.expNode.width l.impNode).toStrategy).legal ha
  obtain ⟨f₂, ha₂⟩ := wait_of_zip_top hz₂ hxa hyb (path_wplay _ _ _ _)
  obtain ⟨low₁, k₁, H₁, hk₁, rfl⟩ := hc_zip_wait (oneShot_splitH _) ha₂ hyb hz₂
  rw [hc_splitH_inv H₁ hge] at ha
  simp only [splitH, Nat.not_lt.mpr (Nat.le_add_right _ _), ↓reduceIte] at hk₁
  obtain ⟨hk₁, -⟩ := Prog.call.inj hk₁
  subst hk₁
  obtain ⟨-, -, haN⟩ := ha
  rw [halves_wplay_inr] at haN
  -- the importer's node forwards the pending import call
  rw [toStrategy_node_denD, forget_impSemD, Linked2.impNode, Node.den] at haN
  obtain ⟨uN, huN, vB, hvB, hzN⟩ := haN
  rw [expNode_width] at huN
  obtain ⟨yN, hyN⟩ := Strategy.mem_ofHandler.mp huN
  obtain ⟨xv, hxv⟩ := (l.imp.toComp.denU (impSem P)).legal hvB
  obtain ⟨mB, hvw⟩ := wait_of_zip_below hzN hyN hxv (path_wplay _ _ _ _)
  obtain ⟨up₂, cs₂, rfl⟩ := exists_wplay hvw
  obtain ⟨low₂, csP', kN, H₂, H₂', hkN, he₂⟩ :=
    hb_zip_wait (oneShot_implsH _ _) hyN (path_wplay _ _ _ _) hzN
  obtain ⟨hlow₂, -, rfl, -⟩ := rplay_snoc_inj he₂
  subst hlow₂
  have G₂ : List.Forall₂ (fun x c => HBR (implsH l.exp.exports.length (wireArgs l)) x
      (downBy l.exp.exports.length c)) up₂ cl := forall₂_map_right (hb_forall₂ H₂)
  have htop : ∀ x ∈ up₂, TopI l.imp x := by
    intro x hx
    obtain ⟨co, c, hxc, hc, hco⟩ := forall₂_mem_left
      (forall₂_comp G₂ (forall₂_and_right K fun co hco => (List.of_mem_zip hco).1)) x hx
    obtain ⟨cq, ccs, ca⟩ := c
    have hcq : cq = (l.exp.exports.length + co.1.1.val, .vals co.1.2) := congrArg Sigma.fst hc
    subst hcq
    obtain ⟨q, a, cs, cs', rfl, hy, -⟩ := hxc
    cases hy
    refine ⟨co.1.1, co.1.2, ?_, ht _ hco⟩
    show ((l.exp.exports.length + co.1.1.val - l.exp.exports.length, Payload.vals co.1.2) :
      Nat × Payload) = _
    rw [Nat.add_sub_cancel_left]
  -- the importer's IR, waiting
  rw [Nat.add_sub_cancel_left] at hvB
  obtain ⟨ri, f, ics, dss, e, s', t', nm, ft, ws, F, hpath, hf₁, hf₂, hF, hcs, hft, hlw,
    -⟩ :=
    imp_wait_readback hl.impGood hIi htop hck hvB
  rw [hcs] at H₂'
  have hcsP := hrounds_wire_inv hl.wireTy dss.flatten csP H₂'
  exact ⟨cl, csP, ri, f, ics, dss, e, s', t', rfl, rfl, K, forall₂_comp F G₂, hpath, hf₁, hf₂,
    hF, hcsP, nm, ft, ws, hft, hlw⟩

/-! ## The read-back of chatter -/

theorem prefix_map {α β : Type} (f : α → β) {a b : List α} (h : a <+: b) : a.map f <+: b.map f := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t.map f, by rw [List.map_append]⟩

theorem forall₂_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {a : List α} {b : List β}, List.Forall₂ R a b →
      ∀ k (h₁ : k < a.length) (h₂ : k < b.length), R a[k] b[k]
  | _, _, .nil, _, h₁, _ => absurd h₁ (Nat.not_lt_zero _)
  | _, _, .cons h _, 0, _, _ => h
  | _, _, .cons _ t, k + 1, h₁, h₂ =>
    forall₂_getElem t k (by simpa using h₁) (by simpa using h₂)

theorem impRel_length {c : SimpleI} {I : SInst} {x : Σ e : I.E.Op, I.E.Ar e}
    {ds : List (Round (sigN c.imports.length))} (h : ImpRel c I x ds) : ds.length ≤ 1 := by
  obtain ⟨nm, ft, A, -, -, hm⟩ := h
  split at hm
  · obtain ⟨-, rfl⟩ := hm
    simp
  · obtain ⟨hk, R, rfl, -⟩ := hm
    simp

theorem flatten_length_le {c : SimpleI} {I : SInst} :
    ∀ {ics : List (Σ e : I.E.Op, I.E.Ar e)} {dss : List (List (Round (sigN c.imports.length)))},
      List.Forall₂ (ImpRel c I) ics dss → dss.flatten.length ≤ ics.length
  | _, _, .nil => le_rfl
  | _, _, .cons h t => by
    have h₁ := impRel_length h
    have h₂ := flatten_length_le t
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

/-- **Chatter read back at a deterministic profile** (under `Linked2.Adequate`). -/
theorem chatterReadBack_profile (o : GrowOracle) {l : Linked2} (hl : l.Adequate) :
    Linked2.Task.ChatterReadBack (profile o) l := by
  intro Ie Ii hIe hIi calls outs ht hlen j vs hck h
  obtain ⟨s, t, u, v, h₁, h₂, hu, ht', d, x, h₃, hd, hx⟩ := h
  obtain ⟨I, hI, L, hL, s₀, c₀, hz₀, hleg, hside, hid, hw⟩ := hd
  -- the infinite plays of the exporter's environment and of the importer's node
  have hE : Linked2.expObs (impSemD (profile o)) l = DObs.of (DStrategy.ext 0
      (DStrategy.ofHandler (maskH 0)) (Node.denD (impSemD (profile o)) 0 l.expNode)) :=
    (obs_ext _ _ _).symm
  have hI' : I ∈ (DStrategy.ext 0 (DStrategy.ofHandler (maskH 0))
      (Node.denD (impSemD (profile o)) 0 l.expNode)).inf := by
    rw [hE] at hI
    exact hI
  have hIinf := (DStrategy.ext 0 (DStrategy.ofHandler (maskH 0))
    (Node.denD (impSemD (profile o)) 0 l.expNode)).inf_isInf hI'
  have hIpl : ∀ y ∈ I, y ∈ (Linked2.expObs (impSemD (profile o)) l).plays := by
    intro y hy
    rw [hE]
    exact (DStrategy.ext 0 (DStrategy.ofHandler (maskH 0))
      (Node.denD (impSemD (profile o)) 0 l.expNode)).inf_sub hI' hy
  have hLinf := (Node.denD (impSemD (profile o)) l.expNode.width l.impNode).inf_isInf hL
  have hLpl := (Node.denD (impSemD (profile o)) l.expNode.width l.impNode).inf_sub hL
  have hnoinl : ∀ y ∈ (Linked2.expObs (impSemD (profile o)) l).plays, NoInl y := by
    rw [expObs_plays]
    exact noInl_comp (noInl_ofHandler_pure pure_maskH0)
  -- the shared moves, as one stream
  choose wk hwk using hw
  have hinr : Function.Injective (Sum.inr : Ev sigU → Move sigU sigU) := Sum.inr_injective
  have hcomp : ∀ a b, wk a <+: wk b ∨ wk b <+: wk a := by
    intro a b
    rcases hIinf.total (hwk a).2.1 (hwk b).2.1 with hab | hab
    · exact .inl (prefix_of_map_prefix hinr ((List.prefix_append_right_inj _).mp hab))
    · exact .inr (prefix_of_map_prefix hinr ((List.prefix_append_right_inj _).mp hab))
  obtain ⟨W, hW⟩ := exists_limit wk hcomp fun k => ⟨k + 1, by have := (hwk (k + 1)).1; omega⟩
  have hWpre : ∀ n, streamTake W n <+: wk n := fun n => by
    rw [streamTake_eq_take (hW n) (hwk n).1]
    exact List.take_prefix _ _
  have hIn : ∀ n, s₀ ++ (streamTake W n).map .inr ∈ I := fun n =>
    hIinf.of_prefix (hwk n).2.1 ((List.prefix_append_right_inj _).mpr (prefix_map _ (hWpre n)))
  have hLn : ∀ n, (Split.halves false (c₀.map (splitRoute l.expNode.width))).2 ++
      (streamTake W n).map .inl ∈
        (Node.denD (impSemD (profile o)) l.expNode.width l.impNode).toStrategy := fun n =>
    hLpl (hLinf.of_prefix (hwk n).2.2
      ((List.prefix_append_right_inj _).mpr (prefix_map _ (hWpre n))))
  -- the node calls at least every other move
  have halt : ∀ i, (∃ m, W i = .ask m) ∨ (∃ m, W (i + 1) = .ask m) := by
    intro i
    obtain ⟨y, hy⟩ := (Node.denD (impSemD (profile o)) l.expNode.width
      l.impNode).toStrategy.legal (hLn (i + 1 + 1))
    have e : (Split.halves false (c₀.map (splitRoute l.expNode.width))).2 ++
        (streamTake W (i + 1 + 1)).map .inl =
          ((Split.halves false (c₀.map (splitRoute l.expNode.width))).2 ++
            (streamTake W i).map .inl) ++ [.inl (W i), .inl (W (i + 1))] := by
      rw [streamTake_snoc, streamTake_snoc]
      simp
    rw [e] at hy
    obtain ⟨y₀, -, hy₂⟩ := Path.of_append hy
    rcases hWi : W i with m | ⟨m, r⟩
    · exact .inl ⟨m, rfl⟩
    · rw [hWi] at hy₂
      cases hy₂ with
      | cons s₁ hy₃ =>
        cases s₁
        rcases hWi' : W (i + 1) with m' | ⟨m', r'⟩
        · exact .inr ⟨m', rfl⟩
        · rw [hWi'] at hy₃
          cases hy₃ with
          | cons s₂ _ => cases s₂
  have hτ : ∀ n, ∃ k, 2 * n ≤ k ∧ k ≤ 2 * n + 1 ∧ ∃ m, W k = .ask m := by
    intro n
    rcases halt (2 * n) with hm | hm
    · exact ⟨2 * n, le_rfl, by omega, hm⟩
    · exact ⟨2 * n + 1, by omega, le_rfl, hm⟩
  choose τ hτ₁ hτ₂ mk hmk using hτ
  have hX : ∀ n, streamTake W (τ n + 1) = streamTake W (τ n) ++ [Ev.ask (mk n)] := fun n => by
    rw [streamTake_snoc, hmk]
  have hsAn : ∀ n, s₀ ++ (streamTake W (τ n) ++ [Ev.ask (mk n)]).map .inr ∈ I := fun n => by
    rw [← hX]
    exact hIn _
  -- the stages, read back
  have hstage : ∀ n, ∃ (cl : List (CRound sigU sigU)) (csN : List (Round sigU))
      (ri : List (CRound Ii.E Ii.F)) (f : Ii.F.Op) (ics : List (Round Ii.E))
      (dss : List (List (Round (sigN l.imp.imports.length)))) (e : Ii.E.Op) (s' : Store Nat)
      (t' : Silmaril.Wasm.SingleThreaded.Thread),
      c₀ ++ (streamTake W (τ n) ++ [Ev.ask (mk n)]).map .inl =
        rplay cl (l.exp.exports.length + j.val, .vals vs) csN ++ [.inl (.ask (mk n))] ∧
      s₀ ++ (streamTake W (τ n) ++ [Ev.ask (mk n)]).map .inr =
        twos (cl.flatMap (·.cs) ++ csN) ++ [.inr (.ask (mk n))] ∧
      List.Forall₂ (fun c co => CRound.toRound c = topR l co) cl (calls.zip outs) ∧
      List.Forall₂ (RdN l Ii) ri cl ∧
      Ii.Path (profile o) (.idle Ii.store) (rplay ri f ics ++ [.inl (.ask e)])
        (.waiting f s' t' e) ∧
      f.1.val = l.imp.exports[j].core ∧
      f.2.1 = (lowerArgs l.imp.exports[j].ty.params vs).map Silmaril.Wasm.SingleThreaded.ofFlat ∧
      List.Forall₂ (ImpRel l.imp Ii) ics dss ∧ csN = dss.flatten.map (wireRound l) ∧
      Lifts l Ii e := by
    intro n
    have hNn := hLn (τ n + 1)
    rw [hX] at hNn
    obtain ⟨htN, gd, htw⟩ := chatter_stage hleg hside hid hNn
    exact stage_readback hl hIi ht hlen hck h₁ h₂ hu ht' h₃ hx (zip_hidden hz₀ _)
      (hnoinl _ (hIpl _ (hsAn n))) htN htw
  choose cl csN ri f ics dss e s' t' hT hS hK hFG hpath hf₁ hf₂ hF hcsN hlift using hstage
  -- the node's rounds are the same at every stage, and its calls grow
  have hcl : ∀ n n', n ≤ n' → cl n = cl n' ∧ csN n <+: csN n' := by
    intro n n' hnn
    have hτle : τ n + 1 ≤ τ n' + 1 := by
      rcases Nat.eq_or_lt_of_le hnn with rfl | hlt
      · exact le_rfl
      · have := hτ₂ n
        have := hτ₁ n'
        omega
    obtain ⟨Y, hY⟩ := streamTake_prefix W hτle
    have e₁ := hT n'
    rw [← hX n', ← hY, List.map_append, ← List.append_assoc, hX n, hT n] at e₁
    obtain ⟨h₁, -, h₂⟩ := rplay_ext_inl e₁
    exact ⟨h₁, h₂⟩
  have hcl0 : ∀ n, cl n = cl 0 := fun n => ((hcl 0 n (Nat.zero_le n)).1).symm
  -- the importer's core rounds and question are the same at every stage
  have hcplay : ∀ n, ∃ z, Ii.Path (profile o) (.idle Ii.store) (cplay (ri n)) z := fun n => by
    have hp := hpath n
    simp only [rplay, List.append_assoc] at hp
    obtain ⟨z, hz, -⟩ := path_split_inst hp
    exact ⟨z, hz⟩
  have hri : ∀ n, ri n = ri 0 := fun n => by
    obtain ⟨z, hz⟩ := hcplay n
    obtain ⟨z', hz'⟩ := hcplay 0
    have F := hFG n
    rw [hcl0 n] at F
    exact rounds_eq hl.wireTy F (hFG 0) hz hz'
  have hf : ∀ n, f n = f 0 := fun n =>
    fop_ext ((hf₁ n).trans (hf₁ 0).symm) ((hf₂ n).trans (hf₂ 0).symm)
  have hpath' : ∀ n, Ii.Path (profile o) (.idle Ii.store)
      (rplay (ri 0) (f 0) (ics n) ++ [.inl (.ask (e n))]) (.waiting (f 0) (s' n) (t' n) (e n)) :=
    fun n => by
      have hp := hpath n
      rw [hri n, hf n] at hp
      exact hp
  -- its core calls grow
  have hics : ∀ n n', n ≤ n' → ics n <+: ics n' ∧ dss n <+: dss n' := by
    intro n n' hnn
    refine pend_prefix (hpath' n) (hpath' n') (hlift n') (hF n) (hF n') ?_
    rw [← hcsN n, ← hcsN n']
    exact (hcl n n' hnn).2
  have hunb : ∀ k, ∃ n, k < (ics n).length := by
    intro k
    obtain ⟨n, hn⟩ : ∃ n, n = k + (cplay (cl 0)).length + 1 := ⟨_, rfl⟩
    refine ⟨n, ?_⟩
    have e₁ := congrArg List.length (hT n)
    rw [hcl0 n] at e₁
    simp only [List.length_append, List.length_map, length_streamTake, List.length_singleton,
      length_rplay] at e₁
    have e₂ : (csN n).length ≤ (ics n).length := by
      rw [hcsN, List.length_map]
      exact flatten_length_le (hF _)
    have := hτ₁ n
    omega
  have hlen_eq : ∀ n, (dss n).length = (ics n).length := fun n => (hF n).length_eq.symm
  obtain ⟨ζ, hζ⟩ := exists_limit ics (comparable_of_mono fun a b h => (hics a b h).1) hunb
  obtain ⟨δ, hδ⟩ := exists_limit dss (comparable_of_mono fun a b h => (hics a b h).2) fun k => by
    obtain ⟨n, hn⟩ := hunb k
    exact ⟨n, by rw [hlen_eq]; exact hn⟩
  -- the session, from the first stage
  obtain ⟨sds, hOk, hr, hcsA, hF', hWT⟩ := build_rounds hl.wireTy (hFG 0) (hK 0)
  have hp0 := hpath' 0
  rw [rplay_snoc_eq] at hp0
  obtain ⟨q₁, hp₁, hp₂₃⟩ := path_split_inst hp0
  obtain ⟨u₁, rfl⟩ := idle_of_path_cplay hp₁
  obtain ⟨q₂, hp₂, hp₃⟩ := path_split_inst hp₂₃
  obtain ⟨sB, tB, rfl⟩ : ∃ sB tB, q₂ = .running (f 0) sB tB := by
    cases hp₃ with
    | cons t₁ h₁ =>
      cases t₁ with
      | ucall run callout op =>
        cases h₁
        exact ⟨_, _, rfl⟩
  -- the importer's calls along one run
  have hQ : ∀ k, ∃ q, Ii.Path (profile o) (.idle u₁)
      (.inr (.ask (f 0)) :: callMoves (streamTake ζ k)) q := by
    intro k
    obtain ⟨n, hn⟩ := hunb k
    have hp := hpath' n
    rw [rplay_snoc_eq] at hp
    obtain ⟨q₁', hp₁', hp₂₃'⟩ := path_split_inst hp
    obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Path.functional hp₁' hp₁
    have hsplit : ics n = streamTake ζ k ++ (ics n).drop k := by
      rw [streamTake_eq_take (hζ n) hn.le, List.take_append_drop]
    rw [hsplit, callMoves_app] at hp₂₃'
    have e₃ : ((.inr (.ask (f 0)) :: (callMoves (streamTake ζ k) ++ callMoves ((ics n).drop k))) ++
        [.inl (.ask (e n))] : List (Move Ii.E Ii.F)) =
          (.inr (.ask (f 0)) :: callMoves (streamTake ζ k)) ++
            (callMoves ((ics n).drop k) ++ [.inl (.ask (e n))]) := by
      simp
    rw [e₃] at hp₂₃'
    obtain ⟨q, hq, -⟩ := path_split_inst hp₂₃'
    exact ⟨q, hq⟩
  choose Q hQ using hQ
  have hQstep : ∀ m, Ii.Path (profile o) (Q m) (callMoves [ζ m]) (Q (m + 1)) := by
    intro m
    have hp := hQ (m + 1)
    rw [streamTake_snoc, callMoves_app, ← List.cons_append] at hp
    obtain ⟨q', h₁', h₂'⟩ := path_split_inst hp
    obtain rfl := Silmaril.Wasm.Game.ScalarInstance.Path.functional h₁' (hQ m)
    exact h₂'
  have hcs0 : streamTake ζ (ics 0).length = ics 0 := by
    rw [streamTake_eq_take (hζ 0) le_rfl, List.take_of_length_le le_rfl]
  have hQ0 : Q (ics 0).length = .running (f 0) sB tB := by
    have h₀ := hQ (ics 0).length
    rw [hcs0] at h₀
    exact Silmaril.Wasm.Game.ScalarInstance.Path.functional h₀ hp₂
  have hrel : ∀ k, ImpRel l.imp Ii (ζ k) (δ k) := by
    intro k
    obtain ⟨n, hn⟩ := hunb k
    have hn' : k < (dss n).length := by rw [hlen_eq]; exact hn
    have h₀ := forall₂_getElem (hF n) k hn hn'
    rw [hζ n k hn, hδ n k hn'] at h₀
    exact h₀
  -- the exporter serves them along one run
  have hwtrel : ∀ {x : Round Ii.E} {ds : List (Round (sigN l.imp.imports.length))},
      ImpRel l.imp Ii x ds → ∀ y ∈ ds, WT l y := by
    intro x ds hx y hy
    obtain ⟨nm, ft, ws, hft, hp, hck'⟩ := impRel_typed hx y hy
    exact wt_of hl.wireTy hft hp hck'
  have hwt₀ : ∀ y ∈ (sds.flatMap fun d => d.dss.flatten) ++ (dss 0).flatten, WT l y := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hWT y hy
    · obtain ⟨ds', hds, hy⟩ := List.mem_flatten.mp hy
      obtain ⟨x', hx'⟩ := forall₂_mem_right (hF 0) ds' hds
      exact hwtrel hx' y hy
  have hd0 : streamTake δ (ics 0).length = dss 0 := by
    rw [streamTake_eq_take (hδ 0) (hlen_eq 0).ge, ← hlen_eq 0, List.take_of_length_le le_rfl]
  have hplays : ∀ n, (twos ((((sds.flatMap fun d => d.dss.flatten) ++ (dss 0).flatten) ++
      (streamTake (fun k => δ ((ics 0).length + k)) n).flatten).map (wireRound l)) :
        List (Move sigU sigU)) ∈ (Linked2.expObs (impSemD (profile o)) l).plays := by
    intro n
    obtain ⟨N₁, hN₁⟩ := hunb ((ics 0).length + n)
    have hadd := streamTake_add' δ (ics 0).length n
    rw [hd0] at hadd
    have hpre : (dss 0).flatten ++ (streamTake (fun k => δ ((ics 0).length + k)) n).flatten <+:
        (dss N₁).flatten := by
      rw [← List.flatten_append, ← hadd,
        streamTake_eq_take (hδ N₁) (by rw [hlen_eq]; exact hN₁.le)]
      exact flatten_prefix (List.take_prefix _ _)
    have hmap : (((sds.flatMap fun d => d.dss.flatten) ++ (dss 0).flatten) ++
        (streamTake (fun k => δ ((ics 0).length + k)) n).flatten).map (wireRound l) <+:
          (cl 0).flatMap (·.cs) ++ csN N₁ := by
      rw [List.append_assoc, List.map_append, hcsA, hcsN N₁]
      exact (List.prefix_append_right_inj _).mpr (prefix_map _ hpre)
    have hm := hIpl _ (hsAn N₁)
    rw [hS N₁, hcl0 N₁] at hm
    exact (Linked2.expObs (impSemD (profile o)) l).plays.of_prefix hm
      ((twos_prefix hmap).trans (List.prefix_append _ _))
  obtain ⟨st, hst0, hst⟩ := exp_plays_stream hl hIe _ (fun k => δ ((ics 0).length + k)) hwt₀
    (fun k => hwtrel (hrel _)) hplays
  obtain ⟨π, hrun₁, hrun₂⟩ := expRunT_split _ _ hst0
  have hp₁' := hp₁
  rw [← hr, LinkedSessionIR.cplay_r] at hp₁'
  have hSS := sessSpec_of_idle sds calls outs hF' hlen hOk hp₁' hrun₁
  exact ⟨Ie, Ii, u₁, π, hIe, hIi, hSS, ⟨j, vs, f 0, ics 0, dss 0⟩, sB, tB, st 0, rfl, rfl,
    ⟨lowerArgs l.imp.exports[j].ty.params vs, checkLower_of_check hck, hf₁ 0, hf₂ 0, hF 0⟩,
    hp₂, hrun₂, .inr (.inr ⟨fun k => Q ((ics 0).length + k), fun k => ζ ((ics 0).length + k),
      fun k => δ ((ics 0).length + k), st, hQ0, rfl,
      fun k => ⟨hQstep ((ics 0).length + k), hrel _, hst k⟩⟩)⟩

end Silmaril.Proofs.Wasm.Component.Reference.LinkedSessionDAdeq
