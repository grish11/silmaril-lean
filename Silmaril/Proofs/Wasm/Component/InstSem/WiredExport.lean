module

public import Silmaril.Proofs.Wasm.Component.InstSem.WiredEngine
public import Silmaril.Proofs.Wasm.Component.InstSem.Export

/-!
# An export call after the instantiation of import-wired nodes

The converse of `InstSem.Export` for one export call without calls below, after a ready
instantiation:

* `coreNodeI_ex_inv`: a core node's instantiation round followed by one export round is its
  module's, the module's import calls answered by the wiring (`implsN`), the export question
  in range (`widenH`) unless the answer is a trap;
* `extT_inv_right`: the routing layer of `extI` sends an export call at or past `e` to the new
  instance, shifted;
* `EnvInvE`, `envInvE_denNodesI`: **the environment after the nodes `pre`**: an instantiation
  round, forwarded import calls and one export round without calls below are the nodes'
  instantiations followed by that export round at the node owning the export (no import is
  owned: an import call is forwarded, so makes a call below);
* `denI_ex_inv`: on top, the component's export runs its program.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-! ## A core node -/

/-- **A core node's instantiation round and one export round are its module's**, the module's
import calls answered by the wiring; the export is in range unless it is answered by a trap. -/
theorem coreNodeI_ex_inv {C : CoreSemI M} {e : Nat} {m : M} {args : List Impl}
    {w cs : List (Call sigU)} {a : InstAns Unit} {q : sigU.Op} {n : Option Payload}
    (h : roundsMoves [instRound (F := sigU) w a, exRound (R := Unit) (⟨q, cs, n⟩ : Round sigU sigU)] ∈
      coreNodeI C e m args) :
    ∃ xs₁ xs₂ : List (Round sigU (sigN (CoreModule.imports m).length)),
      (∀ y ∈ xs₁ ++ xs₂, Prog.Runs (implsN e args (CoreModule.imports m).length y.q) y.cs y.a) ∧
      w = allCalls xs₁ ∧ cs = allCalls xs₂ ∧
      ((n = none ∧ xs₂ = []) ∨ ∃ hq : q.1 < (CoreModule.exports m).length,
        roundsMoves [instRound (F := CoreIface.sig (CoreModule.exports m)) (xs₁.map Round.call) a,
          exRound (R := Unit) (⟨(⟨q.1, hq⟩, q.2), xs₂.map Round.call, n⟩ :
            Round (sigN (CoreModule.imports m).length) (CoreIface.sig (CoreModule.exports m)))] ∈
          C.sem m) := by
  obtain ⟨s, hs, t, ht, hz⟩ := h
  obtain ⟨_, ps⟩ := (Strategy.ofHandler _).legal hs
  obtain ⟨_, pt⟩ := Strategy.legal _ ht
  obtain ⟨ss, ts, rfl, rfl, hZ⟩ := zip_rounds_inv _ ps pt hz
  obtain ⟨xs₁, _, _, rfl, rfl, hc₁, hZ₁⟩ := zipR_cons_inv hZ
  obtain ⟨xs₂, _, _, rfl, rfl, hc₂, hZ₂⟩ := zipR_cons_inv hZ₁
  cases hZ₂
  rw [List.append_nil] at hs
  simp only [exRound] at hc₁ hc₂
  refine ⟨xs₁, xs₂, runs_of_ofHandler_rounds hs, hc₁, hc₂, ?_⟩
  obtain ⟨s', hs', t', ht', hz'⟩ := ht
  obtain ⟨_, ps'⟩ := Strategy.legal _ hs'
  obtain ⟨_, pt'⟩ := Strategy.legal _ ht'
  obtain ⟨us, vs, rfl, rfl, hZ'⟩ := zip_rounds_inv _ ps' pt' hz'
  obtain ⟨us₁, _, _, rfl, rfl, hd₁, hZ'₁⟩ := zipR_cons_inv hZ'
  obtain ⟨us₂, _, _, rfl, rfl, hd₂, hZ'₂⟩ := zipR_cons_inv hZ'₁
  cases hZ'₂
  rw [List.append_nil] at hs'
  have hr := runs_of_ofHandler_rounds ht'
  have h₁ := hr _ (.head _)
  have h₂ := hr _ (.tail _ (.head _))
  simp only [liftH, exRound, instRound] at h₁ h₂
  simp only at hd₁ hd₂
  -- the instantiation round is forwarded
  rcases us₁ with _ | ⟨⟨uq, ucs, ua⟩, _ | _⟩
  · cases h₁
  · cases h₁ with
    | call h₁ =>
      cases h₁
      simp only [allCalls, List.append_nil] at hd₁
      subst hd₁
      -- the export round
      obtain ⟨k, pl⟩ := q
      simp only [widenH] at h₂
      by_cases hk : k < (CoreModule.exports m).length
      · simp only [hk, ↓reduceDIte, Prog.interp] at h₂
        rcases us₂ with _ | ⟨⟨vq, vcs, va⟩, _ | _⟩
        · cases h₂
        · cases h₂ with
          | call h₂ =>
            cases h₂
            simp only [allCalls, List.append_nil] at hd₂
            subst hd₂
            refine .inr ⟨hk, ?_⟩
            simp only [roundsMoves, List.append_nil, List.singleton_append] at hs' ⊢
            exact hs'
        · cases h₂ with
          | call h₂ => cases h₂
      · simp only [hk, ↓reduceDIte, Prog.interp] at h₂
        rcases us₂ with _ | ⟨_, _⟩
        · cases h₂
          refine .inl ⟨rfl, ?_⟩
          cases xs₂ with
          | nil => rfl
          | cons x xs => simp [allCalls] at hd₂
        · cases h₂
  · cases h₁ with
    | call h₁ => cases h₁

/-! ## The routing layer -/

theorem zipR_append_inv {E F G : Sig.{0}} :
    ∀ {rs₁ rs₂ : List (Round E G)} {ss : List (Round E F)} {ts : List (Round F G)},
      ZipR (rs₁ ++ rs₂) ss ts →
      ∃ ss₁ ss₂ ts₁ ts₂, ss = ss₁ ++ ss₂ ∧ ts = ts₁ ++ ts₂ ∧ ZipR rs₁ ss₁ ts₁ ∧ ZipR rs₂ ss₂ ts₂
  | [], _, _, _, h => ⟨[], _, [], _, rfl, rfl, .nil, h⟩
  | r :: rs₁, rs₂, _, _, h => by
    obtain ⟨xs, ss', ts', rfl, rfl, hc, hz⟩ := zipR_cons_inv (rs := rs₁ ++ rs₂) h
    obtain ⟨ss₁, ss₂, ts₁, ts₂, rfl, rfl, h₁, h₂⟩ := zipR_append_inv hz
    exact ⟨xs ++ ss₁, ss₂, _ :: ts₁, ts₂, by rw [List.append_assoc], rfl, .cons r xs hc h₁, h₂⟩

theorem lefts_append {E F₁ F₂ : Sig.{0}} :
    ∀ l₁ l₂ : List (Round E F₁ ⊕ Round E F₂), lefts (l₁ ++ l₂) = lefts l₁ ++ lefts l₂
  | [], _ => rfl
  | .inl _ :: l, l₂ => by simp only [List.cons_append, lefts, lefts_append l l₂]
  | .inr _ :: l, l₂ => by simp only [List.cons_append, lefts, lefts_append l l₂]

theorem rights_append {E F₁ F₂ : Sig.{0}} :
    ∀ l₁ l₂ : List (Round E F₁ ⊕ Round E F₂), rights (l₁ ++ l₂) = rights l₁ ++ rights l₂
  | [], _ => rfl
  | .inl _ :: l, l₂ => by simp only [List.cons_append, rights, rights_append l l₂]
  | .inr _ :: l, l₂ => by simp only [List.cons_append, rights, rights_append l l₂]

/-- **The routing layer of `extI`, an export call at or past `e`**: after a ready instantiation
and export calls below `e` (forwarded to the environment), an export call at or past `e` is the
new instance's, shifted by `e`, its calls made export calls below. -/
theorem extT_inv_right {e : Nat} {N : Strategy sigU sigUI} {c c₂ : List (Call sigUI)}
    {X : List (Round sigUI sigUI)} {q : sigU.Op} {n : Option Payload}
    (hX : ∀ x ∈ X, ∃ q : sigU.Op, x.q = some q ∧ q.1 < e) (hq : e ≤ q.1)
    (h : roundsMoves (⟨none, c, .ready⟩ :: X ++ [⟨some q, c₂, n⟩]) ∈ extT e N) :
    (∀ x ∈ X, x.cs = [⟨x.q, x.a⟩]) ∧
      ∃ ys ys₂ : List (Call sigU),
        roundsMoves [instRound (F := sigU) ys .ready,
          exRound (R := Unit) (⟨(q.1 - e, q.2), ys₂, n⟩ : Round sigU sigU)] ∈ N ∧
        c = ⟨none, .ready⟩ :: ys.map exCall ∧ c₂ = ys₂.map exCall := by
  obtain ⟨s, hs, t, ht, hz⟩ := h
  obtain ⟨_, ps⟩ := Strategy.legal _ hs
  obtain ⟨_, pt⟩ := Strategy.legal _ ht
  obtain ⟨us, vs, rfl, rfl, hZ⟩ := zip_rounds_inv _ ps pt hz
  have hv := runs_of_ofHandler_rounds ht
  obtain ⟨xs₀, us', vs', rfl, rfl, hc, hZ'⟩ := zipR_cons_inv hZ
  obtain ⟨uX, uf, vX, vf, rfl, rfl, hZX, hZf⟩ := zipR_append_inv hZ'
  obtain ⟨xf, _, _, rfl, rfl, hcf, hZf'⟩ := zipR_cons_inv hZf
  cases hZf'
  simp only at hc hcf
  subst hc hcf
  have hvX : ∀ v ∈ vX, Prog.Runs (instSplitH e v.q) v.cs v.a :=
    fun v h => hv v (.tail _ (List.mem_append_left _ h))
  have huX := splitH_ex_inv hZX hvX hX
  subst huX
  -- the final round goes right
  have hf := hv _ (.tail _ (List.mem_append_right _ (.head _)))
  have hqe : ¬ q.1 < e := by omega
  simp only [instSplitH, hqe, ↓reduceIte] at hf
  rcases xf with _ | ⟨⟨fq, fcs, fa⟩, _ | _⟩
  · cases hf
  · cases hf with
    | call hf' =>
      cases hf'
      -- the instantiation round
      have h₀ := hv _ (.head _)
      simp only [instSplitH] at h₀
      rcases xs₀ with _ | ⟨⟨uq₁, ucs₁, ua₁⟩, xs₀⟩
      · cases h₀
      · simp only [List.map_cons, Round.call] at h₀
        cases h₀ with
        | @call _ _ n₁ _ _ h₁ =>
          rcases n₁ with _ | r
          · rcases xs₀ with _ | ⟨⟨uq₂, ucs₂, ua₂⟩, xs₀⟩
            · cases h₁
            · cases h₁ with
              | @call _ _ n₂ _ _ h₂ =>
                rcases xs₀ with _ | ⟨_, _⟩
                · cases h₂
                  obtain ⟨hL, hR⟩ := mem_pair_rounds_inv hs
                  simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append,
                    List.nil_append, unsided] at hL hR
                  simp only [lefts, rights, lefts_append, rights_append, (lefts_map_leftR X).1,
                    (lefts_map_leftR X).2, List.nil_append] at hL hR
                  have hid := id_rounds_inv hL
                  refine ⟨fun x hx => hid x (.tail _ (List.mem_append_left _ hx)), ?_⟩
                  obtain ⟨s', hs', t', ht', hz'⟩ := hR
                  obtain ⟨_, ps'⟩ := Strategy.legal _ hs'
                  obtain ⟨_, pt'⟩ := Strategy.legal _ ht'
                  obtain ⟨hrs, ns, rfl, rfl, hZ₂⟩ := zip_rounds_inv
                    [(⟨none, ucs₂, InstAns.ready⟩ : Round sigUI sigUI), ⟨some (q.1 - e, q.2), fcs, fa⟩] ps' pt' hz'
                  obtain ⟨xs₂, _, _, rfl, rfl, hc₂, hz₂⟩ := zipR_cons_inv hZ₂
                  obtain ⟨xs₃, _, _, rfl, rfl, hc₃, hz₃⟩ := zipR_cons_inv hz₂
                  cases hz₃
                  rw [List.append_nil] at hs'
                  have hrun := runs_of_ofHandler_rounds hs'
                  have hcall₂ := exH_rounds_calls fun h hh => hrun h (List.mem_append_left _ hh)
                  have hcall₃ := exH_rounds_calls fun h hh => hrun h (List.mem_append_right _ hh)
                  simp only at hc₂ hc₃
                  refine ⟨xs₂.map Round.call, xs₃.map Round.call, ?_, ?_, ?_⟩
                  · simpa only [roundsMoves, List.append_nil, instRound, exRound] using ht'
                  · have h₁' := hid _ (.head _)
                    simp only at h₁'
                    simp only [allCalls, List.append_nil, hc₂, hcall₂, h₁', List.singleton_append]
                  · simp only [allCalls, List.append_nil, hc₃, hcall₃]
                · cases h₂
          · rcases xs₀ with _ | ⟨_, _⟩
            · cases h₁
            · cases h₁
  · cases hf with
    | call hf' => cases hf'

/-! ## The environment invariant for one export call -/

/-- The number of functions the core nodes `ps` export. -/
def coreWidth (ps : List (M × List Impl)) : Nat := (ps.map fun p => (CoreModule.exports p.1).length).sum

theorem coreWidth_append (ps qs : List (M × List Impl)) :
    coreWidth (ps ++ qs) = coreWidth ps + coreWidth qs := by
  simp [coreWidth]

theorem forall₂_snoc {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β} {x : α} {y : β}, List.Forall₂ R l₁ l₂ → R x y →
      List.Forall₂ R (l₁ ++ [x]) (l₂ ++ [y])
  | [], [], _, _, .nil, h => .cons h .nil
  | _ :: _, _ :: _, _, _, .cons h₁ h₂, h => .cons h₁ (forall₂_snoc h₂ h)

/-- **A ready node-by-node instantiation, split by node.** -/
theorem nodesInst_ready_split {C : CoreSemI M} {n : Nat} :
    ∀ {ps : List (M × List Impl)} {w : List (Call sigU)} {a : InstAns Unit},
      NodesInst C n ps w a → a = .ready →
      ∃ ts : List (List (Call sigU)), w = ts.flatten ∧
        List.Forall₂ (fun p tj => instPlay (F := sigU) tj .ready ∈ coreNodeI C n p.1 p.2) ps ts := by
  intro ps w a h
  induction h with
  | nil => exact fun _ => ⟨[], rfl, .nil⟩
  | failed _ _ => exact fun h => by cases h
  | @step pre x w w' a h hx ih =>
    intro ha
    subst ha
    obtain ⟨ts, rfl, hF⟩ := ih rfl
    exact ⟨ts ++ [w'], by simp, forall₂_snoc hF hx⟩

/-- **The environment after the nodes `pre`, with one export call**: a play of an instantiation
round, forwarded import calls and one export round without calls below answered with a value is
the nodes' instantiations, in order, and the export round at the node `j` owning the export
(after the `n` imports and the exports of the nodes before `j`), without calls below. -/
def EnvInvE (C : CoreSemI M) (n : Nat) (pre : List (M × List Impl)) (D : Strategy sigU sigUI) :
    Prop :=
  ∀ (w : List (Call sigU)) (zs : List (Round sigU sigU)) (q : sigU.Op) (y : Payload),
    (∀ z ∈ zs, z.q.1 < n) →
    roundsMoves (instRound (F := sigU) w .ready :: zs.map (exRound (R := Unit)) ++
        [exRound (R := Unit) (⟨q, [], some y⟩ : Round sigU sigU)]) ∈ D →
    ∃ ts : List (List (Call sigU)), w = ts.flatten ∧
      List.Forall₂ (fun p tj => instPlay (F := sigU) tj .ready ∈ coreNodeI C n p.1 p.2) pre ts ∧
      ∃ (j : Nat) (p : M × List Impl) (tj : List (Call sigU)), pre[j]? = some p ∧ ts[j]? = some tj ∧
        n + coreWidth (pre.take j) ≤ q.1 ∧
        q.1 < n + coreWidth (pre.take j) + (CoreModule.exports p.1).length ∧
        roundsMoves [instRound (F := sigU) tj .ready, exRound (R := Unit)
          (⟨(q.1 - (n + coreWidth (pre.take j)), q.2), [], some y⟩ : Round sigU sigU)] ∈
          coreNodeI C n p.1 p.2

/-- The imports alone own no export: an import call is forwarded, so it makes a call below. -/
theorem envInvE_base (C : CoreSemI M) (n : Nat) :
    EnvInvE C n [] (withReady (R := Unit) (Strategy.ofHandler (maskH n))) := by
  intro w zs q y _ h
  exfalso
  rw [withReady, ← Strategy.ofHandler_comp] at h
  have hr := runs_of_ofHandler_rounds h
  have h₁ := hr (exRound ⟨q, [], some y⟩) (List.mem_append_right _ (.head _))
  obtain ⟨q₁, q₂⟩ := q
  by_cases hq : q₁ < n
  · simp only [exRound, Handler.comp, readyH, Prog.interp, maskH, Target.prog, hq, ite_true,
      Prog.bind] at h₁
    cases h₁
  · simp only [exRound, Handler.comp, readyH, Prog.interp, maskH, Target.prog, hq] at h₁
    cases h₁

theorem allCalls_append {E F : Sig.{0}} : ∀ (xs ys : List (Round E F)),
    allCalls (xs ++ ys) = allCalls xs ++ allCalls ys
  | [], _ => rfl
  | x :: xs, ys => by simp only [List.cons_append, allCalls, allCalls_append xs ys, List.append_assoc]

theorem getElem?_append_singleton {α : Type} {l : List α} {j : Nat} {a x : α} (h : l[j]? = some a) :
    (l ++ [x])[j]? = some a := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1, h]

theorem take_append_singleton {α : Type} {l : List α} {j : Nat} {a x : α} (h : l[j]? = some a) :
    (l ++ [x]).take j = l.take j := by
  rw [List.take_append_of_le_length (List.getElem?_eq_some_iff.1 h).1.le]

/-- **One node**: the invariant with one export call is carried from `D` to `extI e D N` for an
import-wired core node `N`, `e` the size of the environment `D`. -/
theorem envInvE_extI {C : CoreSemI M} {n : Nat} {pre : List (M × List Impl)}
    {D : Strategy sigU sigUI} {m : M} {args : List Impl} (hD : EnvInv C n pre D)
    (hE : EnvInvE C n pre D) (hs : ScopedList n args) :
    EnvInvE C n (pre ++ [(m, args)])
      (extI (n + coreWidth pre) D (coreNodeI C (n + coreWidth pre) m args)) := by
  intro w zs q y hzs h
  obtain ⟨s, hsD, t, ht, hz⟩ := h
  obtain ⟨_, ps⟩ := D.legal hsD
  obtain ⟨_, pt⟩ := Strategy.legal _ ht
  obtain ⟨ss, ts, rfl, rfl, hZ⟩ := zip_rounds_inv _ ps pt hz
  obtain ⟨xs₀, ss', ts', rfl, rfl, hc, hZ'⟩ := zipR_cons_inv hZ
  obtain ⟨sZ, sf, tZ, tf, rfl, rfl, hZZ, hZf⟩ := zipR_append_inv hZ'
  obtain ⟨xf, _, _, rfl, rfl, hcf, hZf'⟩ := zipR_cons_inv hZf
  cases hZf'
  simp only [exRound] at hc hcf
  subst hc
  have hX : ∀ x ∈ tZ, ∃ q : sigU.Op, x.q = some q ∧ q.1 < n + coreWidth pre := by
    intro x hx
    have hq : x.q ∈ tZ.map (·.q) := List.mem_map_of_mem hx
    rw [zipR_qs hZZ, List.map_map] at hq
    obtain ⟨z, hz, hzq⟩ := List.mem_map.1 hq
    exact ⟨z.q, hzq.symm, by have := hzs z hz; omega⟩
  have hne : n ≤ n + coreWidth pre := Nat.le_add_right _ _
  by_cases hq : q.1 < n + coreWidth pre
  · -- the export goes to the environment
    have hX' : ∀ x ∈ tZ ++ [⟨some q, xf.map Round.call, some y⟩],
        ∃ q : sigU.Op, x.q = some q ∧ q.1 < n + coreWidth pre := by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hX x hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact ⟨q, rfl, hq⟩
    obtain ⟨hfwd, hcase⟩ := extT_inv hX' (by simpa only [instRound, exRound] using ht)
    have hsZ := zipR_fwd hZZ fun t ht => hfwd t (List.mem_append_left _ ht)
    subst hsZ
    have hff := hfwd _ (List.mem_append_right _ (.head _))
    simp only at hff
    rcases xf with _ | ⟨⟨fq, fcs, fa⟩, _ | _⟩
    · simp at hff
    · simp only [List.map_cons, List.map_nil, Round.call, List.cons.injEq,
        and_true] at hff
      cases hff
      simp only [allCalls, List.append_nil] at hcf
      subst hcf
      rcases hcase with ⟨r, hr, -⟩ | ⟨ys, hN, hc₀⟩
      · cases hr
      · rcases xs₀ with _ | ⟨⟨xq, xcs, xa⟩, ds⟩
        · simp at hc₀
        · simp only [List.map_cons, Round.call, List.cons.injEq] at hc₀
          obtain ⟨hx₀, hds⟩ := hc₀
          cases hx₀
          obtain ⟨ds', rfl, hys⟩ := ex_rounds_of_calls hds
          subst hys
          have hlt := coreNodeI_calls_lt hs hN
          have hzs' : ∀ z ∈ ds' ++ zs, z.q.1 < n := by
            intro z hz
            rcases List.mem_append.1 hz with hz | hz
            · exact hlt _ (List.mem_map_of_mem hz)
            · exact hzs z hz
          have hplay : roundsMoves (instRound (F := sigU) xcs .ready ::
              (ds' ++ zs).map (exRound (R := Unit)) ++
              [exRound (R := Unit) (⟨q, [], some y⟩ : Round sigU sigU)]) ∈ D := by
            simpa only [List.cons_append, roundsMoves_append, List.map_append, roundsMoves,
              List.append_assoc, exRound, instRound, List.nil_append, List.append_nil] using hsD
          obtain ⟨-, h₂⟩ := hD xcs .ready (ds' ++ zs) hzs'
            (D.of_prefix hplay (by rw [roundsMoves_append]; exact List.prefix_append _ _))
          obtain ⟨tsD, rfl, hF, j, p, tj, hpj, htj, hle, hlt', hnode⟩ :=
            hE xcs (ds' ++ zs) q y hzs' hplay
          have hcalls : allCalls ds' = ds'.map Round.call :=
            allCalls_fwd fun d hd => h₂ d (List.mem_append_left _ hd)
          rw [coreNodeI_scoped C hs hne, ← instPlay_eq] at hN
          refine ⟨tsD ++ [ds'.map Round.call], ?_, forall₂_snoc hF hN, j, p, tj,
            getElem?_append_singleton hpj, getElem?_append_singleton htj, ?_, ?_, ?_⟩
          · simp only [allCalls, allCalls_map_exRound, hcalls, List.flatten_append,
              List.flatten_cons, List.flatten_nil, List.append_nil]
          · rwa [take_append_singleton hpj]
          · rwa [take_append_singleton hpj]
          · rwa [take_append_singleton hpj]
    · simp at hff
  · -- the export goes to the new node
    obtain ⟨hfwd, ys, ys₂, hN, hc₀, hc₂⟩ := extT_inv_right (q := q) (n := some y) hX (by omega)
      (by simpa only [instRound, exRound, List.cons_append] using ht)
    have hsZ := zipR_fwd hZZ hfwd
    subst hsZ
    obtain ⟨xs₁, xs₂, hruns, hys, hys₂, hcase⟩ := coreNodeI_ex_inv hN
    obtain ⟨hk, -⟩ : ∃ hk : q.1 - (n + coreWidth pre) < (CoreModule.exports m).length, True := by
      rcases hcase with ⟨h, -⟩ | ⟨hk, -⟩
      · cases h
      · exact ⟨hk, trivial⟩
    have hlt := allCalls_lt hs hruns
    rcases xs₀ with _ | ⟨⟨xq, xcs, xa⟩, ds⟩
    · simp at hc₀
    · simp only [List.map_cons, Round.call, List.cons.injEq] at hc₀
      obtain ⟨hx₀, hds⟩ := hc₀
      cases hx₀
      obtain ⟨ds', rfl, hys'⟩ := ex_rounds_of_calls hds
      obtain ⟨df', rfl, hys₂'⟩ := ex_rounds_of_calls hc₂
      have hzs' : ∀ z ∈ ds' ++ zs ++ df', z.q.1 < n := by
        intro z hz
        rcases List.mem_append.1 hz with hz | hz
        · rcases List.mem_append.1 hz with hz | hz
          · have : z.call ∈ ys := hys' ▸ List.mem_map_of_mem hz
            rw [hys] at this
            exact hlt _ (by rw [allCalls_append]; exact List.mem_append_left _ this)
          · exact hzs z hz
        · have : z.call ∈ ys₂ := hys₂' ▸ List.mem_map_of_mem hz
          rw [hys₂] at this
          exact hlt _ (by rw [allCalls_append]; exact List.mem_append_right _ this)
      obtain ⟨hNI, h₂⟩ := hD xcs .ready (ds' ++ zs ++ df') hzs' (by
        simpa only [List.cons_append, roundsMoves_append, List.map_append, roundsMoves,
          List.append_assoc, exRound, instRound, List.nil_append, List.append_nil] using hsD)
      have hdf : allCalls df' = df'.map Round.call :=
        allCalls_fwd fun d hd => h₂ d (List.mem_append_right _ hd)
      have hcalls : allCalls ds' = ds'.map Round.call :=
        allCalls_fwd fun d hd => h₂ d (List.mem_append_left _ (List.mem_append_left _ hd))
      rw [allCalls_map_exRound, hdf] at hcf
      have hdf0 : df' = [] := by
        cases df' with
        | nil => rfl
        | cons d ds => simp at hcf
      subst hdf0
      simp only [List.map_nil] at hys₂'
      subst hys₂' hys'
      obtain ⟨tsD, rfl, hF⟩ := nodesInst_ready_split hNI rfl
      rw [coreNodeI_scoped C hs hne] at hN
      have hNi : instPlay (F := sigU) (ds'.map Round.call) .ready ∈ coreNodeI C n m args := by
        rw [instPlay_eq]
        refine (coreNodeI C n m args).of_prefix hN ?_
        simp only [roundsMoves, List.append_nil]
        exact List.prefix_append _ _
      have hlen : tsD.length = pre.length := hF.length_eq.symm
      refine ⟨tsD ++ [ds'.map Round.call], ?_, forall₂_snoc hF hNi, pre.length, (m, args),
        ds'.map Round.call, by simp, by simp [← hlen], ?_, ?_, ?_⟩
      · simp only [allCalls, allCalls_map_exRound, hcalls, List.flatten_append,
          List.flatten_cons, List.flatten_nil, List.append_nil]
      · simp only [List.take_left']; omega
      · simp only [List.take_left']; omega
      · rw [List.take_left' rfl]
        exact hN

theorem envInvE_denNodesI {C : CoreSemI M} {n : Nat} :
    ∀ (ps : List (M × List Impl)) {pre : List (M × List Impl)} {D : Strategy sigU sigUI},
      EnvInv C n pre D → EnvInvE C n pre D → ImportWired n ps →
      EnvInvE C n (pre ++ ps) (denNodesI C (n + coreWidth pre) (coreNodes ps) D)
  | [], pre, D, _, hE, _ => by
    simpa only [List.append_nil, coreNodes, List.map_nil, denNodesI] using hE
  | (m, args) :: ps, pre, D, hD, hE, hw => by
    have hs := hw _ (.head _)
    have hD' := envInv_extI (m := m) hD hs (Nat.le_add_right n (coreWidth pre))
    have hE' := envInvE_extI (m := m) hD hE hs
    have := envInvE_denNodesI ps hD' hE' (fun p h => hw p (.tail _ h))
    rw [coreWidth_append] at this
    simpa only [coreNodes, List.map_cons, denNodesI, Node.denI, Node.width, List.append_assoc,
      List.singleton_append, coreWidth, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, Nat.add_assoc] using this

/-! ## On top -/

theorem runs_interp_exH {A : Type} :
    ∀ {P : Prog sigU A} {cs : List (Call sigUI)} {a : A},
      Prog.Runs (P.interp (exH sigU Unit)) cs a →
      ∃ cs' : List (Call sigU), cs = cs'.map exCall ∧ Prog.Runs P cs' a
  | .pure _, _, _, h => by cases h; exact ⟨[], rfl, .pure _⟩
  | .call m k, _, _, h => by
    simp only [Prog.interp, Handler.ofHom, exHom, Prog.bind] at h
    cases h with
    | @call _ _ n cs _ h =>
      obtain ⟨cs', rfl, h'⟩ := runs_interp_exH h
      exact ⟨⟨m, n⟩ :: cs', rfl, .call h'⟩

/-- **An export call after a ready instantiation of an import-wired component**: the component's
export `j` runs its program, making the export calls `ds` of the nodes' environment, each without
calls below, after the nodes' instantiation. -/
theorem denI_ex_inv {C : CoreSemI M} {I : Iface} {ps : List (M × List Impl)}
    {xs : List Export} {t : List (Call sigU)} {q : sigU.Op} {n : Option Payload}
    (h : instPlay (F := sigU) t .ready ++ [askEx q, ansEx q n] ∈
      (Comp.mk I (coreNodes ps) xs).denI C) :
    ∃ ds : List (Round sigU sigU), (∀ d ∈ ds, d.cs = []) ∧
      Prog.Runs (exportsH (envAfter I.length (coreNodes ps)) xs q) (ds.map Round.call) n ∧
      roundsMoves (instRound (F := sigU) t .ready :: ds.map (exRound (R := Unit))) ∈
        denNodesI C I.length (coreNodes ps) (withReady (Strategy.ofHandler (maskH I.length))) := by
  have h' := instGuard_le _ h
  have he : instPlay (F := sigU) t (InstAns.ready (R := Unit)) ++ [askEx q, ansEx q n] =
      roundsMoves [instRound (F := sigU) t .ready,
        exRound (R := Unit) (⟨q, [], n⟩ : Round sigU sigU)] := by
    rw [instPlay_eq]
    simp only [roundsMoves, exRound, Round.moves, callEvs, List.map_nil, List.nil_append,
      List.append_nil]
    rfl
  rw [Comp.denIR, he] at h'
  obtain ⟨s, hs, t', ht, hz⟩ := h'
  obtain ⟨_, ps'⟩ := Strategy.legal _ hs
  obtain ⟨_, pt⟩ := Strategy.legal _ ht
  obtain ⟨ss, ts, rfl, rfl, hZ⟩ := zip_rounds_inv _ ps' pt hz
  obtain ⟨xs₁, _, _, rfl, rfl, hc₁, hZ₁⟩ := zipR_cons_inv hZ
  obtain ⟨xs₂, _, _, rfl, rfl, hc₂, hZ₂⟩ := zipR_cons_inv hZ₁
  cases hZ₂
  rw [List.append_nil] at hs
  have hr := runs_of_ofHandler_rounds ht
  have h₁ := hr _ (.head _)
  have h₂ := hr _ (.tail _ (.head _))
  simp only [instRound, exRound, liftH] at h₁ h₂ hc₁ hc₂
  rcases xs₁ with _ | ⟨⟨xq, xcs, xa⟩, _ | _⟩
  · cases h₁
  · cases h₁ with
    | call h₁ =>
      cases h₁
      simp only [allCalls, List.append_nil] at hc₁
      subst hc₁
      obtain ⟨cs', hcs', hrun⟩ := runs_interp_exH h₂
      obtain ⟨ds, rfl, rfl⟩ := ex_rounds_of_calls hcs'
      refine ⟨ds, fun d hd => ?_, hrun, ?_⟩
      · rw [allCalls_map_exRound] at hc₂
        exact allCalls_eq_nil hc₂.symm d hd
      · simpa only [List.singleton_append, roundsMoves, instRound] using hs
  · cases h₁ with
    | call h₁ => cases h₁

/-- **An export call after a ready instantiation of an import-wired component, at the node owning
it**: if the component's export makes one call of the environment's function `r` (on `pl`), answered
with a value `y`, that function is export `r - o` of a node `j`, whose instantiation round (after
the nodes before it, from the `n` imports, offset `o`) is followed by that export round without
calls below; the nodes' instantiations split `t`. -/
theorem denI_ex_node {C : CoreSemI M} {I : Iface} {ps : List (M × List Impl)}
    {xs : List Export} (hw : ImportWired I.length ps) {t : List (Call sigU)} {q : sigU.Op}
    {n : Option Payload} {r : Nat} {pl : Payload}
    (hone : ∀ cs, Prog.Runs (exportsH (envAfter I.length (coreNodes ps)) xs q) cs n →
      ∃ y, cs = [⟨(r, pl), some y⟩])
    (h : instPlay (F := sigU) t .ready ++ [askEx q, ansEx q n] ∈
      (Comp.mk I (coreNodes ps) xs).denI C) :
    ∃ y : Payload,
      Prog.Runs (exportsH (envAfter I.length (coreNodes ps)) xs q) [⟨(r, pl), some y⟩] n ∧
      ∃ ts : List (List (Call sigU)), t = ts.flatten ∧
      List.Forall₂ (fun p tj => instPlay (F := sigU) tj .ready ∈ coreNodeI C I.length p.1 p.2)
        ps ts ∧
      ∃ (j : Nat) (p : M × List Impl) (tj : List (Call sigU)), ps[j]? = some p ∧ ts[j]? = some tj ∧
        I.length + coreWidth (ps.take j) ≤ r ∧
        r < I.length + coreWidth (ps.take j) + (CoreModule.exports p.1).length ∧
        roundsMoves [instRound (F := sigU) tj .ready, exRound (R := Unit)
          (⟨(r - (I.length + coreWidth (ps.take j)), pl), [], some y⟩ : Round sigU sigU)] ∈
          coreNodeI C I.length p.1 p.2 := by
  obtain ⟨ds, hds, hrun, hD⟩ := denI_ex_inv h
  obtain ⟨y, hc⟩ := hone _ hrun
  refine ⟨y, hc ▸ hrun, ?_⟩
  rcases ds with _ | ⟨⟨dq, dcs, da⟩, _ | _⟩
  · cases hc
  · simp only [List.map_cons, List.map_nil, Round.call, List.cons.injEq, and_true] at hc
    cases hc
    have hdcs : dcs = [] := hds _ (.head _)
    subst hdcs
    have hE := envInvE_denNodesI ps (envInv_base C I.length) (envInvE_base C I.length) hw
    simp only [List.nil_append, coreWidth, List.map_nil, List.sum_nil, Nat.add_zero] at hE
    exact hE t [] (r, pl) y (fun _ h => nomatch h) (by
      simpa only [List.map_nil, List.map_cons, List.cons_append, List.nil_append] using hD)
  · simp at hc

/-! ## At an engine semantics -/

section Engine

open Silmaril.Wasm.Component.Param Silmaril.Proofs.Wasm.Component.InstEngine
open Silmaril.Wasm.Component.Reference (Engine)
open Silmaril.Wasm.Game (liftMove)

variable {E : Engine} {imps exps : CoreIface}

/-- **A running export call answered with a value** is a run with the import calls `cs`
(`StartRunI`) to returned values. -/
theorem run_running_inv {I : EInstance E} {q : (sigN exps.length).Op} {y : Payload} :
    ∀ (cs : List (Σ _ : (sigN imps.length).Op, Option Payload)) {s : E.Store Nat}
      {t : E.Thread Nat} {z : EState E imps.length exps.length},
    (engineLTS E I imps exps).Run (.running q s t)
      ((callEvs (E := sigN imps.length) cs).map .inl ++ [.inr (.ans q (some y))]) z →
    ∃ (c' : E.Config Nat) (ys : List Flat), StartRunI E imps (s, t) cs c' ∧
      E.status c'.1 c'.2 = .returned (.values ys) ∧ y = .flat ys
  | [], s, t, z, h => by
    simp only [callEvs, List.map_nil, List.nil_append] at h
    rcases run_cases h with ⟨hl, -⟩ | ⟨y', ⟨m, hm, -⟩, -⟩ | ⟨o, l', y', hl, ⟨m, hm, hs⟩, -⟩
    · cases hl
    · cases hm
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
      cases hm
      cases hs with
      | oret run final => exact ⟨_, _, .nil run, final, rfl⟩
  | ⟨m₀, n₀⟩ :: cs, s, t, z, h => by
    simp only [callEvs, List.map_cons, List.cons_append] at h
    rcases run_cases h with ⟨hl, -⟩ | ⟨y', ⟨m, hm, -⟩, -⟩ | ⟨o, l', y', hl, ⟨m, hm, hs⟩, hr⟩
    · cases hl
    · cases hm
    · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
      cases hm
      cases hs with
      | ucall run callout hh =>
        rcases run_cases hr with ⟨hl, -⟩ | ⟨y'', ⟨m', hm', -⟩, -⟩ |
          ⟨o', l'', y'', hl', ⟨m', hm', hs'⟩, hr'⟩
        · cases hl
        · cases hm'
        · obtain ⟨rfl, rfl⟩ := List.cons.inj hl'
          cases hm'
          cases hs' with
          | uret r =>
            obtain ⟨c', ys, hrun, hf, rfl⟩ := run_running_inv cs hr'
            exact ⟨c', ys, .call run callout hh n₀ hrun, hf, rfl⟩

/-- **An export round answered with a value** invokes the export and runs it, with the import
calls `cs`, to returned values. -/
theorem engine_round_inv {I : EInstance E} {x : EState E imps.length exps.length}
    {q : (sigN exps.length).Op} {cs : List (Σ _ : (sigN imps.length).Op, Option Payload)}
    {y : Payload} {s : E.Store Nat} {z : EState E imps.length exps.length}
    (hx : x = .idle s)
    (h : (engineLTS E I imps exps).Run x
      (.inr (.ask q) :: ((callEvs (E := sigN imps.length) cs).map .inl ++
        [.inr (.ans q (some y))])) z) :
    ∃ (a : E.FuncAddr) (xs : List Flat) (c' : E.Config Nat) (ys : List Flat),
      callee? I.addrs exps q = some (a, xs) ∧ StartRunI E imps (s, E.invoke a xs) cs c' ∧
      E.status c'.1 c'.2 = .returned (.values ys) ∧ y = .flat ys := by
  subst hx
  rcases run_cases h with ⟨hl, -⟩ | ⟨y', ⟨m, hm, -⟩, -⟩ | ⟨o, l', y', hl, ⟨m, hm, hs⟩, hr⟩
  · cases hl
  · cases hm
  · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
    cases hm
    cases hs with
    | call hc =>
      obtain ⟨c', ys, hrun, hf, rfl⟩ := run_running_inv cs hr
      exact ⟨_, _, c', ys, hc, hrun, hf, rfl⟩
    | refuse hc =>
      exfalso
      rcases cs with _ | ⟨⟨m₁, n₁⟩, cs⟩
      · simp only [callEvs, List.map_nil, List.nil_append] at hr
        rcases run_cases hr with ⟨hl, -⟩ | ⟨y'', ⟨m', hm', -⟩, -⟩ |
          ⟨o', l'', y'', hl', ⟨m', hm', hs'⟩, -⟩
        · cases hl
        · cases hm'
        · obtain ⟨rfl, rfl⟩ := List.cons.inj hl'
          cases hm'
          cases hs'
      · simp only [callEvs, List.map_cons, List.cons_append] at hr
        rcases run_cases hr with ⟨hl, -⟩ | ⟨y'', ⟨m', hm', -⟩, -⟩ |
          ⟨o', l'', y'', hl', ⟨m', hm', hs'⟩, -⟩
        · cases hl
        · cases hm'
        · obtain ⟨rfl, rfl⟩ := List.cons.inj hl'
          cases hm'
          cases hs'

/-- **An engine instance's instantiation round and one export round answered with a value**:
the instance exists; its start function (if any) runs with the instantiation's import calls and
returns, leaving the store `s'`; the export is invoked in `s'` and runs, with the export round's
import calls, to returned values. -/
theorem engineI_ex_inv {I : Option (IInstance E)}
    {cs cs₂ : List (Σ _ : (sigN imps.length).Op, Option Payload)} {q : (sigN exps.length).Op}
    {y : Payload}
    (h : roundsMoves [instRound (F := sigN exps.length) cs .ready,
      exRound (R := Unit) (⟨q, cs₂, some y⟩ : Round (sigN imps.length) (sigN exps.length))] ∈
      engineStrategyI E I imps exps) :
    ∃ J : IInstance E, I = some J ∧ ∃ s' : E.Store Nat,
      ((J.start = none ∧ cs = [] ∧ s' = J.store) ∨
        ∃ f c' ys, J.start = some f ∧ StartRunI E imps (J.store, E.invoke f []) cs c' ∧
          E.status c'.1 c'.2 = .returned (.values ys) ∧ s' = c'.1) ∧
      ∃ (a : E.FuncAddr) (xs : List Flat) (c'' : E.Config Nat) (ys : List Flat),
        callee? J.addrs exps q = some (a, xs) ∧ StartRunI E imps (s', E.invoke a xs) cs₂ c'' ∧
        E.status c''.1 c''.2 = .returned (.values ys) ∧ y = .flat ys := by
  have he : roundsMoves [instRound (F := sigN exps.length) cs (InstAns.ready (R := Unit)),
      exRound (R := Unit) (⟨q, cs₂, some y⟩ : Round (sigN imps.length) (sigN exps.length))] =
      (askInst :: ((callEvs (E := sigN imps.length) cs).map .inl ++ ansInst .ready ::
        (.inr (.ask (some q)) :: (callEvs (E := sigN imps.length) cs₂).map .inl))) ++
        [.inr (.ans (some q) (some y))] := by
    simp only [roundsMoves, instRound, exRound, Round.moves, List.append_nil, List.cons_append,
      List.append_assoc]
    rfl
  rw [he] at h
  obtain ⟨z, hz⟩ := trace_of_mem_ofLTS h (by simp [Move.IsP])
  simp only [List.cons_append, List.append_assoc] at hz
  obtain ⟨y₀, hy, hr⟩ := run_fresh_inv hz
  -- the moves after `ready`, lifted
  have hlift : (.inr (.ask (some q)) :: ((callEvs (E := sigN imps.length) cs₂).map .inl ++
      [.inr (.ans (some q) (some y))]) :
        List (Move (sigN imps.length) ((sigN exps.length).withInst Unit))) =
      (.inr (.ask q) :: ((callEvs (E := sigN imps.length) cs₂).map .inl ++
        [.inr (.ans q (some y))]) : List (Move (sigN imps.length) (sigN exps.length))).map
        (liftMove (R := Unit)) := by
    simp only [List.map_cons, List.map_append, List.map_map, List.map_nil]
    rfl
  have hround : ∀ (s : E.Store Nat) {z'}, (engineLTSI E I imps exps).Run (.ready (.idle s))
      (.inr (.ask (some q)) :: ((callEvs (E := sigN imps.length) cs₂).map .inl ++
        [.inr (.ans (some q) (some y))])) z' →
      ∃ (a : E.FuncAddr) (xs : List Flat) (c'' : E.Config Nat) (ys : List Flat),
        callee? (addrsOf I) exps q = some (a, xs) ∧ StartRunI E imps (s, E.invoke a xs) cs₂ c'' ∧
        E.status c''.1 c''.2 = .returned (.values ys) ∧ y = .flat ys := by
    intro s z' hrun
    rw [hlift] at hrun
    obtain ⟨p, y', hp, -, hr'⟩ := run_ready_inv s _ hrun
    obtain rfl := List.map_injective_iff.2 liftMove_injective hp
    exact engine_round_inv rfl hr'
  cases hy with
  | @start J f hI hf =>
    obtain ⟨c', ys, hrun, hst, hrest⟩ := run_starting_inv cs hr
    obtain ⟨a, xs, c'', ys', hc, hrun', hst', rfl⟩ := hround c'.1 hrest
    rw [hI] at hc
    exact ⟨J, hI, c'.1, .inr ⟨f, c', ys, hf, hrun, hst, rfl⟩, a, xs, c'', ys', hc, hrun', hst', rfl⟩
  | @noStart J hI hf =>
    rcases cs with _ | ⟨c₀, cs⟩
    · simp only [callEvs, List.map_nil, List.nil_append] at hr
      rcases run_readying_inv hr with hl | ⟨rest, hl, hr'⟩
      · cases hl
      · obtain ⟨-, rfl⟩ := List.cons.inj hl
        obtain ⟨a, xs, c'', ys', hc, hrun', hst', rfl⟩ := hround J.store hr'
        rw [hI] at hc
        exact ⟨J, hI, J.store, .inl ⟨hf, rfl, rfl⟩, a, xs, c'', ys', hc, hrun', hst', rfl⟩
    · exfalso
      obtain ⟨m₀, n₀⟩ := c₀
      simp only [callEvs, List.map_cons, List.cons_append] at hr
      rcases run_readying_inv hr with hl | ⟨rest, hl, -⟩
      · cases hl
      · cases (List.cons.inj hl).1
  | noInst hI =>
    exfalso
    rcases cs with _ | ⟨⟨m₀, n₀⟩, cs⟩
    · simp only [callEvs, List.map_nil, List.nil_append] at hr
      rcases run_failing_inv hr with hl | ⟨rest, hl⟩
      · cases hl
      · exact ansInst_ne_fail (List.cons.inj hl).1
    · simp only [callEvs, List.map_cons, List.cons_append] at hr
      rcases run_failing_inv hr with hl | ⟨rest, hl⟩
      · cases hl
      · cases (List.cons.inj hl).1

end Engine

end Silmaril.Proofs.Wasm.Component.InstSem
