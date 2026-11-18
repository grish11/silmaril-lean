module

public import Silmaril.Proofs.Wasm.Component.InstSem.Run

/-!
# Scripted components

When every core module denotes the strategy of a handler (a *script*: a fixed program for the
instantiation and for each export call), so does every component: `denIR_ofScripts` computes the
handler `compScriptH`, by the functor law `Strategy.ofHandler_comp`, the pairing law
`ofHandler_pair_ofHandler` and `ofHandler_id`. Bounding the core modules by scripts
(refinement, `denIR_mono`) bounds the component by the script of the component, whose program for
`inst` can be computed. The plays of a handler follow its programs (`handler_inst_plays`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.InstSem

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Component

variable {M : Type} [CoreModule M]

/-- A script for each core module. -/
abbrev Scripts (M : Type) [CoreModule M] : Type :=
  (m : M) → Handler (CoreIface.sig (CoreModule.imports m))
    ((CoreIface.sig (CoreModule.exports m)).withInst Unit)

/-- The core semantics of scripts. -/
def CoreSemI.ofScripts (H : Scripts M) : CoreSemI M := ⟨fun m => Strategy.ofHandler (H m)⟩

/-- The script of `extI`. -/
def extScriptH (e : Nat) (D N : Handler sigU sigUI) : Handler sigU sigUI :=
  D.comp ((Handler.copair (Handler.id sigUI) ((exH sigU Unit).comp N)).comp (instSplitH e))

mutual
/-- The script of a component. -/
def compScriptH (H : Scripts M) : Comp M → Handler sigU sigUI
  | .mk I ns xs =>
    (nodesScriptH H I.length ns ((maskH I.length).comp (readyH sigU Unit))).comp
      (liftH (exportsH (envAfter I.length ns) xs))

/-- The script of nodes extending an environment. -/
def nodesScriptH (H : Scripts M) : Nat → List (Node M) → Handler sigU sigUI →
    Handler sigU sigUI
  | _, [], D => D
  | e, n :: ns, D => nodesScriptH H (e + n.width) ns (extScriptH e D (nodeScriptH H e n))

/-- The script of a node. -/
def nodeScriptH (H : Scripts M) : Nat → Node M → Handler sigU sigUI
  | e, .core m args =>
    (implsN e args (CoreModule.imports m).length).comp
      ((H m).comp (liftH (widenH (CoreModule.exports m).length)))
  | e, .inst c args => (implsH e args).comp (compScriptH H c)
end

open Strategy

theorem extI_ofHandler (e : Nat) (D N : Handler sigU sigUI) :
    extI e (ofHandler D) (ofHandler N) = ofHandler (extScriptH e D N) := by
  rw [extI, ← ofHandler_comp, ← ofHandler_id, ofHandler_pair_ofHandler, ← ofHandler_comp,
    ← ofHandler_comp, extScriptH]

mutual
/-- **A component of scripted modules is scripted.** -/
theorem denIR_ofScripts (H : Scripts M) :
    ∀ c : Comp M, c.denIR (CoreSemI.ofScripts H) = ofHandler (compScriptH H c)
  | .mk I ns xs => by
    rw [Comp.denIR, compScriptH, withReady, ← ofHandler_comp, nodesScriptH_eq H I.length ns,
      ← ofHandler_comp]

theorem nodesScriptH_eq (H : Scripts M) : ∀ (e : Nat) (ns : List (Node M))
    (D : Handler sigU sigUI),
    denNodesI (CoreSemI.ofScripts H) e ns (ofHandler D) = ofHandler (nodesScriptH H e ns D)
  | _, [], _ => by simp only [denNodesI, nodesScriptH]
  | e, n :: ns, D => by
    rw [denNodesI, nodesScriptH, nodeScriptH_den H e n, extI_ofHandler, nodesScriptH_eq H _ ns]

theorem nodeScriptH_den (H : Scripts M) : ∀ (e : Nat) (n : Node M),
    n.denI (CoreSemI.ofScripts H) e = ofHandler (nodeScriptH H e n)
  | e, .core m args => by
    rw [Node.denI, nodeScriptH, coreNodeI, ofHandler_comp, ofHandler_comp]
    rfl
  | e, .inst c args => by
    rw [Node.denI, nodeScriptH, denIR_ofScripts H c, ofHandler_comp]
end

/-! ## Plays of scripts -/

/-- The calls a program may make, in order, are among `L` (a prefix of `L` is made, whatever
the answers). -/
inductive Prog.AsksWithin {E : Sig.{0}} {A : Type} : Prog E A → List E.Op → Prop
  | pure (a : A) (L : List E.Op) : Prog.AsksWithin (.pure a) L
  | call {m : E.Op} {k : E.Ar m → Prog E A} {L : List E.Op} :
      (∀ n, Prog.AsksWithin (k n) L) → Prog.AsksWithin (.call m k) (m :: L)

theorem lowerAsks_append {E F : Sig.{0}} : ∀ (p q : List (Move E F)),
    lowerAsks (p ++ q) = lowerAsks p ++ lowerAsks q
  | [], _ => rfl
  | .inl (.ask m) :: p, q => by simp only [List.cons_append, lowerAsks, lowerAsks_append p q]
  | .inl (.ans _ _) :: p, q => by simp only [List.cons_append, lowerAsks, lowerAsks_append p q]
  | .inr _ :: p, q => by simp only [List.cons_append, lowerAsks, lowerAsks_append p q]

section Handler

variable {E F : Sig.{0}} {h : Handler E F}

/-- From a program whose calls are among `L`, a run of the handler asks a prefix of `L` before
answering, after which it is idle. -/
theorem handler_run_asks {q : F.Op} : ∀ {P : Prog E (F.Ar q)} {L : List E.Op}
    {x : h.toReduction.toLTS.State} {p : List (Move E F)},
    Prog.AsksWithin P L → h.toReduction.toLTS.Run (.run q P) p x →
      (lowerAsks p <+: L ∧ (∀ o ∈ p, o.isLeft)) ∨
      ∃ a p₁ p₂, p = p₁ ++ .inr (.ans q a) :: p₂ ∧ lowerAsks p₁ <+: L ∧
        (∀ o ∈ p₁, o.isLeft) ∧ h.toReduction.toLTS.Run .idle p₂ x := by
  intro P L x p hP hr
  induction hP generalizing x p with
  | pure a L =>
    rcases p with _ | ⟨o, p⟩
    · exact .inl ⟨List.nil_prefix, fun _ h => by simp at h⟩
    · obtain ⟨y, hs, hr'⟩ := handler_run_cons hr
      cases hs with
      | call hc => cases hc
      | ret hd =>
        cases hd
        exact .inr ⟨a, [], p, rfl, List.nil_prefix, fun _ h => by simp at h, hr'⟩
  | @call m k L hk ih =>
    rcases p with _ | ⟨o, p⟩
    · exact .inl ⟨List.nil_prefix, fun _ h => by simp at h⟩
    · obtain ⟨y, hs, hr'⟩ := handler_run_cons hr
      cases hs with
      | ret hd => cases hd
      | call hc =>
        cases hc
        rcases p with _ | ⟨o', p⟩
        · exact .inl ⟨by simp [lowerAsks], by simp⟩
        · obtain ⟨y', hs', hr''⟩ := handler_run_cons hr'
          cases hs' with
          | resume _ _ _ n =>
            rcases ih n hr'' with ⟨h1, h2⟩ | ⟨a, p₁, p₂, rfl, h1, h2, h3⟩
            · refine .inl ⟨?_, ?_⟩
              · simpa [lowerAsks] using h1
              · intro o ho
                simp only [List.mem_cons] at ho
                rcases ho with rfl | rfl | ho
                · rfl
                · rfl
                · exact h2 o ho
            · refine .inr ⟨a, .inl (.ask m) :: .inl (.ans m n) :: p₁, p₂, rfl, ?_, ?_, h3⟩
              · simpa [lowerAsks] using h1
              · intro o ho
                simp only [List.mem_cons] at ho
                rcases ho with rfl | rfl | ho
                · rfl
                · rfl
                · exact h2 o ho

end Handler

/-! ## Plays of the protocol guard over a script -/

section Guard

variable {E F : Sig.{0}} {R : Type}

theorem lowerAsks_prefix {p q : List (Move E F)} (h : p <+: q) : lowerAsks p <+: lowerAsks q := by
  obtain ⟨t, rfl⟩ := h
  rw [lowerAsks_append]
  exact List.prefix_append _ _

theorem lowerAsks_isO {x : Move E F} (h : x.IsO) : lowerAsks [x] = [] := by
  rcases x with (_ | _) | (_ | _)
  · exact h.elim
  · rfl
  · rfl
  · rfl

theorem upper_of_left : ∀ {p : List (Move E F)}, (∀ o ∈ p, o.isLeft) → upper p = []
  | [], _ => rfl
  | .inl _ :: p, h => by
    simp only [upper, List.filterMap_cons, Sum.getRight?_inl]
    exact upper_of_left fun o ho => h o (.tail _ ho)
  | .inr _ :: _, h => by simpa using h _ (.head _)

/-- **The plays of the guard come from plays following the protocol.** -/
theorem guard_plays {σ : Strategy E (F.withInst R)} {H : Handler E (F.withInst R)}
    (hle : σ ≤ Strategy.ofHandler H) {p : List (Move E (F.withInst R))} (hp : p ∈ instGuard σ) :
    ∃ q ∈ Strategy.ofHandler H, InstProper q ∧
      (p <+: q ∨ ∃ q₀ x, p = q₀ ++ [x] ∧ q₀ <+: q ∧ x.IsO) := by
  obtain ⟨-, u, hu, hpu⟩ := hp
  rcases hu with rfl | ⟨⟨hu, hpr⟩, -⟩
  · exact ⟨[], Strategy.nil_mem _, .inl rfl, hpu⟩
  · exact ⟨u, hle hu, hpr, hpu⟩

theorem properUp_head {u : List (Ev (F.withInst R))} {x : Ev (F.withInst R)}
    (h : ProperUp (x :: u)) : x = .ask none := by
  rcases h with h | h | ⟨_, h⟩ | ⟨_, h, -⟩ <;> cases h <;> rfl

theorem properUp_after {a : InstAns R} {u : List (Ev (F.withInst R))}
    (h : ProperUp (.ask none :: Ev.ans (E := F.withInst R) none a :: u)) : ∀ x ∈ u, IsExEv x := by
  rcases h with h | h | ⟨_, h⟩ | ⟨rest, h, hr⟩
  · cases h
  · cases h
  · cases h; intro _ hx; cases hx
  · cases h; exact hr

theorem properUp_fail {r : R} {u : List (Ev (F.withInst R))}
    (h : ProperUp (.ask none :: Ev.ans (E := F.withInst R) none (.fail r) :: u)) : u = [] := by
  rcases h with h | h | ⟨_, h⟩ | ⟨rest, h, -⟩
  · cases h
  · cases h
  · cases h; rfl
  · cases h

variable {H : Handler E (F.withInst R)}

theorem handler_run_ex_rounds (hex : ∀ q, ∃ a, H (some q) = .pure a) :
    ∀ (n : Nat) (p : List (Move E (F.withInst R))) (y : H.toReduction.toLTS.State),
      p.length ≤ n → H.toReduction.toLTS.Run .idle p y → (∀ x ∈ upper p, IsExEv x) →
        lowerAsks p = []
  | _, [], _, _, _, _ => rfl
  | 0, _ :: _, _, hn, _, _ => by simp at hn
  | n + 1, o :: p, y, hn, hr, hx => by
    obtain ⟨q, rfl, hr₁⟩ := handler_run_idle_cons hr
    rcases q with _ | q
    · exact absurd (hx (.ask none) (by simp [upper])) (by simp [IsExEv])
    obtain ⟨a, ha⟩ := hex q
    rw [ha] at hr₁
    rcases p with _ | ⟨o₁, p⟩
    · rfl
    · obtain ⟨rfl, hr₂⟩ := handler_run_pure_cons hr₁
      have := handler_run_ex_rounds hex n p y (by simp at hn; omega) hr₂
        (fun x hx' => hx x (by simp [upper] at hx' ⊢; exact .inr (.inr hx')))
      simpa [lowerAsks] using this

/-- **A proper play of a script makes the calls of its program for `inst`**, when its export
calls make none. -/
theorem handler_proper_asks {L : List E.Op} (hH : Prog.AsksWithin (H none) L)
    (hex : ∀ q, ∃ a, H (some q) = .pure a) {q : List (Move E (F.withInst R))}
    (hq : q ∈ Strategy.ofHandler H) (hp : InstProper q) : lowerAsks q <+: L := by
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 hq
  rcases q with _ | ⟨o, q₁⟩
  · exact List.nil_prefix
  obtain ⟨q₀, rfl, hr⟩ := handler_run_idle_cons hy
  have h0 : q₀ = none := by
    have := properUp_head (u := upper q₁) (x := .ask q₀) (by simpa [InstProper, upper] using hp)
    cases this; rfl
  subst h0
  rcases handler_run_asks hH hr with ⟨h1, -⟩ | ⟨a, p₁, p₂, rfl, h1, h2, h3⟩
  · simpa [lowerAsks] using h1
  · have hup : upper (Sum.inr (Ev.ask (none : Option F.Op)) :: (p₁ ++ .inr (.ans none a) :: p₂) :
        List (Move E (F.withInst R))) =
        .ask none :: Ev.ans (E := F.withInst R) none a :: upper p₂ := by
      simp only [upper, List.filterMap_cons, Sum.getRight?_inr, List.filterMap_append]
      rw [show List.filterMap Sum.getRight? p₁ = upper p₁ from rfl, upper_of_left h2]
      rfl
    have hx := properUp_after (by unfold InstProper at hp; rw [hup] at hp; exact hp)
    have h4 := handler_run_ex_rounds hex _ p₂ _ le_rfl h3 hx
    simp only [lowerAsks, lowerAsks_append, h4, List.append_nil]
    exact h1

/-- **A proper play of a script that fails at once is a prefix of `[inst, fail r]`.** -/
theorem handler_proper_fail {r : R} (hH : H none = .pure (.fail r))
    {q : List (Move E (F.withInst R))} (hq : q ∈ Strategy.ofHandler H) (hp : InstProper q) :
    q <+: [askInst, ansInst (.fail r)] := by
  obtain ⟨y, hy⟩ := Strategy.mem_ofHandler.1 hq
  rcases q with _ | ⟨o, q₁⟩
  · exact List.nil_prefix
  obtain ⟨q₀, rfl, hr⟩ := handler_run_idle_cons hy
  have h0 : q₀ = none := by
    have := properUp_head (u := upper q₁) (x := .ask q₀) (by simpa [InstProper, upper] using hp)
    cases this; rfl
  subst h0
  rw [hH] at hr
  rcases q₁ with _ | ⟨o₁, q₂⟩
  · exact List.cons_prefix_cons.2 ⟨rfl, List.nil_prefix⟩
  obtain ⟨rfl, hr₁⟩ := handler_run_pure_cons hr
  rcases q₂ with _ | ⟨o₂, q₃⟩
  · exact List.prefix_refl _
  obtain ⟨q₄, rfl, -⟩ := handler_run_idle_cons hr₁
  have := properUp_fail (u := upper (.inr (.ask q₄) :: q₃)) (r := r)
    (by simpa [InstProper, upper] using hp)
  simp [upper] at this

end Guard

end Silmaril.Proofs.Wasm.Component.InstSem
