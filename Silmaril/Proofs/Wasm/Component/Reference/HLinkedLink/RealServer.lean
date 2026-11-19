module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink.Pend
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.Back
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.RetT
public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionObj.InfT2

/-!
# The host-realizable server against the passthrough server (proofs)

The host-realizable server `HLinked2.serverR` (state: the calls `R` refused since the last answer)
and the passthrough server `HLinked2.serverO` serve the same calls; they differ only on host
calls:

* `round_RO`: a round of `serverR` is a round of `serverO` with the same question and answer whose
  log is either the same and a `VisRun` (one visible refusal or legal answer, or no host call), or
  a forced refusal that `serverR` hid (a trap answer);
* `round_OR`, `round_OR_hidden`: conversely a `serverO` round whose log is a `VisRun` from `R` is a
  `serverR` round with that log, and one refusing a call forced at `R` is a `serverR` round with
  no call.

Lifted to sequences of rounds (`rounds_RO`, `rounds_OR`, `rounds_OR_hidden`; a trap answer may only
come last, `TrapLast`) and to infinite services (`inf_RO`, `inf_OR`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink

open Silmaril.Games Silmaril.Games.Abstract
open Silmaril.Games.Abstract.StratObs (satP CallPre)
open Silmaril.Games.Abstract.SessionLink (linkS served servedLog InfServe logTake linkEnd)
open Silmaril.Games.Abstract.StratThread (Rounds)
open Silmaril.Games.Abstract.StratSession (pairS pairEndL pairEndR)
open Silmaril.Games.Abstract.SessionExt (routeS foldS)
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Game (ScalarInstance)
open Silmaril.Wasm.Execution.Core (Store)
open Silmaril.Wasm.Component.Reference.HLinked2 (VisRun Forced hostLegal hostTripleR)

variable {P : Profile} {l : HLinked2} {Ie : ScalarInstance}


/-! ## Rounds of the host-realizable server -/

/-- The end of an exporter round in the host-realizable server's store. -/
def expEndR (R : List (sigN l.host.length).Op) : End (Store Nat) (Payload ⊕ PUnit.{1}) →
    End (List (sigN l.host.length).Op × Store Nat) (Payload ⊕ PUnit.{1})
  | .ret x s => .ret x (R, s)
  | .trap => .trap
  | .div => .div

theorem serverR_fst (σ : List (sigN l.host.length).Op × Store Nat) (a : Nat × Payload) :
    (l.serverR P Ie).1 σ a = (fun x => (x.1, SessionRoute.mapEnd foldS x.2)) ''
      (pairS (hostTripleR l.host) (l.expTripleH P Ie)).1 σ (l.route a) := rfl

theorem legal_not_forced {h : Iface} {R : List (sigN h.length).Op} {m : (sigN h.length).Op}
    {p : Payload} (hm : m ∉ R) (hl : hostLegal h m (some p)) : ¬ Forced h R m := by
  rintro (hf | hf)
  · exact hm hf
  · rcases p with ys | us
    · exact hl
    · exact hf ⟨us, hl⟩

/-- **A routed host question of the host-realizable server.** -/
theorem mem_serverR_inl {R : List (sigN l.host.length).Op} {π : Store Nat} {a : Nat × Payload} {m : (sigN l.host.length).Op}
    (h : l.route a = .inl m)
    {x : List (Call (sigN l.host.length)) × End (List (sigN l.host.length).Op × Store Nat) (Payload ⊕ PUnit.{1})} :
    x ∈ (l.serverR P Ie).1 (R, π) a ↔
      (Forced l.host R m ∧ x = ([], .ret (.inr PUnit.unit) (R, π))) ∨
      (¬ Forced l.host R m ∧ x = ([⟨m, none⟩], .ret (.inr PUnit.unit) (m :: R, π))) ∨
      (∃ p, m ∉ R ∧ hostLegal l.host m (some p) ∧
        x = ([⟨m, some p⟩], .ret (.inl p) ([], π))) := by
  rw [serverR_fst, h]
  change x ∈ (fun x => (x.1, SessionRoute.mapEnd foldS x.2)) ''
    ((fun x => (x.1, pairEndL π x.2)) '' (hostTripleR l.host).1 R m) ↔ _
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    rcases hz with ⟨hf, rfl⟩ | ⟨hf, rfl⟩ | ⟨p, hm, hl, rfl⟩
    · exact .inl ⟨hf, rfl⟩
    · exact .inr (.inl ⟨hf, rfl⟩)
    · exact .inr (.inr ⟨p, hm, hl, rfl⟩)
  · rintro (⟨hf, rfl⟩ | ⟨hf, rfl⟩ | ⟨p, hm, hl, rfl⟩)
    · exact ⟨_, ⟨_, .inl ⟨hf, rfl⟩, rfl⟩, rfl⟩
    · exact ⟨_, ⟨_, .inr (.inl ⟨hf, rfl⟩), rfl⟩, rfl⟩
    · exact ⟨_, ⟨_, .inr (.inr ⟨p, hm, hl, rfl⟩), rfl⟩, rfl⟩

/-- **Any other question is a round of the exporter's triple**, the refusals kept. -/
theorem mem_serverR_inr {R : List (sigN l.host.length).Op} {π : Store Nat} {a a' : Nat × Payload}
    (h : l.route a = .inr a')
    {x : List (Call (sigN l.host.length)) × End (List (sigN l.host.length).Op × Store Nat) (Payload ⊕ PUnit.{1})} :
    x ∈ (l.serverR P Ie).1 (R, π) a ↔
      x.1 = [] ∧ ∃ e, ([], e) ∈ ((Simple.expSpec l.exp Ie).sessTripleS P).1 π a' ∧
        x.2 = expEndR R e := by
  rw [serverR_fst, h]
  change x ∈ (fun x => (x.1, SessionRoute.mapEnd foldS x.2)) ''
    ((fun x => (x.1, pairEndR R x.2)) ''
      {x : List (Call (sigN l.host.length)) × End (Store Nat) (Payload ⊕ PUnit.{1}) |
        x.1 = [] ∧ ([], x.2) ∈ ((Simple.expSpec l.exp Ie).sessTripleS P).1 π a'}) ↔ _
  constructor
  · rintro ⟨y, ⟨z, ⟨hz, hm⟩, rfl⟩, rfl⟩
    refine ⟨hz, z.2, hm, ?_⟩
    rcases z with ⟨c, ⟨x, s⟩ | _ | _⟩ <;> simp [pairEndR, SessionRoute.mapEnd, expEndR, foldS_inr]
  · rintro ⟨h1, e, he, h2⟩
    refine ⟨(x.1, pairEndR R e), ⟨([], e), ⟨rfl, he⟩, by rw [h1]⟩, ?_⟩
    rcases x with ⟨c, x₂⟩
    simp only at h1 h2
    subst h1 h2
    rcases e with ⟨x, s⟩ | _ | _ <;> simp [pairEndR, SessionRoute.mapEnd, expEndR, foldS_inr]

theorem serverR_inf (σ : List (sigN l.host.length).Op × Store Nat) (a : Nat × Payload) :
    (l.serverR P Ie).2.2 σ a = ∅ := by
  show Sum.elim ((hostTripleR l.host).2.2 σ.1) ((l.expTripleH P Ie).2.2 σ.2) (l.route a) = ∅
  rcases l.route a with m | a' <;> rfl

/-- **The host-realizable server forces only its unforced host calls.** -/
theorem satP_serverR {R : List (sigN l.host.length).Op} {π : Store Nat} {a : Nat × Payload}
    {x : List (Call (sigN l.host.length)) × (sigN l.host.length).Op} (h : x ∈ satP (l.serverR P Ie) (R, π) a) :
    x.1 = [] ∧ l.route a = .inl x.2 ∧ ¬ Forced l.host R x.2 := by
  obtain ⟨c, m'⟩ := x
  rcases hp : l.route a with m | a'
  · have hpend : (l.serverR P Ie).2.1 (R, π) a = {x | ¬ Forced l.host R m ∧ x = ([], m)} := by
      show Sum.elim ((hostTripleR l.host).2.1 R) ((l.expTripleH P Ie).2.1 π) (l.route a) = _
      rw [hp]
      rfl
    rcases h with h | ⟨d, m'', hd, n, c', hc⟩ | ⟨d, e, hd, n, c', hc⟩ | ⟨ω, hω, -⟩
    · rw [hpend] at h
      obtain ⟨hf, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, rfl, hf⟩
    · rw [hpend] at hd
      obtain ⟨-, hd⟩ := hd
      simp only [Prod.mk.injEq] at hd
      obtain ⟨rfl, -⟩ := hd
      simp at hc
    · rcases (mem_serverR_inl hp).1 hd with ⟨-, hd⟩ | ⟨hf, hd⟩ | ⟨p, hm, hl, hd⟩ <;>
        simp only [Prod.mk.injEq] at hd <;> obtain ⟨rfl, -⟩ := hd
      · simp at hc
      · cases c with
        | nil =>
          simp only [List.nil_append, List.cons.injEq, Sigma.mk.injEq] at hc
          obtain ⟨⟨rfl, -⟩, -⟩ := hc
          exact ⟨rfl, rfl, hf⟩
        | cons z c => simp at hc
      · cases c with
        | nil =>
          simp only [List.nil_append, List.cons.injEq, Sigma.mk.injEq] at hc
          obtain ⟨⟨rfl, -⟩, -⟩ := hc
          exact ⟨rfl, rfl, legal_not_forced hm hl⟩
        | cons z c => simp at hc
    · rw [serverR_inf] at hω
      exact hω.elim
  · rcases h with h | ⟨d, m'', hd, -⟩ | ⟨d, e, hd, n, c', hc⟩ | ⟨ω, hω, -⟩
    · change (c, m') ∈ Sum.elim ((hostTripleR l.host).2.1 R) ((l.expTripleH P Ie).2.1 π)
        (l.route a) at h
      rw [hp] at h
      exact h.elim
    · change (d, m'') ∈ Sum.elim ((hostTripleR l.host).2.1 R) ((l.expTripleH P Ie).2.1 π)
        (l.route a) at hd
      rw [hp] at hd
      exact hd.elim
    · have := ((mem_serverR_inr hp).1 hd).1
      simp only at this
      subst this
      simp at hc
    · rw [serverR_inf] at hω
      exact hω.elim

/-! ## One round against the passthrough server -/

/-- **A round of the host-realizable server is a passthrough round**, visible or with a forced
refusal hidden. -/
theorem round_RO {R R' : List (sigN l.host.length).Op} {π π' : Store Nat} {a : Nat × Payload}
    {x : Payload ⊕ PUnit.{1}} {c : List (Call (sigN l.host.length))}
    (h : (c, End.ret x (R', π')) ∈ (l.serverR P Ie).1 (R, π) a) :
    ∃ cO, (cO, End.ret x (PUnit.unit, π')) ∈ (l.serverO P Ie).1 (PUnit.unit, π) a ∧
      ((c = cO ∧ VisRun l.host R c R') ∨
        (x = .inr PUnit.unit ∧ c = [] ∧ R' = R ∧ ∃ m, cO = [⟨m, none⟩] ∧ Forced l.host R m)) := by
  rcases hr : l.route a with m | a'
  · rcases (mem_serverR_inl hr).1 h with ⟨hf, hx⟩ | ⟨hf, hx⟩ | ⟨p, hm, hl, hx⟩ <;>
      simp only [Prod.mk.injEq, End.ret.injEq] at hx
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hx
      exact ⟨_, (mem_serverO_inl hr).2 ⟨none, rfl⟩, .inr ⟨rfl, rfl, rfl, m, rfl, hf⟩⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hx
      exact ⟨_, (mem_serverO_inl hr).2 ⟨none, rfl⟩, .inl ⟨rfl, .refuse hf (.nil _)⟩⟩
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := hx
      exact ⟨_, (mem_serverO_inl hr).2 ⟨some p, rfl⟩, .inl ⟨rfl, .answer hm hl (.nil _)⟩⟩
  · obtain ⟨hc, e, he, h2⟩ := (mem_serverR_inr hr).1 h
    simp only at hc h2
    subst hc
    rcases e with ⟨x', s⟩ | _ | _ <;> simp only [expEndR, End.ret.injEq, Prod.mk.injEq] at h2
    · obtain ⟨rfl, rfl, rfl⟩ := h2
      exact ⟨[], (mem_serverO_inr hr).2 ⟨rfl, _, he, rfl⟩, .inl ⟨rfl, .nil _⟩⟩
    all_goals cases h2

/-- **A passthrough round with a visible log is a round of the host-realizable server.** -/
theorem round_OR {R R' : List (sigN l.host.length).Op} {π π' : Store Nat} {a : Nat × Payload}
    {x : Payload ⊕ PUnit.{1}} {c : List (Call (sigN l.host.length))}
    (h : (c, End.ret x (PUnit.unit, π')) ∈ (l.serverO P Ie).1 (PUnit.unit, π) a)
    (hv : VisRun l.host R c R') : (c, End.ret x (R', π')) ∈ (l.serverR P Ie).1 (R, π) a := by
  rcases hr : l.route a with m | a'
  · obtain ⟨n, hn⟩ := (mem_serverO_inl hr).1 h
    simp only [Prod.mk.injEq, End.ret.injEq] at hn
    obtain ⟨rfl, rfl, -, rfl⟩ := hn
    refine (mem_serverR_inl hr).2 ?_
    cases hv with
    | refuse hF hv => cases hv; exact .inr (.inl ⟨hF, rfl⟩)
    | answer hm hl hv => cases hv; exact .inr (.inr ⟨_, hm, hl, rfl⟩)
  · obtain ⟨hc, e, he, h2⟩ := (mem_serverO_inr hr).1 h
    simp only at hc h2
    subst hc
    cases hv
    refine (mem_serverR_inr hr).2 ⟨rfl, e, he, ?_⟩
    rcases e with ⟨x', s⟩ | _ | _ <;> simp only [expEnd, End.ret.injEq, Prod.mk.injEq] at h2
    · obtain ⟨rfl, -, rfl⟩ := h2
      rfl
    all_goals cases h2

/-- **A passthrough round refusing a forced call is a host-realizable round without a call.** -/
theorem round_OR_hidden {R : List (sigN l.host.length).Op} {π π' : Store Nat} {a : Nat × Payload}
    {x : Payload ⊕ PUnit.{1}} {m : (sigN l.host.length).Op}
    (h : ([⟨m, none⟩], End.ret x (PUnit.unit, π')) ∈ (l.serverO P Ie).1 (PUnit.unit, π) a)
    (hf : Forced l.host R m) :
    ([], End.ret x (R, π')) ∈ (l.serverR P Ie).1 (R, π) a ∧ x = .inr PUnit.unit ∧ π' = π := by
  rcases hr : l.route a with m' | a'
  · obtain ⟨n, hn⟩ := (mem_serverO_inl hr).1 h
    simp only [Prod.mk.injEq, End.ret.injEq, List.cons.injEq, Sigma.mk.injEq, and_true] at hn
    obtain ⟨⟨rfl, hn⟩, rfl, -, rfl⟩ := hn
    cases eq_of_heq hn
    exact ⟨(mem_serverR_inl hr).2 (.inl ⟨hf, rfl⟩), rfl, rfl⟩
  · have := ((mem_serverO_inr hr).1 h).1
    simp at this

theorem div_RO {R : List (sigN l.host.length).Op} {π : Store Nat} {a : Nat × Payload}
    {c : List (Call (sigN l.host.length))} :
    (c, End.div) ∈ (l.serverR P Ie).1 (R, π) a ↔
      (c, End.div) ∈ (l.serverO P Ie).1 (PUnit.unit, π) a := by
  rcases hr : l.route a with m | a'
  · rw [mem_serverR_inl hr, mem_serverO_inl hr]
    simp
  · rw [mem_serverR_inr hr, mem_serverO_inr hr]
    constructor
    · rintro ⟨hc, e, he, h2⟩
      refine ⟨hc, e, he, ?_⟩
      rcases e with ⟨x', s⟩ | _ | _ <;> first | rfl | cases h2
    · rintro ⟨hc, e, he, h2⟩
      refine ⟨hc, e, he, ?_⟩
      rcases e with ⟨x', s⟩ | _ | _ <;> first | rfl | cases h2

/-! ## Sequences of rounds -/

/-- A list of served calls whose trap answers come last. -/
def TrapLast (L : List (Call sigS)) : Prop :=
  ∀ L₁ z L₂, L = L₁ ++ z :: L₂ → z.2 = Sum.inr PUnit.unit → L₂ = []

theorem TrapLast.tail {z : Call sigS} {L : List (Call sigS)} (h : TrapLast (z :: L)) :
    TrapLast L := fun L₁ z' L₂ hL hz => h (z :: L₁) z' L₂ (by rw [hL]; rfl) hz

theorem served_eq_nil {E : Sig.{0}} {A B : Type} {rs : List (A × List (Call E) × (B ⊕ PUnit.{1}))}
    (h : served rs = []) : rs = [] := List.map_eq_nil_iff.1 h

/-- **Rounds of the host-realizable server are passthrough rounds**, all visible, or visible up
to a hidden forced refusal answering the last call. -/
theorem rounds_RO : ∀ {σ σ' : List (sigN l.host.length).Op × Store Nat}
    {rs : List ((Nat × Payload) × List (Call (sigN l.host.length)) × (Payload ⊕ PUnit.{1}))},
    Rounds (l.serverR P Ie) σ rs σ' → TrapLast (served rs) →
    ∃ rsO, Rounds (l.serverO P Ie) (PUnit.unit, σ.2) rsO (PUnit.unit, σ'.2) ∧
      served rsO = served rs ∧
      ((servedLog rsO = servedLog rs ∧ VisRun l.host σ.1 (servedLog rs) σ'.1) ∨
        (∃ m, servedLog rsO = servedLog rs ++ [⟨m, none⟩] ∧
          VisRun l.host σ.1 (servedLog rs) σ'.1 ∧ Forced l.host σ'.1 m ∧
          ∃ L₁ a, served rs = L₁ ++ [⟨a, .inr PUnit.unit⟩]))
  | _, _, _, .nil _, _ => ⟨[], .nil _, rfl, .inl ⟨rfl, .nil _⟩⟩
  | σ, σ', _, @Rounds.cons _ _ _ _ _ _ s₁ _ a c b rs hr hrs, hT => by
    obtain ⟨cO, hO, hcase⟩ := round_RO (R := σ.1) (π := σ.2) (R' := s₁.1) (π' := s₁.2) hr
    rcases hcase with ⟨rfl, hv⟩ | ⟨rfl, rfl, hR, m, rfl, hf⟩
    · obtain ⟨rsO, hRO, hsv, hcase'⟩ := rounds_RO hrs hT.tail
      refine ⟨(a, c, b) :: rsO, .cons hO hRO, congrArg (List.cons _) hsv, ?_⟩
      rcases hcase' with ⟨hlog, hv'⟩ | ⟨m, hlog, hv', hf', L₁, a', hL⟩
      · exact .inl ⟨congrArg (_ ++ ·) hlog, HLinkedSessionObj.visRun_append hv hv'⟩
      · refine .inr ⟨m, by show c ++ servedLog rsO = (c ++ servedLog rs) ++ _; rw [hlog, List.append_assoc], HLinkedSessionObj.visRun_append hv hv', hf',
          ⟨a, b⟩ :: L₁, a', by show _ :: served rs = _; rw [hL]; rfl⟩
    · have hnil : served rs = [] := hT [] ⟨a, .inr PUnit.unit⟩ (served rs) rfl rfl
      obtain rfl := served_eq_nil hnil
      cases hrs
      refine ⟨[(a, [⟨m, none⟩], .inr PUnit.unit)], .cons hO (.nil _), rfl, .inr ⟨m, rfl, ?_,
        ?_, [], a, rfl⟩⟩
      · rw [hR]; exact .nil _
      · rw [hR]; exact hf

/-- **Passthrough rounds with a visible log are rounds of the host-realizable server.** -/
theorem rounds_OR : ∀ {σO σO' : PUnit.{1} × Store Nat}
    {rsO : List ((Nat × Payload) × List (Call (sigN l.host.length)) × (Payload ⊕ PUnit.{1}))},
    Rounds (l.serverO P Ie) σO rsO σO' → ∀ {R R' : List (sigN l.host.length).Op}, VisRun l.host R (servedLog rsO) R' →
    ∃ rsR, Rounds (l.serverR P Ie) (R, σO.2) rsR (R', σO'.2) ∧ served rsR = served rsO ∧
      servedLog rsR = servedLog rsO
  | _, _, _, .nil _, _, _, hv => by cases hv; exact ⟨[], .nil _, rfl, rfl⟩
  | _, _, _, @Rounds.cons _ _ _ _ _ _ s₁ _ a c b rs hr hrs, R, R', hv => by
    obtain ⟨R₁, hv₁, hv₂⟩ := HLinkedSessionObj.visRun_split hv
    have h1 := round_OR (R' := R₁) hr hv₁
    obtain ⟨rsR, hRR, hsv, hlog⟩ := rounds_OR hrs hv₂
    exact ⟨(a, c, b) :: rsR, .cons h1 hRR, congrArg (List.cons _) hsv, congrArg (_ ++ ·) hlog⟩

theorem logOf_length (z : Call sigS) : (logOf l z).length ≤ 1 := by
  unfold logOf
  split <;> simp

/-- **Passthrough rounds ending with a refusal forced after a visible log** are rounds of the
host-realizable server with that refusal hidden. -/
theorem rounds_OR_hidden : ∀ {σO σO' : PUnit.{1} × Store Nat}
    {rsO : List ((Nat × Payload) × List (Call (sigN l.host.length)) × (Payload ⊕ PUnit.{1}))},
    Rounds (l.serverO P Ie) σO rsO σO' → ∀ {R R' : List (sigN l.host.length).Op} {c : List (Call (sigN l.host.length))}
      {m : (sigN l.host.length).Op}, servedLog rsO = c ++ [⟨m, none⟩] → VisRun l.host R c R' → Forced l.host R' m →
      TrapLast (served rsO) →
    ∃ rsR, Rounds (l.serverR P Ie) (R, σO.2) rsR (R', σO'.2) ∧ served rsR = served rsO ∧
      servedLog rsR = c
  | _, _, _, .nil _, _, _, c, _, hlog, _, _, _ => by simp [servedLog] at hlog
  | _, _, _, @Rounds.cons _ _ _ _ _ _ s₁ _ a c₀ b rs hr hrs, R, R', c, m, hlog, hv, hf, hT => by
    have hc₀ : c₀ = logOf l ⟨a, b⟩ := log_of_mem hr
    have hlen : c₀.length ≤ 1 := hc₀ ▸ logOf_length _
    simp only [servedLog, List.flatMap_cons] at hlog
    rcases c₀ with _ | ⟨z, _ | ⟨z', c₀⟩⟩
    · have h1 := round_OR (R' := R) hr (.nil _)
      obtain ⟨rsR, hRR, hsv, hlog'⟩ := rounds_OR_hidden hrs hlog hv hf hT.tail
      exact ⟨(a, [], b) :: rsR, .cons h1 hRR, congrArg (List.cons _) hsv, congrArg (_ ++ ·) hlog'⟩
    · rcases c with _ | ⟨z₀, c⟩
      · simp only [List.singleton_append, List.nil_append, List.cons.injEq] at hlog
        obtain ⟨rfl, hrest⟩ := hlog
        cases hv
        obtain ⟨h1, rfl, hπ⟩ := round_OR_hidden hr hf
        have hnil : served rs = [] := hT [] ⟨a, .inr PUnit.unit⟩ (served rs) rfl rfl
        obtain rfl := served_eq_nil hnil
        cases hrs
        refine ⟨[(a, [], .inr PUnit.unit)], .cons ?_ (.nil _), rfl, rfl⟩
        exact h1
      · simp only [List.cons_append, List.cons.injEq] at hlog
        obtain ⟨rfl, hrest⟩ := hlog
        obtain ⟨R₁, hv₁, hv₂⟩ := HLinkedSessionObj.visRun_split (A := [z]) (B := c) hv
        have h1 := round_OR hr hv₁
        obtain ⟨rsR, hRR, hsv, hlog'⟩ := rounds_OR_hidden hrs hrest hv₂ hf hT.tail
        exact ⟨(a, [z], b) :: rsR, .cons h1 hRR, congrArg (List.cons _) hsv,
          congrArg (_ ++ ·) hlog'⟩
    · simp at hlen

/-! ## Infinite services -/

theorem inf_RO {σ : List (sigN l.host.length).Op × Store Nat} {ω : ℕ → Call sigS}
    {lg : ℕ → List (Call (sigN l.host.length))} {st : ℕ → List (sigN l.host.length).Op × Store Nat}
    (h : InfServe (l.serverR P Ie) σ ω lg st) (hn : ∀ k, (ω k).2 ≠ .inr PUnit.unit) :
    InfServe (l.serverO P Ie) (PUnit.unit, σ.2) ω lg (fun k => (PUnit.unit, (st k).2)) ∧
      ∀ k, VisRun l.host σ.1 (logTake lg k) (st k).1 := by
  have hstep : ∀ k, (lg k, End.ret (ω k).2 (PUnit.unit, (st (k + 1)).2)) ∈
      (l.serverO P Ie).1 (PUnit.unit, (st k).2) (ω k).1 ∧
      VisRun l.host (st k).1 (lg k) (st (k + 1)).1 := by
    intro k
    obtain ⟨cO, hO, hcase⟩ := round_RO (R := (st k).1) (π := (st k).2) (R' := (st (k + 1)).1)
      (π' := (st (k + 1)).2) (h.step k)
    rcases hcase with ⟨rfl, hv⟩ | ⟨hx, -⟩
    · exact ⟨hO, hv⟩
    · exact (hn k hx).elim
  refine ⟨⟨by rw [h.zero], fun k => (hstep k).1⟩, ?_⟩
  intro k
  induction k with
  | zero => rw [h.zero]; exact .nil _
  | succ k ih =>
    rw [logTake_succ]
    exact HLinkedSessionObj.visRun_append ih (hstep k).2

theorem inf_OR {σO : PUnit.{1} × Store Nat} {ω : ℕ → Call sigS}
    {lg : ℕ → List (Call (sigN l.host.length))} {st : ℕ → PUnit.{1} × Store Nat}
    (h : InfServe (l.serverO P Ie) σO ω lg st) {R : List (sigN l.host.length).Op}
    (hv : ∀ k, ∃ R', VisRun l.host R (logTake lg k) R') :
    ∃ stR : ℕ → List (sigN l.host.length).Op × Store Nat, InfServe (l.serverR P Ie) (R, σO.2) ω lg stR ∧
      ∀ k, (stR k).2 = (st k).2 := by
  choose Rs hRs using hv
  refine ⟨fun k => (Rs k, (st k).2), ⟨?_, ?_⟩, fun _ => rfl⟩
  · have h0 := hRs 0
    cases h0
    rw [h.zero]
  · intro k
    have hk := hRs (k + 1)
    rw [logTake_succ] at hk
    obtain ⟨R₁, hv₁, hv₂⟩ := HLinkedSessionObj.visRun_split hk
    obtain rfl := HLinkedSessionObj.visRun_det hv₁ (hRs k)
    exact round_OR (h.step k) hv₂

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedLink
