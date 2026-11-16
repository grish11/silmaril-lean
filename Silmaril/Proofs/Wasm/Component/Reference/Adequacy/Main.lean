module

public import Silmaril.Proofs.Wasm.Component.Reference.Adequacy.Transfer

/-!
# Finite adequacy of the component IR against the reference machine

* `den_shape'`: every play of `c.toComp.den C` is complete export rounds, possibly followed by
  one pending question (`exportRounds`);
* `trapLast_shape`: for an adequate simple component, every trap-last play of
  `c.toComp.den (modSem P)` is a sequence of typed returned calls (`seqMoves`), possibly
  followed by a pending question or a trap answer to it;
* `complete_seq` (completeness): every IR play of a sequence of calls and a terminating last
  call (`SeqIRObs`, the conclusion of `Simple.sound_seq`) is a reference behaviour;
* `trapLastPlays_subset` and `obsSub_of_plays`: the two directions of `adequacy`.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.Adequacy

open Silmaril.Games
open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Execution.Core (Store)

local notation "IVal" => Silmaril.Wasm.Component.Val
local notation "ROutcome" => Silmaril.Wasm.Component.Reference.Outcome

variable {P : Profile} {prof : ProfileKind}

/-! ## Rounds and plays -/

theorem exportRounds_eq {k : Nat} : ∀ L : List (Round (sigN k)),
    exportRounds L = twos (E := sigN 0) L
  | [] => rfl
  | ⟨_, _⟩ :: L => by rw [exportRounds, exportRounds_eq L]; rfl

theorem map_forgetMove_twos {k : Nat} : ∀ L : List (Round (sigN k)),
    (twos (E := sigN 0) L).map forgetMove = twos (L.map Round.forget)
  | [] => rfl
  | ⟨_, _⟩ :: L => by
    show _ :: _ :: (twos L).map forgetMove = _
    rw [map_forgetMove_twos L]
    rfl

theorem twos_inj {F : Sig.{0}} : ∀ {M M' : List (Round F)},
    twos (E := sigN 0) M = twos M' → M = M'
  | [], [], _ => rfl
  | [], ⟨_, _⟩ :: _, h => by cases h
  | ⟨_, _⟩ :: _, [], h => by cases h
  | ⟨q, a⟩ :: M, ⟨q', a'⟩ :: M', h => by
    have h' : Sum.inr (Ev.ask q) :: Sum.inr (Ev.ans q a) :: twos (E := sigN 0) M =
        Sum.inr (Ev.ask q') :: Sum.inr (Ev.ans q' a') :: twos M' := h
    simp only [List.cons.injEq, Sum.inr.injEq, Ev.ask.injEq] at h'
    obtain ⟨rfl, h₁, h₂⟩ := h'
    simp only [Ev.ans.injEq, heq_eq_eq, true_and] at h₁
    rw [h₁, twos_inj h₂]

theorem length_twos {E F : Sig.{0}} : ∀ M : List (Round F), (twos (E := E) M).length = 2 * M.length
  | [] => rfl
  | ⟨_, _⟩ :: M => by
    show (twos (E := E) M).length + 2 = _
    rw [length_twos M, List.length_cons]
    ring

theorem twos_ne_twos_ask {F : Sig.{0}} (M M' : List (Round F)) (q : F.Op) :
    twos (E := sigN 0) M ≠ twos M' ++ [Sum.inr (.ask q)] := by
  intro h
  have := congrArg List.length h
  rw [List.length_append, length_twos, length_twos] at this
  simp at this
  omega

/-- The IR rounds of calls, at `sigU`. -/
def seqRoundsU : List (Nat × List IVal) → List (List IVal) → List (Round sigU)
  | (j, vs) :: cs, ws :: wss => ⟨(j, .vals vs), some (.vals ws)⟩ :: seqRoundsU cs wss
  | _, _ => []

theorem seqRounds_forget (c : Simple) :
    ∀ (calls : List (Fin c.exports.length × List IVal)) (wss : List (List IVal)),
      (seqRounds c calls wss).map Round.forget =
        seqRoundsU (calls.map fun q => (q.1.val, q.2)) wss
  | [], _ => rfl
  | (_, _) :: _, [] => rfl
  | (j, vs) :: cs, ws :: wss => by
    show _ :: (seqRounds c cs wss).map Round.forget = _
    rw [seqRounds_forget c cs wss]
    rfl

theorem castCalls_val {c c' : Simple} (len : c.exports.length = c'.exports.length)
    (calls : List (Fin c.exports.length × List IVal)) :
    (castCalls len calls).map (fun q => (q.1.val, q.2)) = calls.map fun q => (q.1.val, q.2) := by
  simp [castCalls]

theorem seqRoundsU_inj : ∀ {ncs ncs' : List (Nat × List IVal)} {wss wss' : List (List IVal)},
    ncs.length = wss.length → ncs'.length = wss'.length →
    seqRoundsU ncs wss = seqRoundsU ncs' wss' → ncs = ncs' ∧ wss = wss'
  | [], [], [], [], _, _, _ => ⟨rfl, rfl⟩
  | [], _ :: _, [], _ :: _, _, _, h => by cases h
  | _ :: _, [], _ :: _, [], _, _, h => by cases h
  | [], _, _ :: _, _, h, _, _ => by cases h
  | _ :: _, _, [], _, h, _, _ => by cases h
  | _, [], _, _ :: _, _, h, _ => by cases h
  | _, _ :: _, _, [], _, h, _ => by cases h
  | (j, vs) :: ncs, (j', vs') :: ncs', ws :: wss, ws' :: wss', h₁, h₂, h => by
    have h' : (⟨(j, .vals vs), some (.vals ws)⟩ :: seqRoundsU ncs wss : List (Round sigU)) =
        ⟨(j', .vals vs'), some (.vals ws')⟩ :: seqRoundsU ncs' wss' := h
    simp only [List.cons.injEq, Sigma.mk.injEq, Prod.mk.injEq, Payload.vals.injEq,
      heq_eq_eq, Option.some.injEq] at h'
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, h''⟩ := h'
    obtain ⟨rfl, rfl⟩ := seqRoundsU_inj (by simpa using h₁) (by simpa using h₂) h''
    exact ⟨rfl, rfl⟩

theorem calls_eq_of_val {n : Nat} :
    ∀ {calls calls' : List (Fin n × List IVal)},
      calls.map (fun q => (q.1.val, q.2)) = calls'.map (fun q => (q.1.val, q.2)) → calls = calls'
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | (j, vs) :: cs, (j', vs') :: cs', h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨hj, rfl⟩, h'⟩ := h
    rw [Fin.ext hj, calls_eq_of_val h']

/-! ## Trap-last plays -/

theorem trapLast_cons {m : Move (sigN 0) sigU} {p : List (Move (sigN 0) sigU)} :
    TrapLast (m :: p) ↔ ((∃ q, m = .inr (.ans q none)) → p = []) ∧ TrapLast p := by
  constructor
  · intro h
    refine ⟨fun ⟨q, hq⟩ => h [] p q (by rw [hq]; rfl), fun l₁ l₂ q hp => h (m :: l₁) l₂ q ?_⟩
    rw [hp]
    rfl
  · rintro ⟨h₁, h₂⟩ l₁ l₂ q hp
    cases l₁ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      exact h₁ ⟨q, rfl⟩
    | cons x l₁ =>
      simp only [List.cons_append, List.cons.injEq] at hp
      exact h₂ l₁ l₂ q hp.2

theorem trapLast_nil : TrapLast ([] : List (Move (sigN 0) sigU)) :=
  fun l₁ _ _ h => by cases l₁ <;> cases h

theorem trapLast_twos_cons {q : sigU.Op} {a : Option Payload} {M : List (Round sigU)} :
    TrapLast (twos (⟨q, a⟩ :: M)) ↔ (a = none → M = []) ∧ TrapLast (twos M) := by
  show TrapLast (_ :: _ :: twos M) ↔ _
  rw [trapLast_cons, trapLast_cons]
  constructor
  · rintro ⟨-, h₁, h₂⟩
    refine ⟨fun ha => ?_, h₂⟩
    subst ha
    exact twos_inj_nil (h₁ ⟨q, rfl⟩)
  · rintro ⟨h₁, h₂⟩
    refine ⟨(fun ⟨_, h⟩ => by cases h), fun ⟨q', h⟩ => ?_, h₂⟩
    simp only [Sum.inr.injEq, Ev.ans.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [h₁ (eq_of_heq h)]
    rfl

/-- **Trap-last complete rounds**: all answers are results, or all but the last, which is a
trap. -/
theorem trapLast_twos : ∀ (M : List (Round sigU)), TrapLast (twos M) →
    (∀ x ∈ M, x.2.isSome) ∨ ∃ M₀ q, M = M₀ ++ [⟨q, none⟩] ∧ ∀ x ∈ M₀, x.2.isSome
  | [], _ => .inl fun _ h => nomatch h
  | ⟨q, a⟩ :: M, h => by
    rw [trapLast_twos_cons] at h
    obtain ⟨h₁, h₂⟩ := h
    cases a with
    | none =>
      obtain rfl := h₁ rfl
      exact .inr ⟨[], q, rfl, fun _ h => nomatch h⟩
    | some a =>
      rcases trapLast_twos M h₂ with hall | ⟨M₀, q', rfl, hall⟩
      · refine .inl fun x hx => ?_
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact hall x hx
      · refine .inr ⟨⟨q, some a⟩ :: M₀, q', rfl, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact hall x hx

theorem trapLast_twos_allSome : ∀ {M : List (Round sigU)}, (∀ x ∈ M, x.2.isSome) →
    TrapLast (twos M)
  | [], _ => trapLast_nil
  | ⟨q, a⟩ :: M, h => by
    rw [trapLast_twos_cons]
    refine ⟨fun ha => ?_, trapLast_twos_allSome fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
    have := h _ List.mem_cons_self
    subst ha
    cases this

theorem trapLast_twos_last : ∀ {M₀ : List (Round sigU)} (x : Round sigU),
    (∀ x ∈ M₀, x.2.isSome) → TrapLast (twos (M₀ ++ [x]))
  | [], ⟨q, a⟩, _ => by
    rw [List.nil_append, trapLast_twos_cons]
    exact ⟨fun _ => rfl, trapLast_nil⟩
  | ⟨q, a⟩ :: M₀, x, h => by
    rw [List.cons_append, trapLast_twos_cons]
    refine ⟨fun ha => ?_, trapLast_twos_last x fun y hy => h y (List.mem_cons_of_mem _ hy)⟩
    have := h _ List.mem_cons_self
    subst ha
    cases this

theorem trapLast_ask_iff : ∀ (M : List (Round sigU)) (q : sigU.Op),
    TrapLast (twos M ++ [Sum.inr (.ask q)]) ↔ ∀ x ∈ M, x.2.isSome
  | [], q => ⟨(fun _ _ h => nomatch h), fun _ => by
      show TrapLast [Sum.inr (.ask q)]
      exact trapLast_cons.mpr ⟨(fun ⟨_, h⟩ => by cases h), trapLast_nil⟩⟩
  | ⟨q', a⟩ :: M, q => by
    show TrapLast (_ :: _ :: (twos M ++ [Sum.inr (.ask q)])) ↔ _
    rw [trapLast_cons, trapLast_cons, trapLast_ask_iff M q]
    constructor
    · rintro ⟨-, h₁, h₂⟩ x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · cases a with
        | none => exact absurd (h₁ ⟨q', rfl⟩) (by simp)
        | some _ => rfl
      · exact h₂ x hx
    · intro h
      refine ⟨(fun ⟨_, h⟩ => by cases h), fun ⟨q'', h'⟩ => ?_, fun x hx => h x (List.mem_cons_of_mem _ hx)⟩
      simp only [Sum.inr.injEq, Ev.ans.injEq] at h'
      obtain ⟨rfl, h'⟩ := h'
      have := h _ List.mem_cons_self
      rw [eq_of_heq h'] at this
      cases this

/-! ## Indices -/

theorem toComp_length (c : Simple) : c.toComp.exports.length = c.exports.length := by
  simp [Simple.toComp]

theorem forget_mem_lt {c : Simple} {L : List (Round (sigN c.toComp.exports.length))}
    {x : Round sigU} (hx : x ∈ L.map Round.forget) : x.1.1 < c.exports.length := by
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  rw [← toComp_length]
  exact y.1.1.isLt

/-- The rounds of a sequence of calls and a last round, at `sigN`. -/
theorem forget_last {c : Simple} (calls : List (Fin c.exports.length × List IVal))
    (wss : List (List IVal)) (j : Nat) (hj : j < c.toComp.exports.length) (p : Payload)
    (A : Option Payload) :
    (seqRounds c calls wss ++
        ([⟨(⟨j, hj⟩, p), A⟩] : List (Round (sigN c.toComp.exports.length)))).map Round.forget =
      seqRoundsU (calls.map fun q => (q.1.val, q.2)) wss ++
        ([⟨(j, p), A⟩] : List (Round sigU)) := by
  rw [List.map_append, seqRounds_forget]
  rfl

/-- `ObsAns` determines the outcome. -/
theorem obsAns_unique {b b' : ROutcome} {A : Option Payload} (h : ObsAns b A) (h' : ObsAns b' A) :
    b = b' := by
  cases b with
  | returns r =>
    cases r with
    | none => exact h.elim
    | some rs =>
      cases b' with
      | returns r' =>
        cases r' with
        | none => exact h'.elim
        | some rs' =>
          obtain ⟨ws, rfl, rfl⟩ := h
          obtain ⟨ws', rfl, h''⟩ := h'
          simp only [Option.some.injEq, Payload.vals.injEq] at h''
          rw [h'']
      | traps => obtain ⟨ws, -, rfl⟩ := h; cases h'
      | deadlocks => exact h'.elim
      | diverges => exact h'.elim
  | traps =>
    cases b' with
    | returns r' =>
      cases r' with
      | none => exact h'.elim
      | some rs' => obtain ⟨ws, -, rfl⟩ := h'; cases h
    | traps => rfl
    | deadlocks => exact h'.elim
    | diverges => exact h'.elim
  | deadlocks => exact h.elim
  | diverges => exact h.elim

theorem obsAns_term {b : ROutcome} {A : Option Payload} (h : ObsAns b A) : b.Term := by
  cases b with
  | returns r => cases r with
    | none => exact h.elim
    | some _ => trivial
  | traps => trivial
  | deadlocks => exact h.elim
  | diverges => exact h.elim

/-! ## The last round -/

/-- The specification of a typed last round. -/
theorem last_spec {c : Simple} {I : Silmaril.Wasm.Game.ScalarInstance} {s s₂ : Store Nat}
    {j : Nat} {vs : List IVal} {A : Option Payload} (hj : j < c.exports.length)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true)
    (h : RoundSpec P c I s ⟨(j, .vals vs), A⟩ s₂) :
    ∃ b, ObsAns b A ∧ b ∈ specAt P c I c.exports[j] vs s := by
  rcases h with ⟨-, -, hn⟩ | ⟨hj', vs', xs, r, hp, hl, hr, hA, -⟩
  · exact absurd (hn hj vs rfl) (by rw [checkLower_of_check hvs]; simp)
  · cases hp
    refine ⟨liftOutcome c.exports[j].ty r, hA ▸ obsAns_liftOutcome _ r, ?_⟩
    unfold specAt
    rw [hl]
    exact .inl ⟨r, hr, rfl⟩

theorem seqRoundsU_allSome : ∀ (ncs : List (Nat × List IVal)) (wss : List (List IVal)),
    ∀ x ∈ seqRoundsU ncs wss, x.2.isSome
  | [], _, _, h => by simp [seqRoundsU] at h
  | _ :: _, [], _, h => by simp [seqRoundsU] at h
  | (j, vs) :: ncs, ws :: wss, x, h => by
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · exact seqRoundsU_allSome ncs wss x h

/-- **Complete rounds of the IR, read back**: a chain of returned calls from the instance's
store and a typed last round with its specification outcome. -/
theorem read_back {c : Simple} (hc : c.Adequate) {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : c.mod.IsInst I) {L : List (Round (sigN c.toComp.exports.length))}
    (hL : twos L ∈ c.toComp.den (modSem P)) {ncalls : List (Nat × List IVal)}
    {wss : List (List IVal)} (hlen : ncalls.length = wss.length) {j : Nat} {vs : List IVal}
    {A : Option Payload} (hM : L.map Round.forget = seqRoundsU ncalls wss ++ [⟨(j, .vals vs), A⟩])
    (hj : j < c.exports.length) (hvs : ValTy.checkList c.exports[j].ty.params vs = true) :
    ∃ (calls : List (Fin c.exports.length × List IVal)) (s : Store Nat) (b : ROutcome),
      calls.map (fun q => (q.1.val, q.2)) = ncalls ∧ TypedCalls c calls ∧
      SeqSpec P c I I.store (specCalls c calls) wss s ∧ ObsAns b A ∧
      b ∈ specAt P c I c.exports[j] vs s := by
  have hS := specRounds_of_den hc.good hI hL
  rw [hM] at hS
  obtain ⟨calls, wss', s, hM₀, hlen', ht, hseq, hT⟩ :=
    chain_of_specRounds _ (seqRoundsU_allSome ncalls wss) hS
  rw [seqRounds_forget] at hM₀
  obtain ⟨hc₁, rfl⟩ := seqRoundsU_inj hlen (by simpa using hlen') hM₀
  cases hT with
  | cons hr _ =>
    obtain ⟨b, hb, hb'⟩ := last_spec hj hvs hr
    exact ⟨calls, _, b, hc₁.symm, ht, hseq, hb, hb'⟩

/-! ## Completeness -/

/-- **Completeness for sequences of calls**: every play of the IR denotation of a sequence of
resolved calls and a terminating last call, as `SeqIRObs` prescribes, is a reference behaviour
(every profile, every component choice profile). -/
theorem complete_seq (P : Profile) (prof : ProfileKind) (c : Simple) (hc : c.Adequate)
    (calls : List (Fin c.exports.length × List IVal)) (wss : List (List IVal))
    (hlen : calls.length = wss.length) (j : Fin c.exports.length) (vs : List IVal)
    (hvs : ValTy.checkList c.exports[j].ty.params vs = true) (b : ROutcome) (hterm : b.Term)
    (hb : SeqIRObs c (c.toComp.den (modSem P)) calls wss j vs b) :
    TypedCalls c calls ∧ (wss.map (·.map toRefVal), b) ∈ seqBehaviours prof (refHost P) ()
      c.toRef (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
      (vs.map toRefVal) := by
  obtain ⟨I, hI⟩ := hc.inst.inst
  have key : ∀ A, ObsAns b A →
      twos (seqRounds c calls wss ++ [⟨(⟨j, by simp [Simple.toComp]⟩, .vals vs), A⟩]) ∈
        c.toComp.den (modSem P) → TypedCalls c calls ∧ (wss.map (·.map toRefVal), b) ∈
          seqBehaviours prof (refHost P) () c.toRef
            (calls.map fun q => (c.exports[q.1].name, q.2.map toRefVal)) c.exports[j].name
            (vs.map toRefVal) := by
    intro A hA hL
    obtain ⟨calls', s, b', hc', ht, hseq, hb', hspec⟩ := read_back hc hI hL
      (ncalls := calls.map fun q => (q.1.val, q.2)) (wss := wss)
      (by rw [List.length_map]; exact hlen) (forget_last calls wss j _ _ A) j.isLt hvs
    have e := (calls_eq_of_val hc').symm
    subst e
    obtain rfl := obsAns_unique hA hb'
    exact ⟨ht, seq_specToRef P prof c hc.good hc.floatFree hc.inst hc.arity hI calls wss s j vs ht
      hvs hseq hspec (obsAns_term hA)⟩
  cases b with
  | returns r =>
    cases r with
    | none => exact hterm.elim
    | some rs =>
      obtain ⟨ws, rfl, h⟩ := hb
      rw [seqMoves_eq, seqRounds_append c j vs ws calls wss hlen] at h
      exact key _ ⟨ws, rfl, rfl⟩ h
  | traps =>
    have h : twos (E := sigN 0)
        (seqRounds c calls wss ++ [⟨(⟨j, by simp [Simple.toComp]⟩, .vals vs), none⟩]) ∈
        c.toComp.den (modSem P) := by
      rw [twos_append, ← seqMoves_eq]
      exact hb
    exact key none rfl h
  | deadlocks => exact hterm.elim
  | diverges => exact hterm.elim

/-! ## The shape of plays -/

/-- **Every play is complete export rounds, possibly followed by a pending question.** -/
theorem den_shape' (C : CoreSem NumModule) (c : Simple)
    {p : List (Move (sigN 0) (sigN c.toComp.exports.length))} (hp : p ∈ c.toComp.den C) :
    (∃ L, p = exportRounds L) ∨ ∃ L q, p = exportRounds L ++ [.inr (.ask q)] := by
  rcases den_shape C c hp with ⟨L, rfl⟩ | ⟨q, L, rfl⟩
  · exact .inl ⟨L, (exportRounds_eq L).symm⟩
  · exact .inr ⟨L, q, by rw [exportRounds_eq]⟩

theorem forget_injective {k : Nat} : Function.Injective (Round.forget (n := k)) := by
  rintro ⟨⟨j, p⟩, a⟩ ⟨⟨j', p'⟩, a'⟩ h
  simp only [Round.forget, Sigma.mk.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨hj, rfl⟩, h⟩ := h
  obtain rfl := Fin.ext hj
  obtain rfl := eq_of_heq h
  rfl

theorem forget_map_inj {k : Nat} {L L' : List (Round (sigN k))}
    (h : L.map Round.forget = L'.map Round.forget) : L = L' :=
  List.map_injective_iff.mpr forget_injective h

/-- **Trap-last plays read back**: a chain of typed returned calls from the instance store, and
then nothing, a pending question, or a trap answer with its specification round (the store after
the trap is not constrained). -/
theorem trapLast_read {c : Simple} (hc : c.Adequate) {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : c.mod.IsInst I) {p : List (Move (sigN 0) (sigN c.toComp.exports.length))}
    (hp : p ∈ c.toComp.den (modSem P)) (htl : TrapLast (p.map forgetMove)) :
    ∃ (calls : List (Fin c.exports.length × List IVal)) (wss : List (List IVal)) (s : Store Nat),
      TypedCalls c calls ∧ calls.length = wss.length ∧
      SeqSpec P c I I.store (specCalls c calls) wss s ∧
      (p = seqMoves c calls wss ∨ (∃ q, p = seqMoves c calls wss ++ [.inr (.ask q)]) ∨
        ∃ q s₂, p = seqMoves c calls wss ++ [.inr (.ask q), .inr (.ans q none)] ∧
          RoundSpec P c I s ⟨(q.1.val, q.2), none⟩ s₂) := by
  rcases den_shape _ c hp with ⟨L, rfl⟩ | ⟨q, L, rfl⟩
  · rw [map_forgetMove_twos] at htl
    have hS := specRounds_of_den hc.good hI hp
    rcases trapLast_twos _ htl with hall | ⟨M₀, q, hM, hall⟩
    · obtain ⟨calls, wss, s, hM₀, hlen, ht, hseq, -⟩ := chain_of_specRounds (T := []) _ hall
        (by rw [List.append_nil]; exact hS)
      obtain rfl := forget_map_inj hM₀
      exact ⟨calls, wss, s, ht, hlen, hseq, .inl (seqMoves_eq c calls wss).symm⟩
    · rw [hM] at hS
      obtain ⟨calls, wss, s, hM₀, hlen, ht, hseq, hT⟩ := chain_of_specRounds _ hall hS
      obtain ⟨L₀, L₁, rfl, h₀, h₁⟩ := List.map_eq_append_iff.mp hM
      obtain ⟨x, rfl⟩ : ∃ x, L₁ = [x] := by
        cases L₁ with
        | nil => cases h₁
        | cons x L₁ => cases L₁ with
          | nil => exact ⟨x, rfl⟩
          | cons _ _ => exact absurd (congrArg List.length h₁) (by simp)
      have hx : Round.forget x = ⟨q, none⟩ := (List.cons.inj h₁).1
      have hx2 : (x.2 : Option Payload) = none :=
        congrArg (fun y : Round sigU => (y.2 : Option Payload)) hx
      obtain ⟨q', a⟩ := x
      obtain rfl : a = none := hx2
      obtain rfl := forget_map_inj (h₀.trans hM₀)
      have hq : q = (q'.1.val, q'.2) := (congrArg Sigma.fst hx).symm
      subst hq
      cases hT with
      | cons hr _ =>
        refine ⟨calls, wss, s, ht, hlen, hseq, .inr (.inr ⟨q', _, ?_, hr⟩)⟩
        rw [twos_append, seqMoves_eq]
        rfl
  · have hall := (trapLast_ask_iff _ _).mp (by
      have := htl
      rw [List.map_append, map_forgetMove_twos] at this
      exact this)
    have hp₀ : twos L ∈ c.toComp.den (modSem P) := (c.toComp.den (modSem P)).of_prefix hp
      (List.prefix_append _ _)
    have hS := specRounds_of_den hc.good hI hp₀
    obtain ⟨calls, wss, s, hM₀, hlen, ht, hseq, -⟩ := chain_of_specRounds (T := []) _ hall
      (by rw [List.append_nil]; exact hS)
    obtain rfl := forget_map_inj hM₀
    exact ⟨calls, wss, s, ht, hlen, hseq, .inr (.inl ⟨q, by rw [seqMoves_eq]⟩)⟩

/-- **Trap-last plays are typed returned calls**, possibly followed by a pending question or a
trap answer to it. -/
theorem trapLast_shape {c : Simple} (hc : c.Adequate)
    {p : List (Move (sigN 0) (sigN c.toComp.exports.length))}
    (hp : p ∈ c.toComp.den (modSem P)) (htl : TrapLast (p.map forgetMove)) :
    ∃ (calls : List (Fin c.exports.length × List IVal)) (wss : List (List IVal)),
      TypedCalls c calls ∧ calls.length = wss.length ∧
      (p = seqMoves c calls wss ∨ ∃ q, p = seqMoves c calls wss ++ [.inr (.ask q)] ∨
        p = seqMoves c calls wss ++ [.inr (.ask q), .inr (.ans q none)]) := by
  obtain ⟨I, hI⟩ := hc.inst.inst
  obtain ⟨calls, wss, s, ht, hlen, -, h⟩ := trapLast_read hc hI hp htl
  refine ⟨calls, wss, ht, hlen, ?_⟩
  rcases h with h | ⟨q, h⟩ | ⟨q, s₂, h, -⟩
  · exact .inl h
  · exact .inr ⟨q, .inl h⟩
  · exact .inr ⟨q, .inr h⟩

end Silmaril.Proofs.Wasm.Component.Reference.Adequacy
