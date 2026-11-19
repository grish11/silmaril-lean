module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Defs
public import Silmaril.Wasm.Logic.GameLink.Thms
public import Silmaril.Wasm.Logic.Open.Thms

/-!
# Proofs: the program logic and traced sessions

`tsession_good`: along a traced session of an instance meeting `MemSat`, against an environment
whose answers respect the contract's store frame, the configuration is safe under `memHost`
(for the instantiation postcondition, then for the export postcondition) as long as every
input decoded so far meets `K.ans`; and every input tag `x`, preceded only by inputs meeting
`K.ans`, is decoded from a callout meeting `K.pre`, at its call or at its answer.

The invariant `Good` is `Silmaril.Wasm.Logic.GameLink`'s, read on configurations: instantiation
is safe for `instPost Inv`; an invocation (and a finished one) is safe for the export
postcondition, which gives the invariant at the next invocation (`Open.final_post`). At a call
redex the import's precondition holds (`Open.import_pre`), and an answer meeting the frame and
`K.ans` is a step of `memHost` (`Open.redex_step_ret`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept.IO Silmaril.Wasm.Game.HandleAccept.MemSound
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Logic.Strategy (resultOutcome)
open Silmaril.Wasm.SingleThreaded (decompose?)

variable {X I O C : Type}

theorem resultOutcome_inj {r r' : Result} (h : resultOutcome r = resultOutcome r') : r = r' := by
  cases r <;> cases r' <;> simp_all [resultOutcome]

/-- The invariant of a traced session, on its configuration. -/
def Good (P : Numerics.Profile) (m : Module) (memAddr : Option Nat) (R : Roles X I O C)
    (K : MemContract I) (Inv : Store Nat → Prop) : IOAccept.Phase → Config Nat → Prop
  | .inst, c => ∀ n, Safe P (memHost m memAddr R K) (instPost Inv) n c
  | _, c => ∀ n, Safe P (memHost m memAddr R K) (callPost {} [] fun s _ => Inv s) n c

/-- All the inputs of a tag list meet `A`. -/
def AllIn (A : I → Prop) (ts : List (Tag X I O C)) : Prop := ∀ x, Tag.inp x ∈ ts → A x

theorem AllIn.left {A : I → Prop} {ts us : List (Tag X I O C)} (h : AllIn A (ts ++ us)) :
    AllIn A ts := fun x hx => h x (List.mem_append_left _ hx)

theorem AllIn.right {A : I → Prop} {ts us : List (Tag X I O C)} (h : AllIn A (ts ++ us)) :
    AllIn A us := fun x hx => h x (List.mem_append_right _ hx)

/-- Every input tag preceded by inputs meeting `A` is decoded from a callout meeting `pre`. -/
def PreOk (R : Roles X I O C) (K : MemContract I) (ts : List (Tag X I O C)) : Prop :=
  ∀ u x v, ts = u ++ .inp x :: v → AllIn K.ans u →
    ∃ o, K.pre o ∧ (R.callIn o = some x ∨ ∃ w, R.answerIn o w = some x)

theorem split_append {α : Type} {ts N u v : List α} {x : α} (h : ts ++ N = u ++ x :: v) :
    (∃ v', ts = u ++ x :: v') ∨ (∃ u', u = ts ++ u' ∧ N = u' ++ x :: v) := by
  rcases List.append_eq_append_iff.1 h with ⟨a', hu, hN⟩ | ⟨c', hts, hx⟩
  · exact .inr ⟨a', hu, hN⟩
  · cases c' with
    | nil => exact .inr ⟨[], by simpa using hts.symm, by simpa using hx.symm⟩
    | cons y c'' =>
      simp only [List.cons_append, List.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact .inl ⟨c'', hts⟩

theorem PreOk.append {R : Roles X I O C} {K : MemContract I} {ts N : List (Tag X I O C)}
    (h : PreOk R K ts)
    (hN : AllIn K.ans ts → ∀ x, Tag.inp x ∈ N →
      ∃ o, K.pre o ∧ (R.callIn o = some x ∨ ∃ w, R.answerIn o w = some x)) :
    PreOk R K (ts ++ N) := by
  intro u x v he hu
  rcases split_append he with ⟨v', hv'⟩ | ⟨u', rfl, hN'⟩
  · exact h u x v' hv' hu
  · exact hN hu.left x (by rw [hN']; simp)

section Steps

variable {P : Numerics.Profile} {m : Module} {memAddr : Option Nat} {R : Roles X I O C}
  {K : MemContract I} {Inv : Store Nat → Prop}

/-- A safe configuration at a call redex: the callout meets the precondition. -/
theorem pre_of_safe {Q : Post Nat} {c : Config Nat} {E : SingleThreaded.Ctx} {fa h : Nat}
    {args : List Val} (hs : ∀ n, Safe P (memHost m memAddr R K) Q n c)
    (hd : decompose? c.store c.code = some (E, fa, h, args)) {o : Callout}
    (ho : calloutAt? m memAddr c = some o) : K.pre o := by
  obtain ⟨S, hS, hpre⟩ := Silmaril.Wasm.Logic.Open.import_pre (hs 1) hd
  unfold calloutAt? at ho
  rw [hd] at ho
  simp only [Option.bind_some, Option.map_eq_some_iff] at ho
  obtain ⟨i, hi, rfl⟩ := ho
  simp only [memCtx, id, hi, Option.map_some, Option.some.injEq] at hS
  subst hS
  exact hpre

/-- The callout at a call redex exists when the host code is an import with a specification. -/
theorem callout_of_safe {Q : Post Nat} {c : Config Nat} {E : SingleThreaded.Ctx} {fa h : Nat}
    {args : List Val} (hs : ∀ n, Safe P (memHost m memAddr R K) Q n c)
    (hd : decompose? c.store c.code = some (E, fa, h, args)) :
    ∃ i, m.imports[h]? = some i ∧ calloutAt? m memAddr c = some (calloutIn i memAddr c.store args) ∧
      K.pre (calloutIn i memAddr c.store args) := by
  obtain ⟨S, hS, hpre⟩ := Silmaril.Wasm.Logic.Open.import_pre (hs 1) hd
  simp only [memCtx, id, Option.map_eq_some_iff] at hS
  obtain ⟨i, hi, rfl⟩ := hS
  refine ⟨i, hi, ?_, hpre⟩
  unfold calloutAt?
  rw [hd]
  simp [hi, calloutIn]

/-- An answer meeting the frame and the answer assumption keeps a safe configuration safe. -/
theorem safe_answer {Q : Post Nat} {c : Config Nat} {E : SingleThreaded.Ctx} {fa h : Nat}
    {args : List Val} {a : UReply} (hs : ∀ n, Safe P (memHost m memAddr R K) Q n c)
    (hd : decompose? c.store c.code = some (E, fa, h, args)) (hfr : K.reply ⟨h, c.store, args⟩ a)
    (hans : ∀ x, Tag.inp x ∈ ((calloutAt? m memAddr c).elim [] fun o =>
      R.answerTags o ⟨a.result, memOf memAddr a.store⟩ : List (Tag X I O C)) → K.ans x) :
    ∀ n, Safe P (memHost m memAddr R K) Q n ⟨a.store, c.frame, E.fill a.result.toAdmin⟩ := by
  obtain ⟨i, hi, ho, hpre⟩ := callout_of_safe hs hd
  have hr : memHost m memAddr R K h c.store args (.returned a.store a.result) := by
    refine ⟨importSpec h i memAddr R K, by simp [memCtx, hi], hpre, a.result, rfl, hfr,
      fun x hx => ?_⟩
    refine hans x ?_
    rw [ho]
    simp [Option.elim, Roles.answerTags, hx]
  intro n
  exact (hs (n + 1)).step_inv (Silmaril.Wasm.Logic.Open.redex_step_ret hd hr)

/-- The invariant at the end of a finished run. -/
theorem inv_of_finished {p : IOAccept.Phase} {c : Config Nat} (hp : p ≠ .run)
    (hg : Good P m memAddr R K Inv p c) (fin : Finished p.started c) : Inv c.store := by
  cases p with
  | run => exact absurd rfl hp
  | inst =>
    obtain ⟨vs, hc⟩ := fin
    have hc' : c = ⟨c.store, c.frame, vals vs⟩ := by
      rcases c with ⟨s, f, code⟩
      simp only at hc
      simp [hc, Result.toAdmin]
    have hsafe := hg 1
    rw [hc'] at hsafe
    obtain ⟨o, he, hq⟩ := hsafe.exit_of_stuck fun _ => not_step_vals
    exact hq vs (exits_vals_inv he)
  | idle =>
    obtain ⟨r, hc⟩ := fin
    have hc' : c = ⟨c.store, c.frame, r.toAdmin⟩ := by
      rcases c with ⟨s, f, code⟩
      simp only at hc
      simp [hc]
    have hsafe := hg 1
    rw [hc'] at hsafe
    exact Silmaril.Wasm.Logic.Open.final_post (R := fun s _ => Inv s) hsafe

end Steps

/-- **The session invariant.** -/
theorem tsession_good {P : Numerics.Profile} {L : SEnv UImp} {m : Module}
    {memAddr : Option Nat} {R : Roles X I O C} {K : MemContract I} {Inv : Store Nat → Prop}
    {c₀ : Config Nat} {q₀ : L.S} {addrs : List Nat}
    (hinst : ∀ n, Safe P (memHost m memAddr R K) (instPost Inv) n c₀)
    (hexp : ∀ a ∈ addrs, FSpecValid P (memHost m memAddr R K) a (exportSpec Inv a))
    (hL : ∀ q e a q', L.Ans q e a q' → K.reply e a)
    {p : IOAccept.Phase} {w : Bool} {x : Config Nat × L.S} {ts : List (Tag X I O C)}
    (h : TSession P L m memAddr R c₀ q₀ addrs p w x ts) :
    (AllIn K.ans ts → Good P m memAddr R K Inv p x.1) ∧ PreOk R K ts := by
  induction h with
  | start => exact ⟨fun _ => hinst, fun u x v he => by simp at he⟩
  | @internal p _ c c' _ _ _ st ih =>
    refine ⟨fun hA => ?_, ih.2⟩
    have hg := ih.1 hA
    have st' := Step.of_noHost (memHost m memAddr R K) st
    cases p <;> exact fun n => (hg (n + 1)).step_inv st'
  | @call p c _ _ E fa h args _ hd ih =>
    refine ⟨fun hA => ih.1 hA.left, ih.2.append fun hA x hx => ?_⟩
    have hg := ih.1 hA
    have hs : ∀ Q, (∀ n, Safe P (memHost m memAddr R K) Q n c) →
        ∃ o, K.pre o ∧ (R.callIn o = some x ∨ ∃ w, R.answerIn o w = some x) := by
      intro Q hsafe
      obtain ⟨i, -, ho, hpre⟩ := callout_of_safe hsafe hd
      rw [ho] at hx
      simp only [Option.elim, Roles.callTags, List.mem_append, List.mem_map,
        Option.mem_toList] at hx
      rcases hx with ⟨j, hj, he⟩ | ⟨j, -, he⟩
      · cases he; exact ⟨_, hpre, .inl hj⟩
      · cases he
    cases p
    · exact hs _ hg
    · exact hs _ hg
    · exact hs _ hg
  | @answer p c _ _ _ E fa h args a _ hd ans ih =>
    refine ⟨fun hA => ?_, ih.2.append fun hA x hx => ?_⟩
    · have hg := ih.1 hA.left
      cases p <;> exact safe_answer hg hd (hL _ _ _ _ ans) fun x hx => hA.right x hx
    · have hg := ih.1 hA
      have hs : ∀ Q, (∀ n, Safe P (memHost m memAddr R K) Q n c) →
          ∃ o, K.pre o ∧ (R.callIn o = some x ∨ ∃ w, R.answerIn o w = some x) := by
        intro Q hsafe
        obtain ⟨i, -, ho, hpre⟩ := callout_of_safe hsafe hd
        rw [ho] at hx
        simp only [Option.elim, Roles.answerTags, List.mem_map, Option.mem_toList] at hx
        obtain ⟨j, hj, he⟩ := hx
        cases he
        exact ⟨_, hpre, .inr ⟨_, hj⟩⟩
      cases p
      · exact hs _ hg
      · exact hs _ hg
      · exact hs _ hg
  | @invoke p _ c _ _ a args _ hp fin ha ok ih =>
    refine ⟨fun hA => ?_, ih.2.append fun _ x hx => by simp at hx⟩
    have hinv := inv_of_finished hp (ih.1 hA.left) fin
    intro n
    have := hexp a ha n c.store args ⟨hinv, ok⟩ {} []
      (.callRefType ((c.store.funcs[a]?.map FuncInst.type).getD default))
      (show Admin.IsCallRef (.callRefType _) from trivial)
    simpa [invoke, exportSpec] using this
  | ret _ _ ih =>
    exact ⟨fun hA => ih.1 hA.left, ih.2.append fun _ x hx => by simp at hx⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
