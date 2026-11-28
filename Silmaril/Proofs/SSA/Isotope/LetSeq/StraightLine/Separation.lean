module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Replay

public section

namespace Silmaril.Isotope.LetSeq.StraightLine

open LocallyNameless (Derivation Equiv)
open Silmaril.Isotope.Semantics (BoundEnv)
open Silmaril.Semantics.NondeterministicTrace

set_option backward.isDefEq.respectTransparency false

private theorem slot_cases {n : Nat} {β : BoundCtx Types n} {P : Slot (β.snoc Atom) → Prop}
    (zero : P ⟨0, rfl⟩) (succ : ∀ s : Slot β, P ⟨s.1.succ, s.2⟩) :
    ∀ s, P s := by
  rintro ⟨i, h⟩
  revert h
  exact Fin.cases (fun _ => zero) (fun j h => succ ⟨j, h⟩) i

theorem separating_snoc_proof {n : Nat} {β : BoundCtx Types n} {ρ : BoundEnv Value β} {fresh : Nat}
    (h : Separating ρ fresh) : Separating (ρ.snoc (A := Atom) fresh) (fresh + 1) where
  below := slot_cases (Nat.lt_succ_self _) (fun s => Nat.lt_succ_of_lt (h.below s))
  injective := by
    intro x
    induction x using slot_cases with
    | zero =>
      intro y
      induction y using slot_cases with
      | zero => exact fun _ => rfl
      | succ y =>
        intro eq
        have neq := Nat.ne_of_lt (h.below y)
        exact (neq eq.symm).elim
    | succ x =>
      intro y
      induction y using slot_cases with
      | zero =>
        intro eq
        exact (Nat.ne_of_lt (h.below x) eq).elim
      | succ y =>
        intro eq
        have same := h.injective eq
        cases same
        rfl

private theorem slot_run {n : Nat} {β : BoundCtx Types n} (s : Slot β) (ρ : BoundEnv Value β) :
    run (slotDerivation s) ρ = pure (s.value ρ) := by
  have variableRun (A : Types) (h : β.get s.1 = A) :
      run (cast (congrArg (Derivation Request Γ₀ β (.bv s.1)) h) .bv) ρ =
        pure (cast (congrArg Value h) (ρ s.1)) := by
    cases h
    rfl
  exact variableRun Atom s.2

theorem assembly_run_proof {n : Nat} {β : BoundCtx Types n} {A : Types}
    (v : Assembly β A) (ρ : BoundEnv Value β) : run v.derivation ρ = pure (v.value ρ) := by
  induction v with
  | slot i => exact slot_run i ρ
  | unit => rfl
  | pair a b iha ihb =>
    unfold run at iha ihb
    simp only [run, Assembly.derivation, Assembly.value, Derivation.denote, iha, ihb, pure_bind]
    rfl

private theorem assembly_inj {n : Nat} {β : BoundCtx Types n} {A : Types}
    (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    Function.Injective (Assembly.value (A := A) ρ) := by
  intro p
  induction p with
  | slot i =>
    intro q h
    cases q with
    | slot j => exact congrArg Assembly.slot (sep.injective h)
  | unit =>
    intro q _
    cases q
    rfl
  | pair a b iha ihb =>
    intro q h
    cases q with
    | pair x y =>
      exact congrArg₂ Assembly.pair (iha (Prod.mk.inj h).1) (ihb (Prod.mk.inj h).2)

theorem run_step_proof {n : Nat} {β : BoundCtx Types n} {A : Types} {body : Term (n + 2)}
    (f : Request) (arg : Assembly β Packet) (rest : ProductCanonical ((β.snoc Atom).snoc Atom) body A)
    (ρ : BoundEnv Value β) :
    run (ProductCanonical.derivation (.step f arg rest)) ρ =
      model.eval f (arg.value ρ) >>= fun ab =>
        run rest.derivation ((ρ.snoc (A := Atom) ab.1).snoc (A := Atom) ab.2) := by
  have argRun := assembly_run_proof arg ρ
  unfold run at argRun
  simp only [ProductCanonical.derivation, run, Derivation.denote, argRun, pure_bind]
  rfl

theorem run_request_proof {n : Nat} {β : BoundCtx Types n} {body : Term (n + 2)}
    (f : Request) (x y : Slot β) (rest : Canonical ((β.snoc Atom).snoc Atom) body)
    (ρ : BoundEnv Value β) :
    run (canonicalDerivation (.request f x y rest)) ρ =
      model.eval f (x.value ρ, y.value ρ) >>= fun ab =>
        run (canonicalDerivation rest) ((ρ.snoc (A := Atom) ab.1).snoc (A := Atom) ab.2) :=
  run_step_proof f (.pair (.slot x) (.slot y)) rest.toProduct ρ

theorem request_mem_proof {A : Type} {f : Request} {arg : Nat × Nat} {k : Nat × Nat → Trace A}
    {z : A} {w : Log} :
    (z, w) ∈ (model.eval f arg >>= k).outcomes ↔
      ∃ reply tail, (z, tail) ∈ (k reply).outcomes ∧ FreeMonoid.of ⟨f, arg, reply⟩ * tail = w := by
  rw [Finite.mem_bind]
  constructor
  · rintro ⟨a, u, v, ⟨reply, hr⟩, hv, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    exact ⟨reply, v, hv, rfl⟩
  · rintro ⟨reply, tail, h, rfl⟩
    exact ⟨reply, _, tail, ⟨reply, rfl⟩, h, rfl⟩

private theorem log_cons_inj {e f : Event} {l r : Log}
    (h : FreeMonoid.of e * l = FreeMonoid.of f * r) : e = f ∧ l = r := by
  have words : e :: l.toList = f :: r.toList := congrArg FreeMonoid.toList h
  exact ⟨(List.cons.inj words).1, FreeMonoid.ext (List.cons.inj words).2⟩

private theorem log_cons_ne_one (e : Event) (l : Log) : FreeMonoid.of e * l ≠ 1 := by
  intro h
  have words : e :: l.toList = [] := congrArg FreeMonoid.toList h
  cases words

/-- Pick a legal run with two fresh atoms at each request. The observation
records those choices, so a second program matching it must use them too. -/
private def sample {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types}
    (w : ProductCanonical β t A) (ρ : BoundEnv Value β) (fresh : Nat) : Value A × Log :=
  match w with
  | .result v => (v.value ρ, 1)
  | .step f arg rest =>
    let ab := (fresh, fresh + 1)
    let suffix := sample rest ((ρ.snoc (A := Atom) ab.1).snoc (A := Atom) ab.2) (fresh + 2)
    (suffix.1, FreeMonoid.of ⟨f, arg.value ρ, ab⟩ * suffix.2)

private theorem sample_mem {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types}
    (w : ProductCanonical β t A) (ρ : BoundEnv Value β) (fresh : Nat) :
    sample w ρ fresh ∈ (run w.derivation ρ).outcomes := by
  induction w generalizing fresh with
  | result v =>
    change (v.value ρ, 1) ∈ (run v.derivation ρ).outcomes
    rw [assembly_run_proof]
    rfl
  | step f arg rest ih =>
    rw [run_step_proof]
    exact request_mem_proof.mpr ⟨(fresh, fresh + 1), _, ih _ _, rfl⟩

private theorem sample_reflect {n : Nat} {β : BoundCtx Types n} {t : Term n} {A : Types}
    (p : ProductCanonical β t A) (ρ : BoundEnv Value β) (fresh : Nat) (sep : Separating ρ fresh) :
    ∀ {u : Term n} (q : ProductCanonical β u A), sample p ρ fresh ∈ (run q.derivation ρ).outcomes → t = u := by
  induction p generalizing fresh with
  | result v =>
    intro u q h
    cases q with
    | result w =>
      change (v.value ρ, 1) ∈ (run w.derivation ρ).outcomes at h
      rw [assembly_run_proof] at h
      have same : (v.value ρ, (1 : Log)) = (w.value ρ, 1) := h
      exact congrArg Assembly.term (assembly_inj ρ fresh sep (Prod.mk.inj same).1)
    | step f arg rest =>
      rw [run_step_proof] at h
      obtain ⟨reply, tail, _, log⟩ := request_mem_proof.mp h
      exact (log_cons_ne_one _ _ log).elim
  | step f arg rest ih =>
    intro u q h
    cases q with
    | result w =>
      change sample (.step f arg rest) ρ fresh ∈ (run w.derivation ρ).outcomes at h
      rw [assembly_run_proof] at h
      have eq : sample (.step f arg rest) ρ fresh = (w.value ρ, 1) := h
      exact (log_cons_ne_one _ _ (congrArg Prod.snd eq)).elim
    | step g other next =>
      rw [run_step_proof] at h
      let ab := (fresh, fresh + 1)
      let extended := (ρ.snoc (A := Atom) ab.1).snoc (A := Atom) ab.2
      let suffix := sample rest extended (fresh + 2)
      have mem : (suffix.1, FreeMonoid.of ⟨f, arg.value ρ, ab⟩ * suffix.2) ∈ _ := h
      obtain ⟨reply, tail, selected, log⟩ := request_mem_proof.mp mem
      obtain ⟨head, tailEq⟩ := log_cons_inj log
      obtain ⟨label, arguments, answer⟩ := Event.mk.inj head
      have sameArg := assembly_inj ρ fresh sep arguments
      cases label
      cases sameArg
      cases answer
      cases tailEq
      exact congrArg (LocallyNameless.Tm.let₂ (.op f arg.term))
        (ih extended (fresh + 2) (separating_snoc_proof (separating_snoc_proof sep)) next selected)

theorem product_canonical_eq_proof {n : Nat} {β : BoundCtx Types n} {t u : Term n} {A : Types}
    (p : ProductCanonical β t A) (q : ProductCanonical β u A) (ρ : BoundEnv Value β) (fresh : Nat)
    (sep : Separating ρ fresh)
    (h : run p.derivation ρ = run q.derivation ρ) : t = u :=
  sample_reflect p ρ fresh sep q (h ▸ sample_mem p ρ fresh)

theorem canonical_eq_proof {n : Nat} {β : BoundCtx Types n} {t u : Term n}
    (p : Canonical β t) (q : Canonical β u) (ρ : BoundEnv Value β) (fresh : Nat)
    (sep : Separating ρ fresh)
    (h : run (canonicalDerivation p) ρ = run (canonicalDerivation q) ρ) : t = u :=
  product_canonical_eq_proof p.toProduct q.toProduct ρ fresh sep h

end Silmaril.Isotope.LetSeq.StraightLine
