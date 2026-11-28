module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Defs
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Coverage
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Environment
import Silmaril.Proofs.SSA.Isotope.LetSeq.StraightLine.Structural.Replay

public section

namespace Silmaril.Isotope.LetSeq.StraightLine.Structural

open LocallyNameless (Derivation Tm)
open Silmaril.Isotope.Semantics (BoundEnv)
open Silmaril.Semantics.NondeterministicTrace
open scoped Structural

variable {α Φ : Type} [Signature α Φ]
set_option backward.isDefEq.respectTransparency false

private theorem slot_run {n : Nat} {β : Context α n} {A : Ty α} (s : Slot β A)
    (ρ : BoundEnv Value β) : run (s.derivation (Φ := Φ)) ρ = pure (s.value ρ) := by
  have evaluation (B : Ty α) (e : β.get s.1 = B) :
      run (cast (congrArg (Derivation Φ Γ₀ β (.bv s.1)) e) .bv) ρ =
        pure (cast (congrArg Value e) (ρ s.1)) := by
    cases e
    rfl
  exact evaluation A s.2

private theorem assembly_run {n : Nat} {β : Context α n} {A : Ty α} (v : Assembly β A)
    (ρ : BoundEnv Value β) : run (v.derivation (Φ := Φ)) ρ = pure (v.value ρ) := by
  induction v with
  | atom s => exact slot_run s ρ
  | unit => rfl
  | pair a b iha ihb =>
    unfold run at iha ihb
    simp only [run, Assembly.derivation, Assembly.value, Derivation.denote, iha, ihb, pure_bind]
    rfl

omit [Signature α Φ] in
private theorem assembly_inj {n : Nat} {β : Context α n} {A : Ty α} {ρ : BoundEnv Value β}
    {used : Set Nat} (sep : Separates ρ used) : Function.Injective (Assembly.value (A := A) ρ) := by
  intro p
  induction p with
  | @atom a s =>
    intro q h
    cases q with
    | atom t => exact congrArg Assembly.atom (sep.injective a h)
  | unit =>
    intro q _
    cases q
    rfl
  | pair a b iha ihb =>
    intro q h
    cases q with
    | pair x y => exact congrArg₂ Assembly.pair (iha (Prod.mk.inj h).1) (ihb (Prod.mk.inj h).2)

theorem run_split {n m : Nat} {β : Context α n} {γ : Context α m} {t : Term Φ m}
    {A : Ty α} (p : Split β γ) (d : Derivation Φ Γ₀ γ t A) (ρ : BoundEnv Value β) :
    run (p.derivation d) ρ = run d (p.env ρ) := by
  induction p with
  | nil => rfl
  | pair s next ih =>
    have hd := slot_run (Φ := Φ) s ρ
    unfold run at hd
    simp only [run, Split.derivation, Split.env, Derivation.denote, hd, pure_bind]
    exact ih d _

theorem run_normal_request {n : Nat} {β : Context α n} {A : Ty α}
    (f : Φ) (a : Assembly β (instrSrc f)) {t : Term Φ (replyUnpack β f).size}
    (next : Normal (replyUnpack β f).context t A) (ρ : BoundEnv Value β) :
    run (Normal.request f a next).derivation ρ =
      (model (α := α)).eval f (a.value ρ) >>= fun x =>
        run next.derivation ((replyUnpack β f).split.env (ρ.snoc x)) := by
  have hd := assembly_run (Φ := Φ) a ρ
  unfold run at hd
  simp only [Normal.derivation, run, Derivation.denote, hd, pure_bind]
  congr 1
  funext x
  exact run_split (replyUnpack β f).split next.derivation _

theorem mem_request {A : Type} {f : Φ} {a : Value (Signature.argument (α := α) f).ty}
    {k : Value (Signature.reply (α := α) f).ty → Trace α Φ A} {z : A} {w : Log α Φ} :
    (z, w) ∈ (((model (α := α)).eval f a) >>= k).outcomes ↔
      ∃ reply tail, (z, tail) ∈ (k reply).outcomes ∧ FreeMonoid.of ⟨f, a, reply⟩ * tail = w := by
  rw [Finite.mem_bind]
  constructor
  · rintro ⟨a, u, v, ⟨reply, hr⟩, hv, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hr
    exact ⟨reply, v, hv, rfl⟩
  · rintro ⟨reply, tail, h, rfl⟩
    exact ⟨reply, _, tail, ⟨reply, rfl⟩, h, rfl⟩

private theorem log_cons_inj {e f : Event (α := α) (Φ := Φ)} {l r : Log α Φ}
    (h : FreeMonoid.of e * l = FreeMonoid.of f * r) : e = f ∧ l = r := by
  have words : e :: l.toList = f :: r.toList := congrArg FreeMonoid.toList h
  exact ⟨(List.cons.inj words).1, FreeMonoid.ext (List.cons.inj words).2⟩

private theorem log_cons_ne_one (e : Event (α := α) (Φ := Φ)) (l : Log α Φ) : FreeMonoid.of e * l ≠ 1 := by
  intro h
  have words : e :: l.toList = [] := congrArg FreeMonoid.toList h
  cases words

private def sample {n : Nat} {β : Context α n} {t : Term Φ n} {A : Ty α}
    (p : Normal β t A) (ρ : BoundEnv Value β) (k : Nat) : Value A × Log α Φ :=
  match p with
  | .ret v => (v.value ρ, 1)
  | .request f a next =>
    let shape := Signature.reply (α := α) f
    let x := shape.fresh k
    let suffix := sample next ((replyUnpack β f).split.env (ρ.snoc x)) (k + shape.leaves)
    (suffix.1, FreeMonoid.of ⟨f, a.value ρ, x⟩ * suffix.2)

private theorem sample_mem {n : Nat} {β : Context α n} {t : Term Φ n} {A : Ty α}
    (p : Normal β t A) (ρ : BoundEnv Value β) (k : Nat) :
    sample p ρ k ∈ (run p.derivation ρ).outcomes := by
  induction p generalizing k with
  | ret v =>
    change (v.value ρ, 1) ∈ (run v.derivation ρ).outcomes
    rw [assembly_run]
    rfl
  | request f a next ih =>
    rw [run_normal_request]
    exact mem_request.mpr ⟨(Signature.reply f).fresh k, _, ih _ _, rfl⟩

private theorem sample_reflect {n : Nat} {β : Context α n} {t : Term Φ n} {A : Ty α}
    (p : Normal β t A) (ρ : BoundEnv Value β) (k : Nat) (sep : Separates ρ (Set.Iio k)) :
    ∀ {u : Term Φ n} (q : Normal β u A),
      sample p ρ k ∈ (run q.derivation ρ).outcomes → t = u := by
  induction p generalizing k with
  | ret v =>
    intro u q h
    cases q with
    | ret w =>
      change (v.value ρ, 1) ∈ (run w.derivation ρ).outcomes at h
      rw [assembly_run] at h
      have same : (v.value ρ, (1 : Log α Φ)) = (w.value ρ, 1) := h
      exact congrArg Assembly.term (assembly_inj sep (Prod.mk.inj same).1)
    | request f arg next =>
      rw [run_normal_request] at h
      obtain ⟨reply, tail, _, log⟩ := mem_request.mp h
      exact (log_cons_ne_one _ _ log).elim
  | @request _ β _ f a _ next ih =>
    intro u q h
    cases q with
    | ret w =>
      change sample (.request f a next) ρ k ∈ (run w.derivation ρ).outcomes at h
      rw [assembly_run] at h
      have eq : sample (.request f a next) ρ k = (w.value ρ, 1) := h
      exact (log_cons_ne_one _ _ (congrArg Prod.snd eq)).elim
    | request g b other =>
      rw [run_normal_request] at h
      let shape := Signature.reply (α := α) f
      let x := shape.fresh k
      let extended := (replyUnpack β f).split.env (ρ.snoc x)
      let suffix := sample next extended (k + shape.leaves)
      have mem : (suffix.1, FreeMonoid.of ⟨f, a.value ρ, x⟩ * suffix.2) ∈ _ := h
      obtain ⟨reply, tail, selected, log⟩ := mem_request.mp mem
      obtain ⟨head, tailEq⟩ := log_cons_inj log
      have generator : g = f := congrArg Event.generator head
      subst g
      have fields := Event.mk.inj head
      have sameArg := assembly_inj sep (eq_of_heq fields.2.1)
      have sameReply := eq_of_heq fields.2.2
      cases sameArg
      cases sameReply
      cases tailEq
      exact congrArg (fun t => Tm.let₁ (.op f a.term) ((replyUnpack β f).split.wrap t))
        (ih extended (k + shape.leaves) (fresh_after sep shape) other selected)

theorem normal_eq_of_run {n : Nat} {β : Context α n} {t u : Term Φ n} {A : Ty α}
    (p : Normal β t A) (q : Normal β u A) (ρ : BoundEnv Value β) (k : Nat)
    (sep : Separates ρ (Set.Iio k)) (h : run p.derivation ρ = run q.derivation ρ) : t = u :=
  sample_reflect p ρ k sep q (h ▸ sample_mem p ρ k)

end Silmaril.Isotope.LetSeq.StraightLine.Structural
