module

public import Silmaril.SSA.Isotope.LetCase.Structural.Finite.Defs
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Finite.Substitution
import Silmaril.Proofs.SSA.Isotope.LetCase.Structural.Finite.Extensional
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum

public section

namespace Silmaril.Isotope.LetCase.Structural.Finite

open LocallyNameless (Derivation Equiv Tm)
open Reply (Γ₀ run)
open LetSeq.StraightLine.Structural (Event Log Trace model)
open Silmaril.Isotope.Semantics (BoundEnv)
open Silmaril.Semantics.NondeterministicTrace

open Silmaril.Semantics.NondeterministicTrace.Finite renaming mem_bind → trace_mem_bind
open scoped Silmaril.Isotope.LetCase.Structural.Finite LetSeq.StraightLine.Structural

variable {Φ : Type} [Signature Φ]
set_option backward.isDefEq.respectTransparency false

abbrev closedEnv : BoundEnv Value (.nil : Context 0) := fun i => i.elim0

theorem run_of_equiv {n : Nat} {β : Context n} {t u : Term Φ n} {A : Types}
    (d : Derivation Φ Γ₀ β t A) (e : Derivation Φ Γ₀ β u A)
    (h : Equiv false Γ₀ β t u A) (ρ : BoundEnv Value β) : run d ρ = run e ρ :=
  (Reply.traceArrow_eq_iff_run d e).mp (Reply.traceArrow_of_valid (Reply.valid_of_equiv d e h)) ρ

private theorem constructor_run {n : Nat} {β : Context n} {A : Types}
    (a : Constructor A) (ρ : BoundEnv Value β) :
    run (a.typing (Φ := Φ)) ρ = pure a.value := by
  induction a with
  | unit => rfl
  | pair a b ha hb =>
    change (run a.typing ρ >>= fun x => run b.typing ρ >>= fun y => pure (x, y)) = _
    rw [ha, hb, pure_bind, pure_bind]
    rfl
  | inl a ih =>
    change (run a.typing ρ >>= fun x => pure (Sum.inl x)) = _
    rw [ih, pure_bind]
    rfl
  | inr a ih =>
    change (run a.typing ρ >>= fun x => pure (Sum.inr x)) = _
    rw [ih, pure_bind]
    rfl

omit [Signature Φ] in
theorem Constructor.value_injective {A : Types} : Function.Injective (Constructor.value (A := A)) := by
  intro a
  induction a with
  | unit => intro b _; cases b; rfl
  | pair a b ha hb =>
    intro c h
    cases c with
    | pair x y =>
      obtain ⟨hx, hy⟩ := Prod.mk.inj h
      rw [ha hx, hb hy]
  | inl a ih =>
    intro b h
    cases b with
    | inl b => rw [ih (Sum.inl.inj h)]
    | inr b => cases h
  | inr a ih =>
    intro b h
    cases b with
    | inl b => cases h
    | inr b => rw [ih (Sum.inr.inj h)]

omit [Signature Φ] in
theorem Shape.finite_constructors_proof (s : Shape) : _root_.Finite (Constructor s.ty) := by
  have finiteValues : _root_.Finite (Value s.ty) := by
    induction s with
    | unit => exact inferInstanceAs (_root_.Finite PUnit)
    | pair a b ha hb =>
      exact inferInstanceAs (_root_.Finite (Value a.ty × Value b.ty))
    | sum a b ha hb =>
      exact inferInstanceAs (_root_.Finite (Value a.ty ⊕ Value b.ty))
  exact _root_.Finite.of_injective _ Constructor.value_injective

private abbrev event (f : Φ) (a : Constructor (instrSrc f)) (x : Value (instrTrg f)) : Log Empty Φ :=
  FreeMonoid.of ⟨f, a.value, x⟩

private theorem request_run {A : Types} {b : Term Φ 1} (f : Φ) (a : Constructor (instrSrc f))
    (d : Derivation Φ Γ₀ (.snoc .nil (instrTrg f)) b A) :
    run (.let₁ (.op (f := f) a.typing) d) closedEnv =
      ((model (α := Empty)).eval f a.value >>= fun x => run d (closedEnv.snoc x)) := by
  change ((run a.typing closedEnv >>= (model (α := Empty)).eval f) >>= _) = _
  rw [constructor_run, pure_bind]
  rfl


theorem run_instantiate {n : Nat} {β : Context n} {A B : Types}
    {b : Term Φ (n + 1)} {t : Term Φ n}
    (d : Derivation Φ Γ₀ (.snoc β B) b A) (x : Constructor B)
    (p : Derivation Φ Γ₀ β t A)
    (h : Equiv false Γ₀ β (Tm.instantiate b x.term) t A)
    (ρ : BoundEnv Value β) :
    run d (ρ.snoc x.value) = run p ρ := by
  have eq := run_of_equiv (.let₁ x.typing d) p
    ((Equiv.letBeta x.pure x.typing.toHasType d.toHasType).trans h) ρ
  change (run x.typing ρ >>= fun y => run d (ρ.snoc y)) = _ at eq
  rwa [constructor_run, pure_bind] at eq

theorem Head.run_nonempty {A : Types} {t : Term Φ 0} (p : Head A t) :
    (run p.typing closedEnv).outcomes.Nonempty := by
  induction p with
  | ret a =>
    rw [Head.typing, constructor_run]
    exact ⟨(a.value, 1), rfl⟩
  | request f a d _ heads replay ih =>
    let x := (Signature.target f).witness
    obtain ⟨⟨result, tail⟩, ht⟩ := ih x
    rw [Head.typing, request_run]
    exact ⟨(result, event f a x.value * tail), trace_mem_bind.mpr
      ⟨x.value, event f a x.value, tail, ⟨x.value, rfl⟩, run_instantiate d x (heads x).typing (replay x) closedEnv ▸ ht, rfl⟩⟩

private theorem request_first {A : Types} {b : Term Φ 1} (f : Φ) (a : Constructor (instrSrc f))
    (d : Derivation Φ Γ₀ (.snoc .nil (instrTrg f)) b A)
    {v : Value A} {w : Log Empty Φ}
    (h : (v, w) ∈ (run (.let₁ (.op (f := f) a.typing) d) closedEnv).outcomes) :
    ∃ x tail, w = event f a x * tail := by
  rw [request_run] at h
  obtain ⟨x, first, tail, ⟨y, hy⟩, _, hw⟩ := trace_mem_bind.mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy
  exact ⟨y, tail, hw.symm⟩

private theorem request_head_eq {A : Types}
    {f g : Φ} {a : Constructor (instrSrc f)} {b : Constructor (instrSrc g)}
    {k l : Term Φ 1} {dk : Derivation Φ Γ₀ (.snoc .nil (instrTrg f)) k A}
    {dl : Derivation Φ Γ₀ (.snoc .nil (instrTrg g)) l A}
    {next : Constructor (instrTrg f) → Term Φ 0} {next' : Constructor (instrTrg g) → Term Φ 0}
    (p : ∀ x, Head A (next x)) (q : ∀ x, Head A (next' x))
    (hp : ∀ x, Equiv false Γ₀ .nil (Tm.instantiate k x.term) (next x) A)
    (hq : ∀ x, Equiv false Γ₀ .nil (Tm.instantiate l x.term) (next' x) A)
    (eq : run (Head.request f a dk next p hp).typing closedEnv =
      run (Head.request g b dl next' q hq).typing closedEnv) :
    f = g ∧ HEq a b := by
  obtain ⟨⟨v, w⟩, hv⟩ := (Head.request f a dk next p hp).run_nonempty
  have hw := hv
  rw [eq] at hw
  obtain ⟨x, tail, left⟩ := request_first f a dk hv
  obtain ⟨y, rest, right⟩ := request_first g b dl hw
  have words := congrArg FreeMonoid.toList (left.symm.trans right)
  have first : Event.mk f a.value x = Event.mk g b.value y := (List.cons.inj words).1
  obtain ⟨same, args, _⟩ := Event.mk.inj first
  subst g
  exact ⟨rfl, heq_of_eq (Constructor.value_injective (eq_of_heq args))⟩

private theorem request_head_replies {A : Types} {f : Φ} {a : Constructor (instrSrc f)}
    {k l : Term Φ 1} {dk : Derivation Φ Γ₀ (.snoc .nil (instrTrg f)) k A}
    {dl : Derivation Φ Γ₀ (.snoc .nil (instrTrg f)) l A}
    {next next' : Constructor (instrTrg f) → Term Φ 0}
    (p : ∀ x, Head A (next x)) (q : ∀ x, Head A (next' x))
    (hp : ∀ x, Equiv false Γ₀ .nil (Tm.instantiate k x.term) (next x) A)
    (hq : ∀ x, Equiv false Γ₀ .nil (Tm.instantiate l x.term) (next' x) A)
    (eq : run (Head.request f a dk next p hp).typing closedEnv =
      run (Head.request f a dl next' q hq).typing closedEnv)
    (x : Constructor (instrTrg f)) :
    run (p x).typing closedEnv = run (q x).typing closedEnv := by
  have pref : Reply.PrefixDetermined (run (.op (f := f) a.typing) closedEnv) :=
    Reply.run_prefix_determined _ _
  change Reply.PrefixDetermined (run a.typing closedEnv >>= (model (α := Empty)).eval f) at pref
  rw [constructor_run, pure_bind] at pref
  simp only [Head.typing, request_run] at eq
  have eq' := (Reply.bind_eq_iff_for_replies pref _ _).mp eq x.value (event f a x.value) ⟨x.value, rfl⟩
  exact (run_instantiate dk x (p x).typing (hp x) closedEnv).symm.trans
    (eq'.trans (run_instantiate dl x (q x).typing (hq x) closedEnv))

private theorem return_request_ne {A : Types} (v : Constructor A)
    {f : Φ} {arg : Constructor (instrSrc f)}
    {k : Term Φ 1} {dk : Derivation Φ Γ₀ (.snoc .nil (instrTrg f)) k A}
    {next : Constructor (instrTrg f) → Term Φ 0}
    (p : ∀ x, Head A (next x))
    (replay : ∀ x, Equiv false Γ₀ .nil (Tm.instantiate k x.term) (next x) A) :
    run (Head.ret (Φ := Φ) v).typing closedEnv ≠
      run (Head.request f arg dk next p replay).typing closedEnv := by
  intro eq
  have obs : (v.value, 1) ∈ (run (Head.ret (Φ := Φ) v).typing closedEnv).outcomes := by
    rw [Head.typing, constructor_run]
    rfl
  rw [eq] at obs
  obtain ⟨x, tail, h⟩ := request_first f arg dk obs
  have words : [] = Event.mk f arg.value x :: tail.toList := congrArg FreeMonoid.toList h
  cases words

/-- Reflect native equivalence of witnessed heads using recorded typed events,
cancellation on each reachable reply, and native constructor extensionality. -/
theorem Head.reflect_proof {A : Types} {t u : Term Φ 0} (p : Head A t) (q : Head A u)
    (eq : run p.typing closedEnv = run q.typing closedEnv) :
    Equiv false Γ₀ .nil t u A := by
  induction p generalizing u with
  | ret a =>
    cases q with
    | ret b =>
      simp only [Head.typing, constructor_run] at eq
      have h : (a.value, 1) ∈ (pure a.value : Trace Empty Φ (Value A)).outcomes := rfl
      rw [eq] at h
      have equal : (a.value, (1 : Log Empty Φ)) = (b.value, 1) := h
      obtain rfl := Constructor.value_injective (Prod.mk.inj equal).1
      exact .refl a.typing.toHasType
    | request _ _ _ _ heads replay => exact (return_request_ne a heads replay eq).elim
  | request f a dk _ p hp ih =>
    cases q with
    | ret b => exact (return_request_ne b p hp eq.symm).elim
    | request g b dl _ q hq =>
      obtain ⟨rfl, same⟩ := request_head_eq p q hp hq eq
      obtain rfl := eq_of_heq same
      apply Equiv.let₁ (.refl (.op a.typing.toHasType))
      apply constructor_ext_type_proof (Signature.target f).ty dk.toHasType dl.toHasType
      intro x
      exact (hp x).trans ((ih x (q x) (request_head_replies p q hp hq eq x)).trans (hq x).symm)

end Silmaril.Isotope.LetCase.Structural.Finite
