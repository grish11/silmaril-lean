module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Category.Syntax.Iteration.SequencingObstruction.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction.Terms
import Silmaril.Raw.SSA.Isotope.LambdaSSA.Substitution

/-! # A separating observation for the native CFG rules -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.SequencingObstruction
open Silmaril.DeBruijn (lift liftN liftN_lt liftN_ge)
open Silmaril.Isotope.LambdaSSA.Semantics (extend)

structure Exit where
  label : Nat
  value : Val
  effect : Bool
  marked : Bool

@[expose] def Exit.relabel (x : Exit) (f : Nat → Nat) : Exit :=
  { x with label := f x.label }

@[expose] def Exit.prepend (x : Exit) (effect marked : Bool) : Exit :=
  { x with effect := effect || x.effect, marked := marked || x.marked }

@[expose] def Exit.branch (label : Nat) (v : Val) (effect : Bool) : Exit :=
  ⟨label, v, effect, false⟩

/-- The native diagnostic and the Paper diagnostic share their finite-run
calculus and choose different arities at which to add marks. Suppressing
unary bind and case effects lets the same diagnostic test entry-let
extensions while retaining effects of product destructuring. -/
class MarkArity where
  enabled : Nat → Bool
  keepUnaryEffect : Bool := true

section
set_option linter.concreteInstances false
variable [MarkArity]

@[expose] def markAt (n : Nat) (first : Exit) (remaining : Nat) : Bool :=
  first.marked || (MarkArity.enabled n && first.effect && decide (1 ≤ remaining))

/-- Count transfers within one CFG. An enabled arity marks an effect with
at least two local transfers still ahead. Observations from nested binders
retain their marks independently of the current count. -/
inductive Follow {n : Nat} (block : Fin n → Val → Exit → Prop) :
    Exit → Nat → Exit → Prop where
  | exit {first : Exit} (h : n ≤ first.label) :
      Follow block first 0 (first.relabel (· - n))
  | step {first next out : Exit} {count : Nat} (h : first.label < n)
      (head : block ⟨first.label, h⟩ first.value next) (tail : Follow block next count out) :
      Follow block first (count + 1)
        (out.prepend first.effect (markAt n first count))

@[expose] def withTerm (keepEffect : Bool) (env : Env) (a : Tm Instruction) (body : Val → Exit → Prop) (out : Exit) : Prop :=
  ∃ v e, term env a = some (v, e) ∧ ∃ x, body v x ∧ out = x.prepend (keepEffect && e) false

@[expose] def observe (env : Env) : Region Instruction → Exit → Prop
  | .br i a => fun out => ∃ v e, term env a = some (v, e) ∧ out = Exit.branch i v e
  | .let₁ a r => withTerm MarkArity.keepUnaryEffect env a (fun v => observe (extend env v) r)
  | .let₂ a r => withTerm true env a (fun
      | .pair v w => observe (extend (extend env v) w) r
      | _ => fun _ => False)
  | .case a l r => withTerm MarkArity.keepUnaryEffect env a (fun
      | .inl v => observe (extend env v) l
      | .inr w => observe (extend env w) r
      | _ => fun _ => False)
  | .cfg r _ blocks => fun out =>
      ∃ first count, observe env r first ∧
        Follow (fun i v => observe (extend env v) (blocks i)) first count out

omit [MarkArity] in
private theorem withTerm_congr {keepEffect : Bool} {env env' : Env} {a a' : Tm Instruction}
    {f g : Val → Exit → Prop} (ht : term env a = term env' a')
    (h : ∀ v e, term env' a' = some (v, e) → f v = g v) :
    withTerm keepEffect env a f = withTerm keepEffect env' a' g := by
  funext out
  apply propext
  unfold withTerm
  rw [ht]
  constructor
  · rintro ⟨v, e, hv, x, hx, rfl⟩
    exact ⟨v, e, hv, x, h v e hv ▸ hx, rfl⟩
  · rintro ⟨v, e, hv, x, hx, rfl⟩
    exact ⟨v, e, hv, x, (h v e hv).symm ▸ hx, rfl⟩

theorem observe_subst (r : Region Instruction) {env env' : Env} {σ : Nat → Tm Instruction}
    (h : ∀ i, term env (σ i) = some (env' i, false)) :
    observe env (r.substVars σ) = observe env' r := by
  induction r generalizing env env' σ with
  | br i a => simp only [Region.substVars, observe, term_subst _ h]
  | let₁ a r ih =>
    exact withTerm_congr (term_subst _ h) (fun v _ _ => ih (lift_realizes h v))
  | let₂ a r ih =>
    apply withTerm_congr (term_subst _ h)
    intro v _ _
    cases v <;> simp [ih (lift_realizes (lift_realizes h _) _), Tm.liftSubstN]
  | case a l r il ir =>
    apply withTerm_congr (term_subst _ h)
    intro v _ _
    cases v <;> simp [il (lift_realizes h _), ir (lift_realizes h _)]
  | cfg r n blocks ih ib =>
    simp only [Region.substVars, observe, ih h, ib _ (lift_realizes h _)]

omit [MarkArity] in
theorem single_realizes {env : Env} {a : Tm Instruction} {v : Val} (h : term env a = some (v, false)) :
    ∀ i, term env (Tm.singleSubst a i) = some (extend env v i, false) := by
  intro i
  cases i with
  | zero => exact h
  | succ i => rfl

omit [MarkArity] in
private theorem replace_realizes (env : Env) (arg : Val) :
    (∀ i, term (extend env arg) (Tm.replaceNewest (.inl (.var 0)) i) =
        some (extend env (.inl arg) i, false)) ∧
      (∀ i, term (extend env arg) (Tm.replaceNewest (.inr (.var 0)) i) =
        some (extend env (.inr arg) i, false)) := by
  constructor <;> intro i <;> cases i <;> rfl

omit [MarkArity] in
@[simp] theorem prepend_false (o : Exit) : o.prepend false false = o := by
  cases o; rfl

omit [MarkArity] in
theorem withTerm_value {keepEffect : Bool} {env : Env} {a : Tm Instruction} {v : Val}
    (h : term env a = some (v, false)) (body : Val → Exit → Prop) :
    withTerm keepEffect env a body = body v := by
  funext out
  simp [withTerm, h]

private theorem follow_rename {n : Nat} {f g : Fin n → Val → Exit → Prop}
    (ρ : Nat → Nat)
    (h : ∀ i v x, g i v x ↔ ∃ y, f i v y ∧ x = y.relabel (liftN n ρ))
    (first : Exit) (count : Nat) (x : Exit) :
    Follow g (first.relabel (liftN n ρ)) count x ↔
      ∃ y, Follow f first count y ∧ x = y.relabel ρ := by
  constructor
  · intro hx
    generalize heq : first.relabel (liftN n ρ) = first' at hx
    induction hx generalizing first with
    | @exit start outside =>
      subst start
      have hn : n ≤ first.label := by
        by_contra hn
        have hl := liftN_lt ρ (n := n) (i := first.label) (by omega)
        simp only [Exit.relabel, hl] at outside
        omega
      refine ⟨_, .exit hn, ?_⟩
      simp [Exit.relabel, liftN_ge ρ hn]
    | @step start next out k inside head _ ih =>
      subst start
      have hn : first.label < n := by
        by_contra hn
        have hl := liftN_ge ρ (n := n) (i := first.label) (by omega)
        simp only [Exit.relabel, hl] at inside
        omega
      have hi := liftN_lt ρ hn
      have head' : g ⟨first.label, hn⟩ first.value next := by
        simpa only [Exit.relabel, hi] using head
      obtain ⟨next', hb, rfl⟩ := (h _ _ _).mp head'
      obtain ⟨out', ht, rfl⟩ := ih next' rfl
      exact ⟨_, .step hn hb ht, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    induction hy with
    | @exit start outside =>
      have hn : n ≤ (start.relabel (liftN n ρ)).label := by
        simp [Exit.relabel, liftN_ge ρ outside]
      convert Follow.exit (block := g) hn using 1
      simp [Exit.relabel, liftN_ge ρ outside]
    | @step start next out k inside head _ ih =>
      have hn : (start.relabel (liftN n ρ)).label < n := by
        simp [Exit.relabel, liftN_lt ρ inside, inside]
      apply Follow.step hn _ ih
      simp only [Exit.relabel, liftN_lt ρ inside]
      exact (h _ _ _).mpr ⟨_, head, rfl⟩

omit [MarkArity] in
private theorem withTerm_rename {keepEffect : Bool} {env : Env} {a : Tm Instruction} {f g : Val → Exit → Prop}
    (ρ : Nat → Nat) (h : ∀ v x, g v x ↔ ∃ y, f v y ∧ x = y.relabel ρ) (x : Exit) :
    withTerm keepEffect env a g x ↔ ∃ y, withTerm keepEffect env a f y ∧ x = y.relabel ρ := by
  constructor
  · rintro ⟨v, e, hv, z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := (h v z).mp hz
    exact ⟨_, ⟨v, e, hv, y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨v, e, hv, z, hz, rfl⟩, rfl⟩
    exact ⟨v, e, hv, _, (h v _).mpr ⟨z, hz, rfl⟩, rfl⟩

theorem observe_renameLabels (r : Region Instruction) (ρ : Nat → Nat) (env : Env) (x : Exit) :
    observe env (r.renameLabels ρ) x ↔ ∃ y, observe env r y ∧ x = y.relabel ρ := by
  induction r generalizing env x ρ with
  | br i a =>
    exact ⟨fun ⟨v, e, h, hx⟩ => ⟨_, ⟨v, e, h, rfl⟩, hx⟩,
      fun ⟨_, ⟨v, e, h, rfl⟩, hx⟩ => ⟨v, e, h, hx⟩⟩
  | let₁ a r ih => exact withTerm_rename ρ (fun v z => ih ρ (extend env v) z) x
  | let₂ a r ih =>
    apply withTerm_rename ρ _ x
    intro v z
    cases v <;> simp [ih]
  | case a l r il ir =>
    apply withTerm_rename ρ _ x
    intro v z
    cases v <;> simp [il, ir]
  | cfg entry n blocks ie ib =>
    change (∃ first k, observe env (entry.renameLabels (liftN n ρ)) first ∧
      Follow (fun i v => observe (extend env v) ((blocks i).renameLabels (liftN n ρ))) first k x) ↔ _
    have hf := follow_rename (n := n) (f := fun i v => observe (extend env v) (blocks i))
      (g := fun i v => observe (extend env v) ((blocks i).renameLabels (liftN n ρ)))
      ρ (fun i v z => ib i _ _ z)
    constructor
    · rintro ⟨first, k, he, hl⟩
      obtain ⟨first', he', rfl⟩ := (ie _ _ _).mp he
      obtain ⟨y, hy, rfl⟩ := (hf first' k x).mp hl
      exact ⟨y, ⟨first', k, he', hy⟩, rfl⟩
    · rintro ⟨y, ⟨first, k, he, hl⟩, rfl⟩
      exact ⟨_, k, (ie _ _ _).mpr ⟨first, he, rfl⟩, (hf first k _).mpr ⟨y, hl, rfl⟩⟩

@[expose] def Exit.WellTyped (L : LCtx (Ty Empty)) (x : Exit) : Prop :=
  ∃ A, At L x.label A ∧ Typed x.value A

omit [MarkArity] in
private theorem prepend_typed {L : LCtx (Ty Empty)} {x : Exit} {e m : Bool}
    (h : x.WellTyped L) : (x.prepend e m).WellTyped L := h

private theorem follow_mapTyped {n : Nat} (R : Fin n → Ty Empty) (L : LCtx (Ty Empty))
    {f g : Fin n → Val → Exit → Prop}
    (h : ∀ i v x, Typed v (R i) → f i v x → x.WellTyped (List.ofFn R ++ L) ∧ g i v x)
    {first out : Exit} {k : Nat} (run : Follow f first k out)
    (ht : first.WellTyped (List.ofFn R ++ L)) : out.WellTyped L ∧ Follow g first k out := by
  induction run with
  | exit outside =>
    obtain ⟨A, hi, hv⟩ := ht
    change (List.ofFn R ++ L)[_]? = some A at hi
    rw [List.getElem?_append_right (by simpa only [List.length_ofFn] using outside),
      List.length_ofFn] at hi
    exact ⟨⟨A, hi, hv⟩, .exit outside⟩
  | @step first next out count inside head _ ih =>
    obtain ⟨A, hi, hv⟩ := ht
    have he := localAt R ⟨first.label, inside⟩ L
    have eq : A = R ⟨first.label, inside⟩ := Option.some.inj (hi.symm.trans he)
    obtain ⟨hn, hg⟩ := h _ _ _ (eq ▸ hv) head
    obtain ⟨ho, tail⟩ := ih hn
    exact ⟨ho, .step inside hg tail⟩

theorem observe_typed {Γ : VCtx (Ty Empty)} {r : Region Instruction} {L : LCtx (Ty Empty)}
    (hr : Region.HasType Γ r L) {env : Env} (he : EnvTyped Γ env)
    {out : Exit} (h : observe env r out) : out.WellTyped L := by
  induction hr generalizing env out with
  | br hi ha =>
    obtain ⟨v, e, ht, rfl⟩ := h
    exact ⟨_, hi, term_typed ha he ht⟩
  | let₁ ha _ ih =>
    obtain ⟨_, _, ht, x, hx, rfl⟩ := h
    exact prepend_typed (ih (he.extend (term_typed ha he ht)) hx)
  | let₂ ha _ ih =>
    obtain ⟨v, _, ht, x, hx, rfl⟩ := h
    have hv := term_typed ha he ht
    cases hv with
    | pair ha hb => exact prepend_typed (ih ((he.extend ha).extend hb) hx)
  | case ha _ _ il ir =>
    obtain ⟨v, _, ht, x, hx, rfl⟩ := h
    have hv := term_typed ha he ht
    cases hv with
    | inl h => exact prepend_typed (il (he.extend h) hx)
    | inr h => exact prepend_typed (ir (he.extend h) hx)
  | cfg R _ _ ie ib =>
    obtain ⟨first, _, hfirst, hf⟩ := h
    exact (follow_mapTyped R _ (fun i _ _ hv hx => ⟨ib i (he.extend hv) hx, hx⟩)
      hf (ie he hfirst)).1

@[expose] def Preserves (Γ : VCtx (Ty Empty)) (r s : Region Instruction) : Prop :=
  ∀ env, EnvTyped Γ env → observe env r = observe env s

theorem preserves_let₁ {Γ : VCtx (Ty Empty)} {A : Ty Empty} {a : Tm Instruction}
    {r s : Region Instruction} (ha : Tm.HasType Γ a A) (h : Preserves (A :: Γ) r s) :
    Preserves Γ (.let₁ a r) (.let₁ a s) := by
  intro env he
  exact withTerm_congr rfl (fun v _ hv => h (extend env v) (he.extend (term_typed ha he hv)))

theorem preserves_let₂ {Γ : VCtx (Ty Empty)} {A B : Ty Empty} {a : Tm Instruction}
    {r s : Region Instruction} (ha : Tm.HasType Γ a (.product A B)) (h : Preserves (B :: A :: Γ) r s) :
    Preserves Γ (.let₂ a r) (.let₂ a s) := by
  intro env he
  apply withTerm_congr rfl
  intro v _ hv
  have ht := term_typed ha he hv
  cases ht with
  | pair ha hb => exact h _ ((he.extend ha).extend hb)

theorem preserves_case {Γ : VCtx (Ty Empty)} {A B : Ty Empty} {a : Tm Instruction}
    {l l' r r' : Region Instruction} (ha : Tm.HasType Γ a (.coprod A B))
    (hl : Preserves (A :: Γ) l l') (hr : Preserves (B :: Γ) r r') :
    Preserves Γ (.case a l r) (.case a l' r') := by
  intro env he
  apply withTerm_congr rfl
  intro v _ hv
  have ht := term_typed ha he hv
  cases ht with
  | inl ha => exact hl _ (he.extend ha)
  | inr hb => exact hr _ (he.extend hb)

theorem preserves_cfg {n : Nat} {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)}
    {r s : Region Instruction} {f g : Fin n → Region Instruction} (R : Fin n → Ty Empty)
    (hr : Region.HasType Γ r (List.ofFn R ++ L)) (hs : Region.HasType Γ s (List.ofFn R ++ L))
    (hf : ∀ i, Region.HasType (R i :: Γ) (f i) (List.ofFn R ++ L))
    (hg : ∀ i, Region.HasType (R i :: Γ) (g i) (List.ofFn R ++ L))
    (he : Preserves Γ r s) (hb : ∀ i, Preserves (R i :: Γ) (f i) (g i)) :
    Preserves Γ (.cfg r n f) (.cfg s n g) := by
  intro env ht
  funext out
  apply propext
  constructor
  · rintro ⟨first, count, entry, tail⟩
    exact ⟨first, count, he env ht ▸ entry,
      (follow_mapTyped R L (fun i _ _ hv hx =>
        ⟨observe_typed (hf i) (ht.extend hv) hx, hb i _ (ht.extend hv) ▸ hx⟩)
        tail (observe_typed hr ht entry)).2⟩
  · rintro ⟨first, count, entry, tail⟩
    exact ⟨first, count, (he env ht).symm ▸ entry,
      (follow_mapTyped R L (fun i _ _ hv hx =>
        ⟨observe_typed (hg i) (ht.extend hv) hx, (hb i _ (ht.extend hv)).symm ▸ hx⟩)
        tail (observe_typed hs ht entry)).2⟩

theorem follow_outward {n : Nat} {f : Fin n → Val → Exit → Prop} {first out : Exit}
    {k : Nat} (h : n ≤ first.label) :
    Follow f first k out ↔ k = 0 ∧ out = first.relabel (· - n) := by
  constructor
  · intro hf
    cases hf with
    | exit => exact ⟨rfl, rfl⟩
    | step hin _ _ => exact False.elim ((Nat.not_lt_of_ge h) hin)
  · rintro ⟨rfl, rfl⟩
    exact .exit h

private theorem observe_outward (r : Region Instruction) (n : Nat) (blocks : Fin n → Region Instruction) (env : Env) :
    observe env (.cfg (r.renameLabels (n + ·)) n blocks) = observe env r := by
  funext out
  apply propext
  constructor
  · rintro ⟨x, k, hx, hfollow⟩
    obtain ⟨y, hy, rfl⟩ := (observe_renameLabels r (n + ·) env x).mp hx
    have hout : n ≤ (y.relabel (n + ·)).label := by simp [Exit.relabel]
    obtain ⟨_, rfl⟩ := (follow_outward hout).mp hfollow
    simpa [Exit.relabel] using hy
  · intro hx
    refine ⟨out.relabel (n + ·), 0, (observe_renameLabels _ _ _ _).mpr ⟨out, hx, rfl⟩, ?_⟩
    apply (follow_outward (by simp [Exit.relabel])).mpr
    simp [Exit.relabel]

private theorem observe_cfg_zero (r : Region Instruction) (blocks : Fin 0 → Region Instruction) (env : Env) :
    observe env (.cfg r 0 blocks) = observe env r := by
  simpa only [Nat.zero_add, show (fun x : Nat => x) = id from rfl, Region.renameLabels_id] using observe_outward r 0 blocks env

theorem observe_br {env : Env} {a : Tm Instruction} {v : Val} {e : Bool}
    (h : term env a = some (v, e)) (i : Nat) :
    observe env (.br i a) = (· = Exit.branch i v e) := by
  funext out
  cases e <;> simp [observe, h]

private theorem observe_cfg_local {n : Nat} {env : Env} {a : Tm Instruction} {v : Val}
    (h : term env a = some (v, false)) (i : Fin n) (blocks : Fin n → Region Instruction) :
    observe env (.cfg (.br i a) n blocks) = observe env (.cfg (.let₁ a (blocks i)) n blocks) := by
  funext out
  apply propext
  change (∃ x k, observe env (.br i a) x ∧
    Follow (fun j w => observe (extend env w) (blocks j)) x k out) ↔
      ∃ x k, withTerm MarkArity.keepUnaryEffect env a (fun w => observe (extend env w) (blocks i)) x ∧
        Follow (fun j w => observe (extend env w) (blocks j)) x k out
  rw [observe_br h, withTerm_value h]
  constructor
  · rintro ⟨x, k, rfl, run⟩
    cases run with
    | exit he => exact False.elim ((Nat.not_lt_of_ge he) i.isLt)
    | @step _ x _ k hi hx ht => exact ⟨x, k, hx, by simpa [Exit.branch, markAt] using ht⟩
  · rintro ⟨x, k, hx, ht⟩
    exact ⟨_, k + 1, rfl, by
      simpa [Exit.branch, markAt] using Follow.step (first := Exit.branch i v false) i.isLt hx ht⟩

private theorem observe_letValue {Γ : VCtx (Ty Empty)} {A : Ty Empty} {a : Tm Instruction}
    {r : Region Instruction} (ha : Tm.BranchValue Γ a A) :
    Preserves Γ (.let₁ a r) (r.substVars (Tm.singleSubst a)) := by
  intro env _
  obtain ⟨v, hv⟩ := value_term ha env
  exact (withTerm_value hv _).trans (observe_subst r (single_realizes hv)).symm

private theorem observe_cfg_exit {n i : Nat} (h : n ≤ i) (env : Env) (a : Tm Instruction)
    (blocks : Fin n → Region Instruction) :
    observe env (.cfg (.br i a) n blocks) = observe env (.br (i - n) a) := by
  have he : Region.renameLabels (n + ·) (.br (i - n) a) = .br i a := by
    simp [Region.renameLabels, Nat.add_sub_of_le h]
  have ho := observe_outward (.br (i - n) a) n blocks env
  rwa [he] at ho

private theorem observe_caseValue {Γ : VCtx (Ty Empty)} {A B : Ty Empty} {a : Tm Instruction}
    {r : Region Instruction} (ha : Tm.BranchValue Γ a (.coprod A B)) :
    Preserves Γ
      (.case a (r.substVars (Tm.replaceNewest (.inl (.var 0))))
        (r.substVars (Tm.replaceNewest (.inr (.var 0)))))
      (r.substVars (Tm.singleSubst a)) := by
  intro env he
  obtain ⟨v, hv⟩ := value_term ha env
  have ht := term_typed ha.hasType he hv
  rw [observe_subst _ (single_realizes hv)]
  change withTerm MarkArity.keepUnaryEffect env a _ = _
  rw [withTerm_value hv]
  cases ht with
  | inl ht => exact observe_subst r (replace_realizes env _).1
  | inr ht => exact observe_subst r (replace_realizes env _).2

omit [MarkArity] in
private theorem withTerm_result {keepEffect : Bool} {env : Env} {a : Tm Instruction} {v : Val} {e : Bool}
    (h : term env a = some (v, e)) (body : Val → Exit → Prop) (out : Exit) :
    withTerm keepEffect env a body out ↔ ∃ x, body v x ∧ out = x.prepend (keepEffect && e) false := by
  cases e <;> simp [withTerm, h]

private theorem observe_acyclic_arm {n : Nat} {f : Fin n → Val → Exit → Prop}
    (env : Env) (r : Region Instruction) (i : Fin n) (v : Val) (e : Bool)
    (h : f i v = observe env (r.renameLabels (n + ·))) (out : Exit) :
    (∃ k, Follow f (Exit.branch i v e) k out) ↔
      ∃ x, observe env r x ∧ out = x.prepend e false := by
  constructor
  · rintro ⟨k, run⟩
    cases run with
    | exit ht => exact False.elim ((Nat.not_lt_of_ge ht) i.isLt)
    | @step _ next y count inside head tail =>
      change f i v next at head
      rw [h] at head
      obtain ⟨x, hx, rfl⟩ := (observe_renameLabels r (n + ·) env next).mp head
      obtain ⟨rfl, rfl⟩ := (follow_outward (by simp [Exit.relabel])).mp tail
      exact ⟨x, hx, by simp [Exit.branch, Exit.relabel, markAt]⟩
  · rintro ⟨x, hx, rfl⟩
    have head : f i v (x.relabel (n + ·)) := by
      rw [h]
      exact (observe_renameLabels r (n + ·) env _).mpr ⟨x, hx, rfl⟩
    have tail : Follow f (x.relabel (n + ·)) 0 x := by
      apply (follow_outward (by simp [Exit.relabel])).mpr
      simp [Exit.relabel]
    exact ⟨1, by simpa [Exit.branch, markAt] using Follow.step (first := Exit.branch i v e) i.isLt head tail⟩

private theorem observe_cfg_dispatch {n : Nat} {entry next : Region Instruction} {blocks : Fin n → Region Instruction}
    (env : Env) (i : Fin n) (v : Val) (e : Bool) (h : blocks i = next.renameLabels (n + ·))
    (he : observe env entry = (· = Exit.branch i v e)) (out : Exit) :
    observe env (.cfg entry n blocks) out ↔
      ∃ x, observe (extend env v) next x ∧ out = x.prepend e false := by
  change (∃ first k, observe env entry first ∧
    Follow (fun j w => observe (extend env w) (blocks j)) first k out) ↔ _
  rw [he]
  have hs : (∃ first k, first = Exit.branch i v e ∧
      Follow (fun j w => observe (extend env w) (blocks j)) first k out) ↔
      ∃ k, Follow (fun j w => observe (extend env w) (blocks j)) (Exit.branch i v e) k out :=
    ⟨fun ⟨_, k, rfl, ht⟩ => ⟨k, ht⟩, fun ⟨k, ht⟩ => ⟨_, k, rfl, ht⟩⟩
  rw [hs]
  exact observe_acyclic_arm (extend env v) next i v e (congrArg (observe (extend env v)) h) out

private theorem observe_case_entry (env : Env) (a : Tm Instruction) (v : Val) (e : Bool)
    (left : Bool) (h : term env a = some ((if left then Value.inl v else Value.inr v), e)) :
    observe env (.case a (.br 0 (.var 0)) (.br 1 (.var 0))) =
      (· = Exit.branch (if left then 0 else 1) v (MarkArity.keepUnaryEffect && e)) := by
  funext out
  change withTerm MarkArity.keepUnaryEffect env a _ out = _
  apply propext
  rw [withTerm_result h]
  cases left <;> simp [observe_br (env := extend env v) (a := .var 0) rfl, Exit.branch, Exit.prepend]

private theorem observe_caseCfg {Γ : VCtx (Ty Empty)} {A B : Ty Empty}
    {a : Tm Instruction} {l r : Region Instruction} (ha : Tm.HasType Γ a (.coprod A B)) :
    Preserves Γ (.case a l r) (Region.caseCfg a l r) := by
  intro env he
  obtain ⟨v, e, hv, ht⟩ := term_total ha he
  funext out
  apply propext
  change withTerm MarkArity.keepUnaryEffect env a _ out ↔ _
  rw [withTerm_result hv]
  unfold Region.caseCfg
  cases ht with
  | inl ht =>
    exact (observe_cfg_dispatch env (0 : Fin 2) _ (MarkArity.keepUnaryEffect && e) rfl (observe_case_entry env a _ e true hv) out).symm
  | inr ht =>
    exact (observe_cfg_dispatch env (1 : Fin 2) _ (MarkArity.keepUnaryEffect && e) rfl (observe_case_entry env a _ e false hv) out).symm

private theorem observe_caseInl {Γ : VCtx (Ty Empty)} {A : Ty Empty}
    {a : Tm Instruction} {l r : Region Instruction} (ha : Tm.HasType Γ a A) :
    Preserves Γ (.case (.inl a) l r) (.let₁ a l) := by
  intro env he
  obtain ⟨v, e, h, _⟩ := term_total ha he
  have hl : term env (.inl a) = some (.inl v, e) := by simp [term, h]
  funext out
  apply propext
  change withTerm MarkArity.keepUnaryEffect env (.inl a) _ out ↔
    withTerm MarkArity.keepUnaryEffect env a _ out
  rw [withTerm_result hl, withTerm_result h]

private theorem observe_caseInr {Γ : VCtx (Ty Empty)} {B : Ty Empty}
    {b : Tm Instruction} {l r : Region Instruction} (hb : Tm.HasType Γ b B) :
    Preserves Γ (.case (.inr b) l r) (.let₁ b r) := by
  intro env he
  obtain ⟨v, e, h, _⟩ := term_total hb he
  have hr : term env (.inr b) = some (.inr v, e) := by simp [term, h]
  funext out
  apply propext
  change withTerm MarkArity.keepUnaryEffect env (.inr b) _ out ↔
    withTerm MarkArity.keepUnaryEffect env b _ out
  rw [withTerm_result hr, withTerm_result h]

private theorem observe_cfgEquiv {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)}
    {r s : Region Instruction} (h : Region.CfgEquiv Γ r s L) : Preserves Γ r s := by
  induction h with
  | refl => intro _ _; rfl
  | symm _ ih => exact fun env he => (ih env he).symm
  | trans _ _ ih₁ ih₂ => exact fun env he => (ih₁ env he).trans (ih₂ env he)
  | let₁ ha _ ih => exact preserves_let₁ ha ih
  | let₂ ha _ ih => exact preserves_let₂ ha ih
  | case ha _ _ il ir => exact preserves_case ha il ir
  | cfg R hentry hblocks ie ib =>
    have he := (Region.RewriteEquiv.entry hentry).typed
    have hb i := (Region.RewriteEquiv.entry (hblocks i)).typed
    exact preserves_cfg R he.1 he.2 (fun i => (hb i).1) (fun i => (hb i).2) ie ib
  | cfgZero =>
    intro env _
    exact observe_cfg_zero _ _ env
  | @cfgBrExit n _ ℓ _ _ a blocks _ _ _ _ =>
    intro env _
    simpa only [Nat.add_sub_cancel_left] using
      observe_cfg_exit (n := n + 1) (i := n + 1 + ℓ) (Nat.le_add_right _ _) env a blocks
  | cfgBrLocal _ i ha _ =>
    intro env _
    obtain ⟨v, hv⟩ := value_term ha env
    exact observe_cfg_local hv i _

private theorem observe_rewriteEquiv {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)}
    {r s : Region Instruction} (h : Region.RewriteEquiv Γ r s L) : Preserves Γ r s := by
  induction h with
  | entry h => exact observe_cfgEquiv h
  | symm _ ih => exact fun env he => (ih env he).symm
  | trans _ _ ih₁ ih₂ => exact fun env he => (ih₁ env he).trans (ih₂ env he)
  | let₁ ha _ ih => exact preserves_let₁ ha ih
  | let₂ ha _ ih => exact preserves_let₂ ha ih
  | case ha _ _ il ir => exact preserves_case ha il ir
  | cfg R hentry hblocks ie ib =>
    exact preserves_cfg R hentry.typed.1 hentry.typed.2
      (fun i => (hblocks i).typed.1) (fun i => (hblocks i).typed.2) ie ib
  | letBr ha _ _ =>
    exact observe_letValue ha
  | caseInl ha _ _ => exact observe_caseInl ha
  | caseInr hb _ _ => exact observe_caseInr hb

theorem observe_substitutionEquiv {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)}
    {r s : Region Instruction} (h : Region.SubstitutionEquiv Γ r s L) : Preserves Γ r s := by
  induction h with
  | base h => exact observe_rewriteEquiv h
  | symm _ ih => exact fun env he => (ih env he).symm
  | trans _ _ ih₁ ih₂ => exact fun env he => (ih₁ env he).trans (ih₂ env he)
  | let₁ ha _ ih => exact preserves_let₁ ha ih
  | let₂ ha _ ih => exact preserves_let₂ ha ih
  | case ha _ _ il ir => exact preserves_case ha il ir
  | cfg R hentry hblocks ie ib =>
    exact preserves_cfg R hentry.typed.1 hentry.typed.2
      (fun i => (hblocks i).typed.1) (fun i => (hblocks i).typed.2) ie ib
  | letValue ha _ => exact observe_letValue ha
  | caseValue ha _ => exact observe_caseValue ha
  | caseCfg ha _ _ => exact observe_caseCfg ha
  | initial ha _ _ =>
    intro env he
    obtain ⟨_, _, _, hv⟩ := term_total ha.hasType he
    cases hv
  | cfgOutward =>
    intro env _
    exact observe_outward _ _ _ env

private theorem follow_unique {n : Nat} {blocks : Fin n → Val → Exit → Prop}
    (h : ∀ i v x y, blocks i v x → blocks i v y → x = y)
    {first x y : Exit} {k l : Nat} (hx : Follow blocks first k x) (hy : Follow blocks first l y) :
    k = l ∧ x = y := by
  induction hx generalizing l y with
  | exit outside =>
    cases hy with
    | exit => exact ⟨rfl, rfl⟩
    | step inside _ _ => exact False.elim ((Nat.not_lt_of_ge outside) inside)
  | step inside head tail ih =>
    cases hy with
    | exit outside => exact False.elim ((Nat.not_lt_of_ge outside) inside)
    | @step _ next' out' k' inside' head' tail' =>
      have eq := h _ _ _ _ head head'
      subst next'
      obtain ⟨rfl, rfl⟩ := ih tail'
      exact ⟨rfl, rfl⟩

omit [MarkArity] in
private theorem withTerm_unique {keepEffect : Bool} {env : Env} {a : Tm Instruction} {f : Val → Exit → Prop}
    (h : ∀ v x y, f v x → f v y → x = y)
    {x y : Exit} (hx : withTerm keepEffect env a f x) (hy : withTerm keepEffect env a f y) : x = y := by
  obtain ⟨v, e, hv, u, hu, rfl⟩ := hx
  obtain ⟨w, d, hw, z, hz, rfl⟩ := hy
  have eq := Option.some.inj (hv.symm.trans hw)
  cases eq
  rw [h v u z hu hz]

theorem observe_unique (r : Region Instruction) (env : Env) {x y : Exit}
    (hx : observe env r x) (hy : observe env r y) : x = y := by
  induction r generalizing env x y with
  | br i a =>
    obtain ⟨v, e, hv, rfl⟩ := hx
    obtain ⟨w, d, hw, rfl⟩ := hy
    cases Option.some.inj (hv.symm.trans hw)
    rfl
  | let₁ a r ih => exact withTerm_unique (fun v _ _ => ih (extend env v)) hx hy
  | let₂ a r ih =>
    refine withTerm_unique ?_ hx hy
    intro v x y hx hy
    cases v with
    | pair a b => exact ih _ hx hy
    | _ => cases hx
  | case a l r il ir =>
    refine withTerm_unique ?_ hx hy
    intro v x y hx hy
    cases v with
    | inl => exact il _ hx hy
    | inr => exact ir _ hx hy
    | _ => cases hx
  | cfg entry n blocks ie ib =>
    obtain ⟨f, _, hf, hfx⟩ := hx
    obtain ⟨g, _, hg, hgy⟩ := hy
    have eq := ie env hf hg
    subst g
    exact (follow_unique (fun i v _ _ => ib i (extend env v)) hfx hgy).2

@[expose] def followFuel {n : Nat} (blocks : Fin n → Val → Option Exit) :
    Nat → Exit → Option (Nat × Exit)
  | 0, _ => none
  | fuel + 1, first =>
    if h : first.label < n then
      (blocks ⟨first.label, h⟩ first.value).bind fun next =>
        (followFuel blocks fuel next).map fun (count, out) =>
          (count + 1, out.prepend first.effect (markAt n first count))
    else
      some (0, first.relabel (· - n))

private theorem followFuel_sound {n : Nat} {f : Fin n → Val → Option Exit}
    {g : Fin n → Val → Exit → Prop} (h : ∀ i v x, f i v = some x → g i v x)
    (fuel : Nat) (first : Exit) {count : Nat} {out : Exit}
    (run : followFuel f fuel first = some (count, out)) : Follow g first count out := by
  induction fuel generalizing first count out with
  | zero => simp [followFuel] at run
  | succ fuel ih =>
    by_cases inside : first.label < n
    · simp only [followFuel, dite_eq_left inside, Option.bind_eq_some_iff, Option.map_eq_some_iff] at run
      obtain ⟨next, hn, ⟨k, x⟩, hx, eq⟩ := run
      cases eq
      exact .step inside (h _ _ _ hn) (ih next hx)
    · simp [followFuel, inside] at run
      obtain ⟨rfl, rfl⟩ := run
      exact .exit (Nat.le_of_not_gt inside)

@[expose] def executeTerm (keepEffect : Bool) (env : Env) (a : Tm Instruction) (body : Val → Option Exit) : Option Exit :=
  (term env a).bind fun (v, e) => (body v).map (fun x => x.prepend (keepEffect && e) false)

@[expose] def execute (fuel : Nat) (env : Env) : Region Instruction → Option Exit
  | .br i a => (term env a).map (fun (v, e) => Exit.branch i v e)
  | .let₁ a r => executeTerm MarkArity.keepUnaryEffect env a (fun v => execute fuel (extend env v) r)
  | .let₂ a r => executeTerm true env a (fun
      | .pair v w => execute fuel (extend (extend env v) w) r
      | _ => none)
  | .case a l r => executeTerm MarkArity.keepUnaryEffect env a (fun
      | .inl v => execute fuel (extend env v) l
      | .inr w => execute fuel (extend env w) r
      | _ => none)
  | .cfg r _ blocks => (execute fuel env r).bind fun first =>
    (followFuel (fun i v => execute fuel (extend env v) (blocks i)) fuel first).map Prod.snd

omit [MarkArity] in
private theorem executeTerm_sound {keepEffect : Bool} {env : Env} {a : Tm Instruction} {f : Val → Option Exit}
    {g : Val → Exit → Prop} (h : ∀ v x, f v = some x → g v x)
    {out : Exit} (he : executeTerm keepEffect env a f = some out) :
    withTerm keepEffect env a g out := by
  simp only [executeTerm, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
  obtain ⟨⟨v, e⟩, ht, x, hx, rfl⟩ := he
  exact ⟨v, e, ht, x, h v x hx, rfl⟩

theorem execute_sound (fuel : Nat) (r : Region Instruction) (env : Env) {out : Exit}
    (he : execute fuel env r = some out) : observe env r out := by
  induction r generalizing env out with
  | br i a =>
    simp only [execute, Option.map_eq_some_iff] at he
    obtain ⟨⟨v, e⟩, ht, rfl⟩ := he
    exact ⟨v, e, ht, rfl⟩
  | let₁ a r ih => exact executeTerm_sound (fun v _ => ih (extend env v)) he
  | let₂ a r ih =>
    refine executeTerm_sound ?_ he
    intro v x hx
    cases v with
    | pair v w => exact ih _ hx
    | _ => cases hx
  | case a l r il ir =>
    refine executeTerm_sound ?_ he
    intro v x hx
    cases v with
    | inl => exact il _ hx
    | inr => exact ir _ hx
    | _ => cases hx
  | cfg entry n blocks ie ib =>
    simp only [execute, Option.bind_eq_some_iff, Option.map_eq_some_iff] at he
    obtain ⟨first, hf, ⟨k, x⟩, hx, rfl⟩ := he
    exact ⟨first, k, ie env hf, followFuel_sound (fun i v _ => ib i (extend env v)) fuel first hx⟩

end

private local instance : MarkArity where
  enabled _ := true

theorem producer_valueBranches :
    Region.ValueBranches [stateType] producer [.coprod .unit stateType] :=
  .let₁ (.op .unit)
    (.case (A := .unit) (B := .coprod .unit .unit) (.var (i := 1) rfl)
      (.br (ℓ := 0) rfl (.inr (.inr (.inl .unit))))
      (.case (A := .unit) (B := .unit) (.var (i := 0) rfl)
        (.br (ℓ := 0) rfl (.inr (.inr (.inr .unit))))
        (.br (ℓ := 0) rfl (.inl .unit))))

private def initialEnv : Env :=
  extend (fun _ => .unit) (.inl .unit)

private theorem initialEnv_typed : EnvTyped [stateType] initialEnv :=
  Resumption.Typing.EnvTyped.extend (fun _ _ h => by simp [At] at h) (.inl .unit)

private def markedExit : Exit := ⟨0, .unit, true, true⟩
private def unmarkedExit : Exit := ⟨0, .unit, true, false⟩

private theorem unfolded_marked : observe initialEnv unfolded markedExit :=
  execute_sound 4 unfolded initialEnv rfl

private theorem sequenced_unmarked : observe initialEnv sequenced unmarkedExit :=
  execute_sound 4 sequenced initialEnv rfl

private theorem fixpoint_marked :
    observe initialEnv (Region.SyntacticCategory.iterateRegion stateType producer) markedExit :=
  execute_sound 4 _ initialEnv rfl

private theorem fixpoint_rhs_unmarked :
    observe initialEnv (producer.lsubst (fun _ => returnOrRepeat)) unmarkedExit :=
  execute_sound 4 _ initialEnv rfl

theorem sequencing_obstruction : ¬ Region.SubstitutionEquiv [stateType] unfolded sequenced [.unit] := by
  intro equiv
  have h := observe_substitutionEquiv equiv initialEnv initialEnv_typed
  have same := observe_unique sequenced initialEnv (h ▸ unfolded_marked) sequenced_unmarked
  exact Bool.noConfusion (congrArg Exit.marked same)

theorem fixpoint_obstruction :
    ¬ Region.SubstitutionEquiv [stateType] (Region.SyntacticCategory.iterateRegion stateType producer)
      (producer.lsubst (fun _ => returnOrRepeat)) [.unit] := by
  intro equiv
  have h := observe_substitutionEquiv equiv initialEnv initialEnv_typed
  have same := observe_unique _ initialEnv (h ▸ fixpoint_marked) fixpoint_rhs_unmarked
  exact Bool.noConfusion (congrArg Exit.marked same)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing
