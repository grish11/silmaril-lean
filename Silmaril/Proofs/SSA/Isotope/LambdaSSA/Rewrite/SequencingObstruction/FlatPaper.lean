module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.SequencingObstruction
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.EntryLet.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.CfgEta.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Family.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.SingletonReification.SingleCfg.Endpoint.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.EntryLet.Obstruction.Destructure.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Defs

/-! # Paper soundness for the flat CFG diagnostic -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Region.SequencingObstruction
open Silmaril.Isotope.LambdaSSA.Semantics (extend)

section
set_option linter.concreteInstances false
variable [MarkArity]

/-! ## Outgoing substitution preserves the local transfer path -/

omit [MarkArity] in
@[simp] private theorem prepend_prepend (x : Exit) (a b c d : Bool) :
    (x.prepend c d).prepend a b = x.prepend (a || c) (b || d) := by
  simp [Exit.prepend, Bool.or_assoc]

private def Post (k : Nat → Val → Exit → Prop) (x y : Exit) : Prop :=
  ∃ z, k x.label x.value z ∧ y = z.prepend x.effect x.marked

private def Under (n : Nat) (k : Nat → Val → Exit → Prop) (x y : Exit) : Prop :=
  if x.label < n then y = x
  else ∃ z, k (x.label - n) x.value z ∧ y = (z.prepend x.effect x.marked).relabel (n + ·)

omit [MarkArity] in
private theorem under_local {n : Nat} {k : Nat → Val → Exit → Prop} {x y : Exit}
    (h : Under n k x y) (hi : y.label < n) : y = x := by
  unfold Under at h
  split at h
  · exact h
  · obtain ⟨z, _, rfl⟩ := h
    simp only [Exit.relabel, Exit.prepend] at hi
    omega

omit [MarkArity] in
private theorem under_exit {n : Nat} {k : Nat → Val → Exit → Prop} {x y : Exit}
    (h : Under n k x y) (ho : n ≤ y.label) :
    n ≤ x.label ∧ Post k (x.relabel (· - n)) (y.relabel (· - n)) := by
  unfold Under at h
  split at h
  · rename_i hi
    subst y
    omega
  · rename_i hi
    obtain ⟨z, hz, rfl⟩ := h
    exact ⟨by omega, z, hz, by simp [Exit.relabel]⟩

private theorem follow_post_forward {n : Nat} {f g : Fin n → Val → Exit → Prop}
    {k : Nat → Val → Exit → Prop}
    (hfg : ∀ i v y, g i v y → ∃ x, f i v x ∧ Under n k x y)
    {x y out : Exit} {count : Nat} (run : Follow g y count out) (hxy : Under n k x y) :
    ∃ result, Follow f x count result ∧ Post k result out := by
  induction run generalizing x with
  | exit hy =>
      obtain ⟨hx, post⟩ := under_exit hxy hy
      exact ⟨_, .exit hx, post⟩
  | @step y next out count hi head _ ih =>
      obtain rfl := under_local hxy hi
      obtain ⟨x', hx', hside⟩ := hfg _ _ _ head
      obtain ⟨result, rest, z, hz, rfl⟩ := ih hside
      refine ⟨_, .step hi hx' rest, z, hz, ?_⟩
      rw [prepend_prepend]
      rfl

private theorem follow_post_backward {n : Nat} {f g : Fin n → Val → Exit → Prop}
    {k : Nat → Val → Exit → Prop}
    (hfg : ∀ i v x y, f i v x → Under n k x y → g i v y)
    {x result out : Exit} {count : Nat} (run : Follow f x count result) (post : Post k result out) :
    ∃ y, Under n k x y ∧ Follow g y count out := by
  induction run generalizing out with
  | @exit x hx =>
      obtain ⟨z, hz, rfl⟩ := post
      let y := (z.prepend x.effect x.marked).relabel (n + ·)
      refine ⟨y, ?_, ?_⟩
      · rw [Under, ite_eq_right (Nat.not_lt_of_ge hx)]
        exact ⟨z, hz, rfl⟩
      · have hy : n ≤ y.label := by simp [y, Exit.relabel]
        simpa [y, Exit.relabel] using (Follow.exit (block := g) hy)
  | @step x next result count hi head _ ih =>
      obtain ⟨z, hz, rfl⟩ := post
      obtain ⟨y, hy, rest⟩ := ih (out := z.prepend result.effect result.marked) ⟨z, hz, rfl⟩
      refine ⟨x, by simp [Under, hi], ?_⟩
      have step := Follow.step (first := x) hi (hfg _ _ _ _ head hy) rest
      rw [prepend_prepend] at step
      exact step

omit [MarkArity] in
private theorem liftLSubstN_here (n : Nat) (σ : Nat → Region Instruction) {i : Nat} (hi : i < n) :
    liftLSubstN n σ i = labelId i := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change (liftLSubstN n σ i).renameLabels Nat.succ = _
      rw [ih (Nat.lt_of_succ_lt_succ hi)]
      rfl

omit [MarkArity] in
private theorem liftLSubstN_there (n : Nat) (σ : Nat → Region Instruction) (i : Nat) :
    liftLSubstN n σ (n + i) = (σ i).renameLabels (n + ·) := by
  induction n with
  | zero =>
    simp only [liftLSubstN, Nat.zero_add, show (fun j : Nat => j) = id from rfl, renameLabels_id]
  | succ n ih =>
    rw [Nat.succ_add]
    change (liftLSubstN n σ (n + i)).renameLabels Nat.succ = _
    rw [ih, renameLabels_comp]
    congr 1
    funext j
    change Nat.succ (n + j) = n + 1 + j
    omega

private theorem observe_liftVars (σ : Nat → Region Instruction) (i : Nat)
    (env : Env) (v w : Val) :
    observe (extend (extend env v) w) (liftLSubstVars σ i) = observe (extend env w) (σ i) := by
  rw [liftLSubstVars, renameVars_eq_substVars]
  apply observe_subst
  intro j
  cases j <;> rfl

private theorem under_liftLabels (n : Nat) (σ : Nat → Region Instruction)
    (env : Env) (x y : Exit) :
    Post (fun i v => observe (extend env v) (liftLSubstN n σ i)) x y ↔
      Under n (fun i v => observe (extend env v) (σ i)) x y := by
  unfold Under Post
  by_cases hx : x.label < n
  · simp only [hx, ite_true, liftLSubstN_here _ _ hx]
    rw [show labelId (Φ := Instruction) x.label = .br x.label (.var 0) from rfl, observe_br rfl]
    simp [Exit.branch, Exit.prepend]
  · simp only [hx, ite_false]
    have hshift : liftLSubstN n σ x.label = (σ (x.label - n)).renameLabels (n + ·) := by
      rw [← liftLSubstN_there n σ, Nat.add_sub_of_le (Nat.le_of_not_gt hx)]
    simp only [hshift, observe_renameLabels]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, rfl⟩

omit [MarkArity] in
private theorem observe_withTerm_post {keepEffect : Bool} {env : Env} {a : Tm Instruction}
    {f g : Val → Exit → Prop} {k : Nat → Val → Exit → Prop}
    (hg : ∀ v y, g v y ↔ ∃ x, f v x ∧ Post k x y) (out : Exit) :
    withTerm keepEffect env a g out ↔ ∃ x, withTerm keepEffect env a f x ∧ Post k x out := by
  constructor
  · rintro ⟨v, e, hv, y, hy, rfl⟩
    obtain ⟨x, hx, z, hz, rfl⟩ := (hg v y).mp hy
    exact ⟨_, ⟨v, e, hv, x, hx, rfl⟩, z, hz, by simp [Exit.prepend, Bool.or_assoc]⟩
  · rintro ⟨_, ⟨v, e, hv, x, hx, rfl⟩, z, hz, rfl⟩
    exact ⟨v, e, hv, _, (hg v _).mpr ⟨x, hx, z, hz, rfl⟩,
      by simp [Exit.prepend, Bool.or_assoc]⟩

private theorem observe_lsubst {Γ L : List (Ty Empty)} {r : Region Instruction}
    (hr : ValueBranches Γ r L) (σ : Nat → Region Instruction) (env : Env) (out : Exit) :
    observe env (r.lsubst σ) out ↔
      ∃ x, observe env r x ∧ Post (fun i v => observe (extend env v) (σ i)) x out := by
  induction hr generalizing σ env out with
  | br hi ha =>
      obtain ⟨v, hv⟩ := value_term ha env
      simp only [lsubst, observe_subst (σ _) (single_realizes hv), observe_br hv]
      simp [Post, Exit.branch]
  | let₁ _ _ ih =>
      exact observe_withTerm_post
        (fun v y => by simpa only [observe_liftVars] using ih (liftLSubstVars σ) (extend env v) y) out
  | let₂ _ _ ih =>
      apply observe_withTerm_post _ out
      intro v y
      cases v <;> simp
      case pair v w =>
        simpa only [observe_liftVars] using ih (liftLSubstVars (liftLSubstVars σ)) (extend (extend env v) w) y
  | case _ _ _ il ir =>
      apply observe_withTerm_post _ out
      intro v y
      cases v <;> simp
      · rename_i v
        simpa only [observe_liftVars] using il (liftLSubstVars σ) (extend env v) y
      · rename_i v
        simpa only [observe_liftVars] using ir (liftLSubstVars σ) (extend env v) y
  | @cfg n _ entry _ blocks _ _ _ ie ib =>
      let f := fun i v => observe (extend env v) (blocks i)
      let g := fun i v => observe (extend env v) ((blocks i).lsubst (liftLSubstVars (liftLSubstN n σ)))
      let k := fun i v => observe (extend env v) (σ i)
      have hs (y : Exit) : observe env (entry.lsubst (liftLSubstN n σ)) y ↔
          ∃ x, observe env entry x ∧ Under n k x y := by
        simp only [ie, under_liftLabels, k]
      have hb (i : Fin n) (v : Val) (y : Exit) :
          g i v y ↔ ∃ x, f i v x ∧ Under n k x y := by
        simpa only [f, g, k, observe_liftVars, under_liftLabels] using
          ib i (liftLSubstVars (liftLSubstN n σ)) (extend env v) y
      change (∃ y count, _ ∧ Follow g y count out) ↔
        ∃ result, (∃ x count, _ ∧ Follow f x count result) ∧ Post k result out
      constructor
      · rintro ⟨y, count, hy, run⟩
        obtain ⟨x, hx, hxy⟩ := (hs y).mp hy
        obtain ⟨result, rest, post⟩ := follow_post_forward (fun i v y h => (hb i v y).mp h) run hxy
        exact ⟨result, ⟨x, count, hx, rest⟩, post⟩
      · rintro ⟨result, ⟨x, count, hx, run⟩, post⟩
        obtain ⟨y, hxy, rest⟩ := follow_post_backward (fun i v x y h hxy => (hb i v y).mpr ⟨x, h, hxy⟩) run post
        exact ⟨y, count, (hs y).mpr ⟨x, hx, hxy⟩, rest⟩

end

/-! ## Unary CFG laws with mark propagation -/

section Flat

set_option linter.concreteInstances false
variable [profile : MarkArity] [Fact (profile.enabled 1 = false)]

private abbrev One (f : Val → Exit → Prop) (start out : Exit) : Prop :=
  ∃ count, Follow (fun (_ : Fin 1) => f) start count out

private theorem no_one_mark (x : Exit) (count : Nat) : markAt 1 x count = x.marked := by
  simp [markAt, Fact.out (p := profile.enabled 1 = false)]

omit [Fact (profile.enabled 1 = false)] in
private theorem one_exit {f : Val → Exit → Prop} {x y : Exit} (h : 1 ≤ x.label) :
    One f x y ↔ y = x.relabel (· - 1) := by
  simp [One, follow_outward h]

private theorem one_step {f : Val → Exit → Prop} {x out : Exit} (hi : x.label < 1) :
    One f x out ↔ ∃ next y, f x.value next ∧ One f next y ∧ out = y.prepend x.effect x.marked := by
  constructor
  · rintro ⟨k, h⟩
    cases h with
    | exit h => omega
    | @step _ next y c hj head tail =>
        exact ⟨next, y, head, ⟨c, tail⟩, by rw [no_one_mark]⟩
  · rintro ⟨next, y, head, ⟨c, tail⟩, rfl⟩
    exact ⟨c + 1, by rw [← no_one_mark x c]; exact .step hi head tail⟩

private abbrev Unary (f : Val → Exit → Prop) :=
  Follow (fun (_ : Fin 1) => f)

private theorem unary_prefix {f : Val → Exit → Prop} (x out : Exit) (e m : Bool) (j : Nat) :
    Unary f (x.prepend e m) j out ↔ ∃ y, Unary f x j y ∧ out = y.prepend e m := by
  constructor
  · intro h
    generalize eq : x.prepend e m = z at h
    cases h with
    | exit h =>
        subst z
        exact ⟨_, .exit h, rfl⟩
    | @step z next y k h head tail =>
        subst z
        refine ⟨_, .step h head tail, ?_⟩
        simp only [no_one_mark, prepend_prepend]
        rfl
  · rintro ⟨y, h, rfl⟩
    cases h with
    | exit h => exact .exit h
    | @step x next y k h head tail =>
        have step := Follow.step (first := x.prepend e m) h head tail
        simp only [no_one_mark, prepend_prepend] at step ⊢
        exact step

private theorem one_prefix {f : Val → Exit → Prop} (x out : Exit) (e m : Bool) :
    One f (x.prepend e m) out ↔ ∃ y, One f x y ∧ out = y.prepend e m := by
  constructor
  · rintro ⟨j, run⟩
    obtain ⟨y, hy, eq⟩ := (unary_prefix x out e m j).1 run
    exact ⟨y, ⟨j, hy⟩, eq⟩
  · rintro ⟨y, ⟨j, hy⟩, eq⟩
    exact ⟨j, (unary_prefix x out e m j).2 ⟨y, hy, eq⟩⟩

omit [Fact (profile.enabled 1 = false)] in
private theorem reentry_observe (env : Env) (b : Region Instruction) (i : Nat) (v : Val) (y : Exit) :
    observe (extend env v) (CfgEta.reentry b i) y ↔
      One (fun w => observe (extend env w) b) (Exit.branch i v false) y := by
  change (∃ first count, observe (extend env v) (.br i (.var 0)) first ∧
    Follow (fun (_ : Fin 1) w => observe (extend (extend env v) w) (liftLSubstVars (fun _ => b) 0))
      first count y) ↔ _
  simp [observe_br (env := extend env v) (a := .var 0) rfl, observe_liftVars, One]

private theorem one_eta {Γ L : List (Ty Empty)} {e b : Region Instruction}
    {A : Ty Empty} (he : ValueBranches Γ e (A :: L)) :
    Preserves Γ (CfgEta.singleCfg e b) (e.lsubst (CfgEta.reentry b)) := by
  intro env _
  funext out
  apply propext
  rw [observe_lsubst he]
  let f := fun v => observe (extend env v) b
  have bind (x : Exit) :
      Post (fun i v => observe (extend env v) (CfgEta.reentry b i)) x out ↔ One f x out := by
    have hx : (Exit.branch x.label x.value false).prepend x.effect x.marked = x := by
      cases x
      simp [Exit.branch, Exit.prepend]
    rw [← hx]
    rw [one_prefix]
    simp only [Post, Exit.prepend, Exit.branch, Bool.or_false, reentry_observe, f]
  change (∃ x count, observe env e x ∧ Follow (fun (_ : Fin 1) => f) x count out) ↔ _
  simp only [bind]
  exact ⟨fun ⟨x, count, hx, run⟩ => ⟨x, hx, count, run⟩,
    fun ⟨x, hx, count, run⟩ => ⟨x, count, hx, run⟩⟩

private def Through (f : Val → Exit → Prop) (v : Val) (out : Exit) : Prop :=
  One f (Exit.branch 0 v false) out

private def Merge (f : Val → Exit → Prop) (v : Val) (out : Exit) : Prop :=
  ∃ first, f v first ∧ out = first.relabel Nat.pred

private theorem flat_to_nested (f : Val → Exit → Prop) {x out : Exit} {j : Nat}
    (run : Unary (Merge f) (x.relabel Nat.pred) j out) :
    ∃ middle, One f x middle ∧ One (Through f) middle out := by
  generalize eq : x.relabel Nat.pred = start at run
  induction run generalizing x with
  | @exit start ho =>
      subst start
      have hx : 2 ≤ x.label := by
        change 1 ≤ x.label - 1 at ho
        omega
      refine ⟨_, (one_exit (f := f) (by omega : 1 ≤ x.label)).2 rfl, (one_exit ?_).2 ?_⟩
      · change 1 ≤ x.label - 1
        omega
      · simp [Exit.relabel, Nat.pred_eq_sub_one]
  | @step start next out count hi head _ ih =>
      subst start
      obtain ⟨next, hn, rfl⟩ := head
      obtain ⟨middle, inner, outer⟩ := ih (x := next) rfl
      simp only [no_one_mark]
      by_cases hx : x.label < 1
      · refine ⟨middle.prepend x.effect x.marked,
          (one_step hx).2 ⟨next, middle, hn, inner, rfl⟩, ?_⟩
        exact (one_prefix middle _ x.effect x.marked).2 ⟨out, outer, rfl⟩
      · have hh : (x.relabel (· - 1)).label < 1 := by
          simpa [Exit.relabel, Nat.pred_eq_sub_one] using hi
        refine ⟨_, (one_exit (by omega : 1 ≤ x.label)).2 rfl, (one_step hh).2 ?_⟩
        refine ⟨middle, out, ?_, outer, rfl⟩
        exact (one_step (x := Exit.branch 0 x.value false) (by simp [Exit.branch])).2
          ⟨next, middle, hn, inner, (prepend_false middle).symm⟩

private theorem nested_to_flat (f : Val → Exit → Prop) {x middle out : Exit} {j k : Nat}
    (inner : Unary f x j middle) (outer : Unary (Through f) middle k out) :
    One (Merge f) (x.relabel Nat.pred) out := by
  cases inner with
  | @exit x hx =>
      cases outer with
      | exit ho =>
          apply (one_exit (x := x.relabel Nat.pred) (by exact ho)).2
          simp [Exit.relabel, Nat.pred_eq_sub_one]
      | @step _ mid out count hi head tail =>
          obtain ⟨next, y, hnext, ⟨c, inside⟩, hy⟩ := (one_step (x := Exit.branch 0 x.value false)
            (by simp [Exit.branch])).1 head
          simp only [Exit.branch, prepend_false] at hy
          cases hy
          have hflat := nested_to_flat f inside tail
          rw [no_one_mark]
          refine (one_step (x := x.relabel Nat.pred) ?_).2
            ⟨next.relabel Nat.pred, out, ⟨next, hnext, rfl⟩, hflat, rfl⟩
          simpa [Exit.relabel, Nat.pred_eq_sub_one] using hi
  | @step x next mid count hi head tail =>
      rw [no_one_mark] at outer
      obtain ⟨result, rest, rfl⟩ := (unary_prefix mid _ x.effect x.marked k).1 outer
      refine (one_step (x := x.relabel Nat.pred) ?_).2
        ⟨next.relabel Nat.pred, result, ⟨next, head, rfl⟩, nested_to_flat f tail rest, rfl⟩
      change x.label < 1 at hi
      change x.label.pred < 1
      rw [show x.label = 0 by omega]
      decide
termination_by (k, j)
decreasing_by all_goals omega

private theorem one_codiagonal (f : Val → Exit → Prop) (x out : Exit) :
    One (Through f) x out ↔ One (Merge f) x out := by
  by_cases hx : x.label < 1
  · rw [one_step hx, one_step hx]
    constructor
    · rintro ⟨middle, out, head, ⟨k, outer⟩, rfl⟩
      obtain ⟨next, y, hn, ⟨j, inner⟩, eq⟩ := (one_step (x := Exit.branch 0 x.value false)
        (by simp [Exit.branch])).1 head
      simp only [Exit.branch, prepend_false] at eq
      cases eq
      exact ⟨_, _, ⟨next, hn, rfl⟩, nested_to_flat f inner outer, rfl⟩
    · rintro ⟨_, out, ⟨next, hn, rfl⟩, ⟨j, tail⟩, rfl⟩
      obtain ⟨middle, inner, outer⟩ := flat_to_nested f tail
      exact ⟨middle, out, (one_step (x := Exit.branch 0 x.value false) (by simp [Exit.branch])).2
        ⟨next, middle, hn, inner, (prepend_false middle).symm⟩, outer, rfl⟩
  · rw [one_exit (by omega : 1 ≤ x.label), one_exit (by omega : 1 ≤ x.label)]

private theorem codiagonal_observe {e p : Region Instruction} (env : Env) :
    observe env (CfgEta.Codiagonal.nested e p) = observe env (CfgEta.Codiagonal.flattened e p) := by
  funext out
  apply propext
  let f := fun v => observe (extend env v) p
  have inner (v : Val) : observe (extend env v) (CfgEta.reentry p 0) = Through f v :=
    funext fun y => propext (reentry_observe env p 0 v y)
  have merge (v : Val) : observe (extend env v) (p.renameLabels Nat.pred) = Merge f v :=
    funext fun y => propext (observe_renameLabels p Nat.pred (extend env v) y)
  change (∃ x count, observe env e x ∧
      Follow (fun (_ : Fin 1) v => observe (extend env v) (CfgEta.reentry p 0)) x count out) ↔
    (∃ x count, observe env e x ∧
      Follow (fun (_ : Fin 1) v => observe (extend env v) (p.renameLabels Nat.pred)) x count out)
  simp only [inner, merge, exists_and_left]
  exact exists_congr (fun x => and_congr_right (fun _ => one_codiagonal f x out))

private def MapLocal (m : Val → Val) (x : Exit) : Exit :=
  if x.label = 0 then { x with value := m x.value } else x

omit profile in
@[simp] private theorem mapLocal_label (m : Val → Val) (x : Exit) :
    (MapLocal m x).label = x.label := by simp [MapLocal, apply_ite]

omit profile in
@[simp] private theorem mapLocal_effect (m : Val → Val) (x : Exit) :
    (MapLocal m x).effect = x.effect := by simp [MapLocal, apply_ite]

omit profile in
@[simp] private theorem mapLocal_marked (m : Val → Val) (x : Exit) :
    (MapLocal m x).marked = x.marked := by simp [MapLocal, apply_ite]

private theorem unary_map_forward {f g : Val → Exit → Prop} {good : Val → Prop} {m : Val → Val}
    (stable : ∀ v x, good v → f v x → x.label = 0 → good x.value)
    (comm : ∀ v z, good v → (g (m v) z ↔ ∃ x, f v x ∧ z = MapLocal m x))
    {x out : Exit} {j : Nat} (start : x.label = 0 → good x.value)
    (run : Unary g (MapLocal m x) j out) : Unary f x j out := by
  generalize eq : MapLocal m x = y at run
  induction run generalizing x with
  | @exit y h =>
      subst y
      have hx : 1 ≤ x.label := by simpa only [mapLocal_label] using h
      simpa [MapLocal, show x.label ≠ 0 by omega] using (Follow.exit (block := fun (_ : Fin 1) => f) hx)
  | @step y next out count hi head tail ih =>
      subst y
      have hx : x.label < 1 := by simpa only [mapLocal_label] using hi
      have hzero : x.label = 0 := by omega
      have mapped : g (m x.value) next := by simpa [MapLocal, hzero] using head
      obtain ⟨z, hz, rfl⟩ := (comm x.value next (start hzero)).1 mapped
      have rest := ih (x := z) (stable x.value z (start hzero) hz) rfl
      simpa only [no_one_mark, mapLocal_marked, mapLocal_effect] using (Follow.step (first := x) hx hz rest)

private theorem unary_map_backward {f g : Val → Exit → Prop} {good : Val → Prop} {m : Val → Val}
    (stable : ∀ v x, good v → f v x → x.label = 0 → good x.value)
    (comm : ∀ v z, good v → (g (m v) z ↔ ∃ x, f v x ∧ z = MapLocal m x))
    {x out : Exit} {j : Nat} (start : x.label = 0 → good x.value)
    (run : Unary f x j out) : Unary g (MapLocal m x) j out := by
  induction run with
  | @exit x h =>
      simpa [MapLocal, show x.label ≠ 0 by omega] using (Follow.exit (block := fun (_ : Fin 1) => g) h)
  | @step x next out count hi head tail ih =>
      have hzero : x.label = 0 := by omega
      have mapped : g (m x.value) (MapLocal m next) :=
        (comm x.value _ (start hzero)).2 ⟨next, head, rfl⟩
      have part : g (MapLocal m x).value (MapLocal m next) := by
        simpa [MapLocal, hzero] using mapped
      have hi' : (MapLocal m x).label < 1 := by simpa only [mapLocal_label] using hi
      simpa only [no_one_mark, mapLocal_marked, mapLocal_effect] using
        (Follow.step (first := MapLocal m x) hi' part (ih (stable x.value next (start hzero) head)))

private def localValue (a : Tm Instruction) (env : Env) (v : Val) : Val :=
  ((term (extend env v) a).map Prod.fst).getD .unit

omit profile in
private theorem local_value_spec {Γ : VCtx (Ty Empty)} {A D : Ty Empty} {a : Tm Instruction}
    (ha : Tm.BranchValue (A :: Γ) a D) (env : Env) (v : Val) :
    term (extend env v) a = some (localValue a env v, false) := by
  obtain ⟨w, hw⟩ := value_term ha (extend env v)
  simp [localValue, hw]

omit [Fact (profile.enabled 1 = false)] in
private theorem post_localMap {Γ : VCtx (Ty Empty)} {A D : Ty Empty} {a : Tm Instruction}
    (ha : Tm.BranchValue (A :: Γ) a D) (env : Env) (x z : Exit) :
    Post (fun i v => observe (extend env v) (CfgEta.Uniformity.localMap a i)) x z ↔
      z = MapLocal (localValue a env) x := by
  cases x with
  | mk i v e m =>
    cases i with
    | zero =>
      have ht := local_value_spec ha env v
      simp [Post, MapLocal, CfgEta.Uniformity.localMap, observe_br ht, Exit.branch, Exit.prepend]
    | succ i =>
      simp [Post, MapLocal, CfgEta.Uniformity.localMap,
        observe_br (env := extend env v) (a := .var 0) rfl, Exit.branch, Exit.prepend]

omit profile in
private theorem local_good {A : Ty Empty} {L : LCtx (Ty Empty)} {x : Exit}
    (h : x.WellTyped (A :: L)) (hz : x.label = 0) : Typed x.value A := by
  obtain ⟨T, ht, hv⟩ := h
  rw [hz] at ht
  cases Option.some.inj ht
  exact hv

private theorem uniform_observe {Γ L : List (Ty Empty)} {A D : Ty Empty}
    {e p q : Region Instruction} {a : Tm Instruction}
    (he : ValueBranches Γ e (A :: L)) (hp : ValueBranches (A :: Γ) p (A :: L))
    (ha : Tm.BranchValue (A :: Γ) a D)
    (square : Preserves (A :: Γ)
      (p.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a)))
      ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => q)))) :
    Preserves Γ (CfgEta.singleCfg e p) (CfgEta.singleCfg (e.lsubst (CfgEta.Uniformity.localMap a)) q) := by
  intro env henv
  let f := fun v => observe (extend env v) p
  let g := fun v => observe (extend env v) q
  let m := localValue a env
  have stable (v : Val) (x : Exit) (hv : Typed v A) (hx : f v x) (hz : x.label = 0) :
      Typed x.value A :=
    local_good (observe_typed hp.hasType (henv.extend hv) hx) hz
  have comm (v : Val) (z : Exit) (hv : Typed v A) :
      g (m v) z ↔ ∃ x, f v x ∧ z = MapLocal m x := by
    have eq := congrFun (square (extend env v) (henv.extend hv)) z
    have left : observe (extend env v) (p.lsubst (liftLSubstVars (CfgEta.Uniformity.localMap a))) z ↔
        ∃ x, f v x ∧ z = MapLocal m x := by
      simpa only [observe_liftVars, post_localMap ha, f, m] using
        observe_lsubst hp (liftLSubstVars (CfgEta.Uniformity.localMap a)) (extend env v) z
    have right : observe (extend env v) ((Region.br 0 a).lsubst (liftLSubstVars (fun _ => q))) z ↔
        g (m v) z := by
      have branch : ValueBranches (A :: Γ) (.br 0 a) (D :: L) := .br (ℓ := 0) rfl ha
      rw [observe_lsubst branch, observe_br (local_value_spec ha env v)]
      simp [Post, observe_liftVars, Exit.branch, m, g]
    exact right.symm.trans ((iff_of_eq eq.symm).trans left)
  funext out
  apply propext
  change (∃ x count, observe env e x ∧ Unary f x count out) ↔
    ∃ y count, observe env (e.lsubst (CfgEta.Uniformity.localMap a)) y ∧ Unary g y count out
  simp only [observe_lsubst he, post_localMap ha]
  constructor
  · rintro ⟨x, count, hx, run⟩
    have ready : x.label = 0 → Typed x.value A := local_good (observe_typed he.hasType henv hx)
    exact ⟨_, count, ⟨x, hx, rfl⟩, unary_map_backward stable comm ready run⟩
  · rintro ⟨_, count, ⟨x, hx, rfl⟩, run⟩
    have ready : x.label = 0 → Typed x.value A := local_good (observe_typed he.hasType henv hx)
    exact ⟨x, count, hx, unary_map_forward stable comm ready run⟩

omit [Fact (profile.enabled 1 = false)] in
private theorem preserves_post {Γ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)}
    {r s : Region Instruction} {σ : Nat → Region Instruction}
    (hr : ValueBranches Γ r L) (hs : ValueBranches Γ s L) (h : Preserves Γ r s) :
    Preserves Γ (r.lsubst σ) (s.lsubst σ) := by
  intro env he
  funext out
  apply propext
  rw [observe_lsubst hr, observe_lsubst hs, h env he]

private theorem cfgEta_observe {Γ L : List (Ty Empty)} {r s : Region Instruction}
    (h : CfgEta.Eqv Γ r s L) : Preserves Γ r s := by
  induction h with
  | native h => exact observe_substitutionEquiv h
  | symm _ ih => exact fun env he => (ih env he).symm
  | trans _ _ il ir => exact fun env he => (il env he).trans (ir env he)
  | let₁ ha _ ih => exact preserves_let₁ ha ih
  | let₂ ha _ ih => exact preserves_let₂ ha ih
  | case ha _ _ il ir => exact preserves_case ha il ir
  | cfg R he hb ie ib =>
    exact preserves_cfg R he.typed.1 he.typed.2
      (fun i => (hb i).typed.1) (fun i => (hb i).typed.2) ie ib
  | @etaPost Γ e A L block K σ he hb hσ =>
    have hl : ValueBranches Γ (CfgEta.singleCfg e block) L :=
      .cfg (fun _ : Fin 1 => A) he (fun _ => hb)
    have hr : ValueBranches Γ (e.lsubst (CfgEta.reentry block)) L :=
      he.lsubst (fun _ T hi => .cfg (fun _ : Fin 1 => A) (.br hi (.var rfl))
        (fun _ => hb.renameVars ((Ren.wk Γ T).lift A)))
    exact preserves_post hl hr (one_eta he)

omit [Fact (profile.enabled 1 = false)] in
private theorem preserves_value_subst {Γ Δ : VCtx (Ty Empty)} {L : LCtx (Ty Empty)}
    {r s : Region Instruction} {θ : Nat → Tm Instruction}
    (hr : HasType Γ r L) (hs : HasType Γ s L)
    (hθ : ∀ ⦃i A⦄, At Γ i A → Tm.BranchValue Δ (θ i) A) (h : Preserves Γ r s) :
    Preserves Δ (r.substVars θ) (s.substVars θ) := by
  intro env he
  let fill (i : Nat) : Tm Instruction := ((Γ[i]? : Option (Ty Empty)).map (fun _ => θ i)).getD (.var i)
  let env' i := ((term env (fill i)).map Prod.fst).getD .unit
  have agree : ∀ ⦃i A⦄, At Γ i A → θ i = fill i := by
    intro i A hi
    change Γ[i]? = some A at hi
    simp only [fill, hi, Option.map_some, Option.getD_some]
  have termFill (i : Nat) : ∃ v, term env (fill i) = some (v, false) := by
    cases hi : Γ[i]? with
    | none =>
        simp only [fill, hi, Option.map_none, Option.getD_none]
        exact ⟨env i, rfl⟩
    | some A =>
        simp only [fill, hi, Option.map_some, Option.getD_some]
        exact value_term (hθ hi) env
  have run (i : Nat) : term env (fill i) = some (env' i, false) := by
    obtain ⟨v, hv⟩ := termFill i
    simp [env', hv]
  have env'_typed : EnvTyped Γ env' := by
    intro i A hi
    have hv := run i
    rw [← agree hi] at hv
    exact term_typed (hθ hi).hasType he hv
  rw [Paper.SingletonReification.SingleCfg.region_subst_eq hr agree,
    Paper.SingletonReification.SingleCfg.region_subst_eq hs agree, observe_subst _ run, observe_subst _ run]
  exact h env' env'_typed

omit profile in
private theorem term_pair {env : Env} {a b : Tm Instruction} {v w : Val}
    (hv : term env a = some (v, false)) (hw : term env b = some (w, false)) :
    term env (.pair a b) = some (.pair v w, false) := by simp [term, hv, hw]

omit [Fact (profile.enabled 1 = false)] in
private theorem productBeta_observe {Γ L : List (Ty Empty)} {r s : Region Instruction}
    (h : ProductBeta.Step Γ r s L) : Preserves Γ r s := by
  cases h with
  | let₂Beta ha hb _ =>
    intro env _
    obtain ⟨v, hv⟩ := value_term ha env
    obtain ⟨w, hw⟩ := value_term hb env
    change withTerm true env (.pair _ _) _ = _
    rw [withTerm_value (term_pair hv hw)]
    apply Eq.symm
    apply observe_subst
    intro i
    cases i with
    | zero => exact hw
    | succ i => exact single_realizes hv i

omit [Fact (profile.enabled 1 = false)] in
private theorem productEta_observe {Γ L : List (Ty Empty)} {r s : Region Instruction}
    (h : ProductEta.Step Γ r s L) : Preserves Γ r s := by
  cases h with
  | @let₂Eta _ i ℓ A B hi hℓ =>
      intro env he
      have typed := he hi
      cases hv : env i with
      | pair v w =>
          change withTerm true env (.var i) _ = _
          rw [withTerm_value (env := env) (a := .var i) (show term env (.var i) = some (.pair v w, false) from
            congrArg (fun v => some (v, false)) hv)]
          calc
            _ = (· = Exit.branch ℓ (.pair v w) false) :=
              observe_br (env := extend (extend env v) w) (a := .pair (.var 1) (.var 0)) rfl ℓ
            _ = _ := (observe_br (env := env) (a := .var i)
              (congrArg (fun v => some (v, false)) hv) ℓ).symm
      | atom v => exact v.elim
      | unit => rw [hv] at typed; cases typed
      | inl => rw [hv] at typed; cases typed
      | inr => rw [hv] at typed; cases typed

/-! ## Closure under all standard Paper constructors -/

private theorem paper_observe {Γ L : List (Ty Empty)} {r s : Region Instruction}
    (h : Paper.Eqv Γ r s L) : Preserves Γ r s := by
  induction h with
  | cfgEta h => exact cfgEta_observe h
  | productBeta h => exact productBeta_observe h
  | productEta h => exact productEta_observe h
  | symm _ ih => exact fun env he => (ih env he).symm
  | trans _ _ il ir => exact fun env he => (il env he).trans (ir env he)
  | let₁ ha _ ih => exact preserves_let₁ ha ih
  | let₂ ha _ ih => exact preserves_let₂ ha ih
  | case ha _ _ il ir => exact preserves_case ha il ir
  | cfg R he hb ie ib =>
    exact preserves_cfg R he.typed.1 he.typed.2
      (fun i => (hb i).typed.1) (fun i => (hb i).typed.2) ie ib
  | @lsubstCongr Γ p L K σ υ hp _ ih =>
    intro env he
    funext out
    apply propext
    rw [observe_lsubst hp, observe_lsubst hp]
    apply exists_congr
    intro x
    by_cases hx : observe env p x
    · have ⟨A, hi, hv⟩ := observe_typed hp.hasType he hx
      simp only [Post, ih hi (extend env x.value) (he.extend hv)]
    · simp [hx]
  | lsubstPost _ hr hs _ ih => exact preserves_post hr hs ih
  | substVars h hθ ih => exact preserves_value_subst h.typed.1 h.typed.2 hθ ih
  | renameLabels _ _ ih =>
    intro env he
    funext out
    apply propext
    rw [observe_renameLabels, observe_renameLabels, ih env he]
  | @collapsePost Γ e A L p K σ he hp hσ =>
    have hl : ValueBranches Γ (CfgEta.Codiagonal.nested e p) L :=
      .cfg (fun _ : Fin 1 => A) he (fun _ => .cfg (fun _ : Fin 1 => A) (.br (ℓ := 0) rfl (.var rfl))
        (fun _ => hp.renameVars ((Ren.wk Γ A).lift A)))
    have hr : ValueBranches Γ (CfgEta.Codiagonal.flattened e p) L := by
      apply ValueBranches.cfg (fun _ : Fin 1 => A) he
      intro _
      rw [renameLabels_eq_lsubst]
      exact hp.lsubst (fun i _ hi => .br (ℓ := i.pred) (CfgEta.Codiagonal.mergeLabels A L hi) (.var rfl))
    exact preserves_post hl hr (fun env _ => codiagonal_observe env)
  | uniform he hp hq ha _ ih => exact uniform_observe he hp ha ih

omit [Fact (profile.enabled 1 = false)] in
private theorem entryLet_step_observe (quiet : profile.keepUnaryEffect = false)
    {Γ L : List (Ty Empty)} {r s : Region Instruction}
    (h : Paper.WithEntryLet.Step Γ r s L) : Preserves Γ r s := by
  cases h with
  | @seq n Γ L S a d blocks R ha hd hb =>
    intro env _
    have rows (v w : Val) (i : Fin n) :
        observe (extend (extend env v) w)
          ((blocks i).renameVars (Silmaril.DeBruijn.lift Nat.succ)) =
        observe (extend env w) (blocks i) := by
      rw [renameVars_eq_substVars]
      exact observe_subst _ (fun j => by cases j <;> rfl)
    funext out
    apply propext
    simp only [observe, quiet, withTerm, Bool.false_and, prepend_false, rows]
    constructor
    · rintro ⟨first, count, ⟨v, e, he, _, hd, rfl⟩, follow⟩
      exact ⟨v, e, he, out, ⟨_, count, hd, follow⟩, rfl⟩
    · rintro ⟨v, e, he, _, ⟨first, count, hd, follow⟩, rfl⟩
      exact ⟨first, count, ⟨v, e, he, first, hd, rfl⟩, follow⟩

/-- When unary bind and case effects do not contribute a prefix mark, the
diagnostic also respects the full contextual entry-let extension. -/
private theorem entryLet_observe (quiet : profile.keepUnaryEffect = false)
    {Γ L : List (Ty Empty)} {r s : Region Instruction}
    (h : Paper.WithEntryLet.Eqv Γ r s L) : Preserves Γ r s := by
  induction h with
  | paper h => exact paper_observe h
  | extra _ _ h => exact entryLet_step_observe quiet h
  | symm _ ih => exact fun env he => (ih env he).symm
  | trans _ _ il ir => exact fun env he => (il env he).trans (ir env he)
  | let₁ ha _ ih => exact preserves_let₁ ha ih
  | let₂ ha _ ih => exact preserves_let₂ ha ih
  | case ha _ _ il ir => exact preserves_case ha il ir
  | cfg R he hb ie ib =>
    exact preserves_cfg R he.typed.1 he.typed.2
      (fun i => (hb i).typed.1) (fun i => (hb i).typed.2) ie ib
  | @lsubstCongr Γ p L K σ υ hp _ ih =>
    intro env he
    funext out
    apply propext
    rw [observe_lsubst hp, observe_lsubst hp]
    apply exists_congr
    intro x
    by_cases hx : observe env p x
    · have ⟨A, hi, hv⟩ := observe_typed hp.hasType he hx
      simp only [Post, ih hi (extend env x.value) (he.extend hv)]
    · simp [hx]
  | lsubstPost _ hr hs _ ih => exact preserves_post hr hs ih
  | substVars h hθ ih => exact preserves_value_subst h.typed.1 h.typed.2 hθ ih
  | renameLabels _ _ ih =>
    intro env he
    funext out
    apply propext
    rw [observe_renameLabels, observe_renameLabels, ih env he]

end Flat

section Destructure

private local instance : MarkArity where
  enabled n := decide (2 ≤ n)
  keepUnaryEffect := false

private local instance : Fact (MarkArity.enabled 1 = false) := ⟨rfl⟩

open Paper.EntryLetObstruction.Destructure

theorem destructure_reentry_ne : ¬ Paper.WithEntryLet.Eqv [] original reentered [U] := by
  intro eq
  let env : Env := fun _ => .unit
  have he : EnvTyped [] env := by intro i A hi; simp [At] at hi
  have before : observe env original ⟨0, .unit, true, true⟩ := execute_sound 4 _ env rfl
  have after : observe env reentered ⟨0, .unit, true, false⟩ := execute_sound 4 _ env rfl
  have same := entryLet_observe rfl eq env he
  exact Bool.noConfusion (congrArg Exit.marked (observe_unique _ env (same ▸ before) after))

theorem destructure_recurring_ne :
    let A := Silmaril.coprod U U
    let θ := Tm.singleSubst (.unit : Tm Instruction) ∘ Silmaril.DeBruijn.lift Nat.succ
    ¬ Paper.WithEntryLet.Eqv [A] ((recurring moved).substVars θ) ((recurring original).substVars θ) [A] := by
  intro A θ eq
  let env : Env := fun _ => .inl .unit
  have he : EnvTyped [A] env := by
    intro i T hi
    cases i with
    | zero => cases Option.some.inj hi; exact .inl .unit
    | succ i => simp [At] at hi
  have movedRun : observe env ((recurring moved).substVars θ) ⟨0, .inr .unit, true, false⟩ :=
    execute_sound 4 _ env rfl
  have flatRun : observe env ((recurring original).substVars θ) ⟨0, .inr .unit, true, true⟩ :=
    execute_sound 4 _ env rfl
  have same := entryLet_observe rfl eq env he
  exact Bool.noConfusion (congrArg Exit.marked (observe_unique _ env (same ▸ movedRun) flatRun))

end Destructure

private local instance : MarkArity where
  enabled n := decide (2 ≤ n)

private local instance : Fact (MarkArity.enabled 1 = false) := ⟨rfl⟩

open Paper.EntryLetObstruction

/-- Observe a finite run using arity-local diagnostic marks. -/
def observesFlat (env : Semantics.Env Empty) (r : Region Instruction) (out : Observation) : Prop :=
  observe env r ⟨out.label, out.payload, out.effect, out.marked⟩

theorem observesFlat_eq_of_paper {Γ L : List (Ty Empty)} {r s : Region Instruction}
    (h : Paper.Eqv Γ r s L) (env : Semantics.Env Empty)
    (he : Resumption.Typing.EnvTyped (fun (_ _ : Empty) => False) Γ env) (out : Observation) :
    observesFlat env r out ↔ observesFlat env s out :=
  iff_of_eq (congrFun (paper_observe h env he) _)

theorem discardedRecurringRequest_ne :
    let B := Silmaril.coprod U U
    let θ : Nat → Tm Instruction := Tm.singleSubst .unit ∘ Silmaril.DeBruijn.lift Nat.succ
    ¬ Paper.Eqv [B] (movedRecurringRequest.substVars θ) (flatRecurringRequest.substVars θ) [B] := by
  intro B θ eq
  let env : Semantics.Env Empty := fun _ => .inl .unit
  have he : EnvTyped [B] env := by
    intro i A h
    cases i with
    | zero => cases Option.some.inj h; exact .inl .unit
    | succ i => simp [At] at h
  let x : Exit := ⟨0, .inr .unit, true, false⟩
  let y : Exit := ⟨0, .inr .unit, true, true⟩
  have hx : observe env (movedRecurringRequest.substVars θ) x :=
    execute_sound 4 _ env rfl
  have hy : observe env (flatRecurringRequest.substVars θ) y :=
    execute_sound 4 _ env rfl
  have hx' : observe env (flatRecurringRequest.substVars θ) x :=
    (observesFlat_eq_of_paper eq env he ⟨x.label, x.value, x.effect, x.marked⟩).1 hx
  exact Bool.noConfusion (congrArg Exit.marked (observe_unique _ env hx' hy))

theorem unfinishedRequests_ne_bothMoved {r : Region Instruction}
    (hr : r = twoFlatRequests ∨ r = firstRequestMoved ∨ r = secondRequestMoved) :
    let B := Silmaril.coprod U U
    let θ : Nat → Tm Instruction := Tm.singleSubst .unit ∘ Silmaril.DeBruijn.lift Nat.succ
    ¬ Paper.Eqv [B] (r.substVars θ) (bothRequestsMoved.substVars θ) [B] := by
  intro B θ eq
  let env : Semantics.Env Empty := fun _ => .inl .unit
  have he : EnvTyped [B] env := by
    intro i A h
    cases i with
    | zero => cases Option.some.inj h; exact .inl .unit
    | succ i => simp [At] at h
  let marked : Exit := ⟨0, .inr .unit, true, true⟩
  let unmarked : Exit := ⟨0, .inr .unit, true, false⟩
  have hx : observe env (r.substVars θ) marked := by
    rcases hr with rfl | rfl | rfl <;> exact execute_sound 4 _ env rfl
  have hy : observe env (bothRequestsMoved.substVars θ) unmarked :=
    execute_sound 4 _ env rfl
  have hx' : observe env (bothRequestsMoved.substVars θ) marked :=
    (observesFlat_eq_of_paper eq env he ⟨marked.label, marked.value, marked.effect, marked.marked⟩).1 hx
  exact Bool.noConfusion (congrArg Exit.marked (observe_unique _ env hx' hy))

theorem oneMovedRequest_no_image (q : Region Instruction) :
    let B := Silmaril.coprod U U
    ¬ Paper.Eqv [B] (q.substVars discardInput) oneMovedRequest [B] := by
  intro B eq
  let input (v : Val) : Env := fun i => if i = 0 then v else .unit
  have typed (v : Val) (hv : Resumption.Typing.ValueTyped (fun (_ _ : Empty) => False) v B) :
      EnvTyped [B] (input v) := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact hv
    | succ i => simp [At] at hi
  have diagonal (v : Val) :
      observe (input v) (q.substVars discardInput) = observe unitEnv q := by
    apply observe_subst
    intro i
    cases i <;> rfl
  let unmarked : Exit := ⟨0, .inr .unit, true, false⟩
  let marked : Exit := ⟨0, .inr .unit, true, true⟩
  have left : observe (input (.inl .unit)) oneMovedRequest unmarked :=
    execute_sound 4 _ _ rfl
  have right : observe (input (.inr .unit)) oneMovedRequest marked :=
    execute_sound 4 _ _ rfl
  have same := (paper_observe eq (input (.inl .unit)) (typed _ (.inl .unit))).symm ▸ left
  rw [diagonal] at same
  have same' : observe (input (.inr .unit)) (q.substVars discardInput) unmarked := by
    rw [diagonal]
    exact same
  have contrad := (paper_observe eq (input (.inr .unit)) (typed _ (.inr .unit))) ▸ same'
  exact Bool.noConfusion (congrArg Exit.marked (observe_unique _ _ contrad right))

private theorem unitEnv_typed : EnvTyped [U] unitEnv := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .unit
  | succ i => simp [At] at hi

private theorem rows_typed {Γ : VCtx (Ty Empty)} :
    ∀ i : Fin 2, ValueBranches (U :: Γ) (blocks i) [U, U, U] :=
  Fin.cases (.br rfl (.var rfl)) (fun _ => .br rfl (.var rfl))

theorem flatRequest_typed : ValueBranches [U] flatRequest [U] :=
  .cfg (fun _ : Fin 2 => U) (.let₁ (.op (.var rfl)) (.br rfl (.var rfl))) rows_typed

theorem movedRequest_typed : ValueBranches [U] movedRequest [U] :=
  .let₁ (.op (.var rfl)) (.cfg (fun _ : Fin 2 => U) (.br rfl (.var rfl))
    (fun i => (rows_typed (Γ := [U]) i).renameVars ((Ren.wk [U] U).lift U)))

theorem flatRequest_marked : observesFlat unitEnv flatRequest (finish true) :=
  execute_sound 4 flatRequest unitEnv rfl

theorem movedRequest_unmarked : observesFlat unitEnv movedRequest (finish false) :=
  execute_sound 4 movedRequest unitEnv rfl

theorem flatRequest_ne_moved : ¬ Paper.Eqv [U] flatRequest movedRequest [U] := by
  intro heq
  have tagged := (observesFlat_eq_of_paper heq unitEnv unitEnv_typed (finish true)).mp flatRequest_marked
  have same := observe_unique movedRequest unitEnv tagged movedRequest_unmarked
  exact Bool.noConfusion (congrArg Exit.marked same)

theorem entryLet_two_fails :
    ¬ CfgEta.EntryLet (Paper.Eqv (τ := Ty Empty) (Φ := Instruction)) 2 :=
  fun h => flatRequest_ne_moved (h (fun _ => U) (.op (.var rfl)) (.br rfl (.var rfl)) rows_typed)

theorem unary_under_flat :
    Paper.Eqv [U] nestedRequest nestedMoved [U] := by
  refine .cfg (fun _ : Fin 2 => U) ?_ (fun i => Paper.Eqv.refl (rows_typed i).hasType)
  exact .cfgEta (CfgEta.entryLet_of_le_one (by decide : 1 ≤ 1) (fun _ => U)
    (.op (.var rfl)) (.br rfl (.var rfl)) (fun _ => .br rfl (.var rfl)))

theorem unary_under_flat_marked :
    observesFlat unitEnv nestedRequest (finish true) ∧ observesFlat unitEnv nestedMoved (finish true) :=
  let h : observesFlat unitEnv nestedRequest (finish true) := execute_sound 4 nestedRequest unitEnv rfl
  ⟨h, (observesFlat_eq_of_paper unary_under_flat unitEnv unitEnv_typed (finish true)).mp h⟩



end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Sequencing
