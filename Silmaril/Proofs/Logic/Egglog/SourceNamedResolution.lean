module

public import Silmaril.Logic.Egglog.Source.Named.Resolution.Defs
public import Mathlib.Data.List.Nodup

@[expose] public section
namespace Silmaril.Logic.Egglog.Source.Named
open Silmaril.Logic.Institution.Examples

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Erasure retains every ordered constructor argument, including nullary ones. -/
def eraseTerm {D : Declarations} (Γ : CheckedContext D) :
    {s : D.LocalSort} → EQ.Term D.signature.toSignature Γ.profile s → RawTerm
  | _, .var i => .var (Γ.bindings.get i).name
  | _, .app o arguments => .app o.val.name _ (fun i => eraseTerm Γ (arguments i))

/-- Structural independent meaning for every represented local typed total term. -/
theorem eraseTerm_denotes {D : Declarations} (Γ : CheckedContext D)
    (M : Core.Model D.signature) (ρ : Valuation M Γ) {s : D.LocalSort}
    (term : EQ.Term D.signature.toSignature Γ.profile s) :
    (eraseTerm Γ term).Denotes M Γ ρ s (term.eval M.toAlgebra ρ) := by
  exact EQ.Term.rec (motive := fun s term =>
    (eraseTerm Γ term).Denotes M Γ ρ s (term.eval M.toAlgebra ρ))
    (fun i => .var i _ rfl)
    (fun o arguments ih => .app o _ rfl _ _ ih) term

/-- Unique finite source declarations make constructor lookup deterministic;
this is about declared names, not constructor freeness in semantic models. -/
theorem constructor_name_injective (D : Declarations) {left right : TotalDeclaration}
    (hl : left ∈ D.data.constructors) (hr : right ∈ D.data.constructors)
    (same : left.name = right.name) : left = right := by
  have unique : (D.data.constructors.map TotalDeclaration.name).Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp D.valid.2.1).1).1
  exact List.inj_on_of_nodup_map unique hl hr same

/-- Variable lookup is positional and unique, retaining the exact whole context. -/
theorem binding_name_injective {D : Declarations} (Γ : CheckedContext D)
    {i j : Fin Γ.bindings.length}
    (same : (Γ.bindings.get i).name = (Γ.bindings.get j).name) : i = j := by
  have mapped : (Γ.bindings.map Binding.name).get ⟨i.val, by simpa only [List.length_map] using i.isLt⟩ =
      (Γ.bindings.map Binding.name).get ⟨j.val, by simpa only [List.length_map] using j.isLt⟩ := by
    simpa using same
  have positions := Γ.unique.injective_get mapped
  exact Fin.ext (congrArg (fun x : Fin (Γ.bindings.map Binding.name).length => x.val) positions)

/-- Same constructor spelling fixes the entire ordered profile and declaration
witness. Heterogeneous symbol equality records the profile transport explicitly. -/
theorem constructor_profile_unique {D : Declarations} {n : Nat}
    {w v : Fin n → D.LocalSort} {s t : D.LocalSort}
    (left : D.signature.Op n w s) (right : D.signature.Op n v t)
    (same : left.val.name = right.val.name) :
    w = v ∧ s = t ∧ HEq left right := by
  have declaration := constructor_name_injective D left.property.1 right.property.1 same
  have inputs : List.ofFn (fun i => (w i).val) = List.ofFn (fun i => (v i).val) :=
    left.property.2.1.symm.trans ((congrArg TotalDeclaration.inputs declaration).trans
      right.property.2.1)
  have profiles : w = v := by
    funext i
    exact Subtype.ext (congrFun (List.ofFn_injective inputs) i)
  have outputs : s = t := Subtype.ext
    (left.property.2.2.symm.trans ((congrArg TotalDeclaration.output declaration).trans
      right.property.2.2))
  refine ⟨profiles, outputs, ?_⟩
  subst v
  subst t
  exact heq_of_eq (Subtype.ext declaration)

/-- Independent sorted named denotation is single-valued, even when carriers
are empty or constructors identify values. The value and sort travel together. -/
theorem denotes_unique {D : Declarations} (Γ : CheckedContext D)
    (M : Core.Model D.signature) (ρ : Valuation M Γ) {raw : RawTerm}
    {s : D.LocalSort} {value : M.carrier s} (denotes : raw.Denotes M Γ ρ s value) :
    ∀ (t : D.LocalSort) (other : M.carrier t), raw.Denotes M Γ ρ t other →
      (⟨s, value⟩ : Σ s, M.carrier s) = ⟨t, other⟩ := by
  induction denotes with
  | var i name named =>
      intro t other second
      cases second with
      | var j _ named' =>
          have positions := binding_name_injective Γ (named.trans named'.symm)
          subst j
          rfl
  | app o name named arguments values denotes ih =>
      intro t other second
      cases second with
      | app p _ named' _ otherValues otherDenotes =>
          obtain ⟨profiles, outputs, symbols⟩ :=
            constructor_profile_unique o p (named.trans named'.symm)
          subst_vars
          have valuesEqual : values = otherValues := by
            funext i
            exact eq_of_heq (Sigma.mk.inj (ih i _ _ (otherDenotes i))).2
          subst otherValues
          rfl

/-- Successful executable constructor lookup retains the original declared name. -/
theorem constructor?_name (D : Declarations) (name : String) (n : Nat)
    (result : ConstructorAt D n) (found : constructor? D name n = some result) :
    result.2.2.val.name = name := by
  unfold constructor? at found
  obtain ⟨declaration, _, chosen⟩ := List.exists_of_findSome?_eq_some found
  split at chosen
  · rename_i named
    split at chosen
    · rename_i arity
      subst n
      cases Option.some.inj chosen
      exact named
    · contradiction
  · contradiction

/-- Every coordinate of a successful dependent tuple traversal is retained. -/
theorem sequence_component (n : Nat) {β : Fin n → Type}
    (f : (i : Fin n) → Option (β i)) (arguments : (i : Fin n) → β i)
    (success : sequence? n f = some arguments) : ∀ i, f i = some (arguments i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      cases hf : f 0 with
      | none => simp [sequence?, hf] at success
      | some first =>
          cases hr : sequence? n (fun i => f i.succ) with
          | none => simp [sequence?, hf, hr] at success
          | some rest =>
              simp [sequence?, hf, hr] at success
              subst arguments
              intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · exact hf
              · exact ih _ rest hr j

/-- Successful checked transport retains the original term and its sort. -/
theorem termAt?_eq {D : Declarations} {Γ : CheckedContext D} (s : D.LocalSort)
    (packed : PackedTerm Γ) (term : EQ.Term D.signature.toSignature Γ.profile s)
    (success : termAt? s packed = some term) : packed = ⟨s, term⟩ := by
  rcases packed with ⟨sort, original⟩
  unfold termAt? at success
  split at success
  · rename_i equal
    change sort = s at equal
    subst sort
    cases Option.some.inj success
    rfl
  · contradiction

/-- Successful resolution preserves the entire source term, not merely an
abstract equivalent: every original name, nullary call and ordered child remains. -/
theorem resolveTerm_erase {D : Declarations} (Γ : CheckedContext D) (raw : RawTerm)
    (resolved : PackedTerm Γ) (success : resolveTerm? Γ raw = some resolved) :
    eraseTerm Γ resolved.2 = raw := by
  induction raw generalizing resolved with
  | var name =>
      cases hi : (List.finRange Γ.bindings.length).find?
          (fun i => (Γ.bindings.get i).name == name) with
      | none =>
          simp only [resolveTerm?, hi, bind, Option.bind] at success
          cases success
      | some i =>
          simp only [resolveTerm?, hi, bind, Option.bind, Option.pure_def,
            Option.some.injEq] at success
          subst resolved
          exact congrArg RawTerm.var (by simpa using List.find?_some hi)
  | app name n arguments ih =>
      cases hc : constructor? D name n with
      | none =>
          simp only [resolveTerm?, hc, bind, Option.bind] at success
          cases success
      | some symbol =>
          rcases symbol with ⟨w, s, o⟩
          cases hr : sequence? n (fun i => do
              let packed ← resolveTerm? Γ (arguments i)
              termAt? (w i) packed) with
          | none =>
              simp only [bind, Option.bind] at hr
              simp only [resolveTerm?, hc, bind, Option.bind, hr] at success
              cases success
          | some terms =>
              simp only [bind, Option.bind] at hr
              simp only [resolveTerm?, hc, bind, Option.bind, hr, Option.pure_def,
                Option.some.injEq] at success
              subst resolved
              have named := constructor?_name D name n ⟨w, s, o⟩ hc
              change o.val.name = name at named
              simp only [eraseTerm]
              rw [named]
              apply congrArg (RawTerm.app name n)
              funext i
              have component := sequence_component n _ terms hr i
              cases hp : resolveTerm? Γ (arguments i) with
              | none => simp [hp] at component
              | some packed =>
                  have transported : termAt? (w i) packed = some (terms i) := by
                    simpa [hp] using component
                  have original := termAt?_eq (w i) packed (terms i) transported
                  rw [original] at hp
                  exact ih i _ hp

/-- Full exact open-context adequacy, proved against independent raw denotation. -/
theorem resolveTerm_denotes_iff {D : Declarations} (Γ : CheckedContext D) (raw : RawTerm)
    (resolved : PackedTerm Γ) (success : resolveTerm? Γ raw = some resolved)
    (M : Core.Model D.signature) (ρ : Valuation M Γ) (value : M.carrier resolved.1) :
    raw.Denotes M Γ ρ resolved.1 value ↔ resolved.2.eval M.toAlgebra ρ = value := by
  rw [← resolveTerm_erase Γ raw resolved success]
  have canonical := eraseTerm_denotes Γ M ρ resolved.2
  constructor
  · intro denotes
    exact eq_of_heq (Sigma.mk.inj (denotes_unique Γ M ρ canonical _ _ denotes)).2
  · intro equal
    rw [← equal]
    exact canonical

theorem relation?_name (D : Declarations) (name : String) (n : Nat)
    (result : RelationAt D n) (found : relation? D name n = some result) :
    result.2.val.name = name := by
  unfold relation? at found
  obtain ⟨declaration, _, chosen⟩ := List.exists_of_findSome?_eq_some found
  split at chosen
  · rename_i named
    split at chosen
    · rename_i arity
      subst n
      cases Option.some.inj chosen
      exact named
    · contradiction
  · contradiction

theorem function?_name (D : Declarations) (name : String) (n : Nat)
    (result : FunctionAt D n) (found : function? D name n = some result) :
    result.2.2.val.name = name := by
  unfold function? at found
  obtain ⟨declaration, _, chosen⟩ := List.exists_of_findSome?_eq_some found
  split at chosen
  · rename_i named
    split at chosen
    · rename_i arity
      subst n
      cases Option.some.inj chosen
      exact named
    · contradiction
  · contradiction

def eraseAtom {D : Declarations} (Γ : CheckedContext D) :
    Core.Atom D.signature Γ.profile → RawAtom
  | .equal equality => .equal (eraseTerm Γ equality.lhs) (eraseTerm Γ equality.rhs)
  | .relation r arguments => .relation r.val.name _ (fun i => eraseTerm Γ (arguments i))
  | .row f arguments value =>
      .row f.val.name _ (fun i => eraseTerm Γ (arguments i)) (eraseTerm Γ value)

/-- Checked dependent arguments retain exactly the original ordered source list. -/
theorem resolveArguments_erase {D : Declarations} (Γ : CheckedContext D) {n : Nat}
    (w : Fin n → D.LocalSort) (arguments : Fin n → RawTerm)
    (terms : ∀ i, EQ.Term D.signature.toSignature Γ.profile (w i))
    (success : sequence? n (fun i => do
      let packed ← resolveTerm? Γ (arguments i)
      termAt? (w i) packed) = some terms) :
    (fun i => eraseTerm Γ (terms i)) = arguments := by
  funext i
  have component := sequence_component n _ terms success i
  cases hp : resolveTerm? Γ (arguments i) with
  | none => simp [hp] at component
  | some packed =>
      have transported : termAt? (w i) packed = some (terms i) := by
        simpa [hp] using component
      have original := termAt?_eq (w i) packed (terms i) transported
      rw [original] at hp
      exact resolveTerm_erase Γ (arguments i) _ hp

/-- Successful atom resolution retains exact equality terms, predicate/table
kind, all input coordinates and the explicit partial-row output term. -/
theorem resolveAtom_erase {D : Declarations} (Γ : CheckedContext D) (raw : RawAtom)
    (resolved : Core.Atom D.signature Γ.profile)
    (success : resolveAtom? Γ raw = some resolved) : eraseAtom Γ resolved = raw := by
  cases raw with
  | equal left right =>
      cases hl : resolveTerm? Γ left with
      | none => simp [resolveAtom?, hl] at success
      | some packedLeft =>
          rcases packedLeft with ⟨sort, typedLeft⟩
          cases hr : resolveTerm? Γ right with
          | none => simp [resolveAtom?, hl, hr] at success
          | some packedRight =>
              cases ht : termAt? sort packedRight with
              | none => simp [resolveAtom?, hl, hr, ht] at success
              | some typedRight =>
                  simp [resolveAtom?, hl, hr, ht] at success
                  subst resolved
                  have rightOriginal := termAt?_eq sort packedRight typedRight ht
                  rw [rightOriginal] at hr
                  simp only [eraseAtom]
                  rw [resolveTerm_erase Γ left _ hl, resolveTerm_erase Γ right _ hr]
  | relation name n arguments =>
      cases hr : relation? D name n with
      | none => simp [resolveAtom?, hr] at success
      | some symbol =>
          rcases symbol with ⟨w, r⟩
          cases ha : sequence? n (fun i => do
              let packed ← resolveTerm? Γ (arguments i)
              termAt? (w i) packed) with
          | none =>
              simp only [bind, Option.bind] at ha
              simp only [resolveAtom?, hr, bind, Option.bind, ha, Option.pure_def] at success
              cases success
          | some terms =>
              simp only [bind, Option.bind] at ha
              simp only [resolveAtom?, hr, bind, Option.bind, ha, Option.pure_def, Option.some.injEq] at success
              subst resolved
              have named := relation?_name D name n ⟨w, r⟩ hr
              change r.val.name = name at named
              simp only [eraseAtom]
              rw [named, resolveArguments_erase Γ w arguments terms ha]
  | row name n arguments value =>
      cases hf : function? D name n with
      | none => simp [resolveAtom?, hf] at success
      | some symbol =>
          rcases symbol with ⟨w, sort, f⟩
          cases ha : sequence? n (fun i => do
              let packed ← resolveTerm? Γ (arguments i)
              termAt? (w i) packed) with
          | none =>
              simp only [bind, Option.bind] at ha
              simp only [resolveAtom?, hf, bind, Option.bind, ha] at success
              cases success
          | some terms =>
              simp only [bind, Option.bind] at ha
              cases hv : resolveTerm? Γ value with
              | none =>
                  simp only [resolveAtom?, hf, bind, Option.bind, ha, hv] at success
                  cases success
              | some packedValue =>
                  cases ht : termAt? sort packedValue with
                  | none =>
                      simp only [resolveAtom?, hf, bind, Option.bind, ha, hv, ht] at success
                      cases success
                  | some typedValue =>
                      simp only [resolveAtom?, hf, bind, Option.bind, ha, hv, ht, Option.pure_def,
                        Option.some.injEq] at success
                      subst resolved
                      have valueOriginal := termAt?_eq sort packedValue typedValue ht
                      rw [valueOriginal] at hv
                      have named := function?_name D name n ⟨w, sort, f⟩ hf
                      change f.val.name = name at named
                      simp only [eraseAtom]
                      rw [named, resolveArguments_erase Γ w arguments terms ha,
                        resolveTerm_erase Γ value _ hv]

theorem relation_profile_unique {D : Declarations} {n : Nat}
    {w v : Fin n → D.LocalSort} (left : D.signature.Rel n w) (right : D.signature.Rel n v)
    (same : left.val.name = right.val.name) : w = v ∧ HEq left right := by
  have unique : (D.data.relations.map RelationDeclaration.name).Nodup :=
    (List.nodup_append.mp (List.nodup_append.mp D.valid.2.1).1).2.1
  have declaration := List.inj_on_of_nodup_map unique left.property.1 right.property.1 same
  have inputs : List.ofFn (fun i => (w i).val) = List.ofFn (fun i => (v i).val) :=
    left.property.2.symm.trans ((congrArg RelationDeclaration.inputs declaration).trans
      right.property.2)
  have profiles : w = v := by
    funext i
    exact Subtype.ext (congrFun (List.ofFn_injective inputs) i)
  refine ⟨profiles, ?_⟩
  subst v
  exact heq_of_eq (Subtype.ext declaration)

theorem function_profile_unique {D : Declarations} {n : Nat}
    {w v : Fin n → D.LocalSort} {s t : D.LocalSort}
    (left : D.signature.Function n w s) (right : D.signature.Function n v t)
    (same : left.val.name = right.val.name) : w = v ∧ s = t ∧ HEq left right := by
  have unique : (D.data.functions.map TotalDeclaration.name).Nodup :=
    (List.nodup_append.mp D.valid.2.1).2.1
  have declaration := List.inj_on_of_nodup_map unique left.property.1 right.property.1 same
  have inputs : List.ofFn (fun i => (w i).val) = List.ofFn (fun i => (v i).val) :=
    left.property.2.1.symm.trans ((congrArg TotalDeclaration.inputs declaration).trans
      right.property.2.1)
  have profiles : w = v := by
    funext i
    exact Subtype.ext (congrFun (List.ofFn_injective inputs) i)
  have outputs : s = t := Subtype.ext
    (left.property.2.2.symm.trans ((congrArg TotalDeclaration.output declaration).trans
      right.property.2.2))
  refine ⟨profiles, outputs, ?_⟩
  subst v
  subst t
  exact heq_of_eq (Subtype.ext declaration)

/-- Every independently denoted erased term is its actual typed evaluation. -/
theorem eraseTerm_denotes_iff {D : Declarations} (Γ : CheckedContext D)
    (M : Core.Model D.signature) (ρ : Valuation M Γ) {s : D.LocalSort}
    (term : EQ.Term D.signature.toSignature Γ.profile s) (value : M.carrier s) :
    (eraseTerm Γ term).Denotes M Γ ρ s value ↔ term.eval M.toAlgebra ρ = value := by
  have canonical := eraseTerm_denotes Γ M ρ term
  constructor
  · intro denotes
    exact eq_of_heq (Sigma.mk.inj (denotes_unique Γ M ρ canonical _ _ denotes)).2
  · intro equal
    rw [← equal]
    exact canonical

/-- Exact satisfaction of every erased atom, preserving partial-table rows and
all ordered profiles in arbitrary actual Core models. -/
theorem eraseAtom_holds_iff {D : Declarations} (Γ : CheckedContext D)
    (M : Core.Model D.signature) (ρ : Valuation M Γ)
    (atom : Core.Atom D.signature Γ.profile) :
    (eraseAtom Γ atom).Holds M Γ ρ ↔ atom.Holds M ρ := by
  cases atom with
  | equal equality =>
      constructor
      · rintro ⟨sort, left, right, hl, hr, equal⟩
        have canonical := eraseTerm_denotes Γ M ρ equality.lhs
        have same := denotes_unique Γ M ρ canonical _ _ hl
        cases same
        have value := (eraseTerm_denotes_iff Γ M ρ equality.rhs _).mp hr
        exact equal.trans value.symm
      · intro equal
        exact ⟨equality.sort, _, _, eraseTerm_denotes Γ M ρ equality.lhs,
          eraseTerm_denotes Γ M ρ equality.rhs, equal⟩
  | relation r arguments =>
      constructor
      · rintro ⟨profile, other, values, named, denotes, holds⟩
        obtain ⟨profiles, symbols⟩ := relation_profile_unique other r named
        subst profile
        cases eq_of_heq symbols
        have valuesEqual : (fun i => (arguments i).eval M.toAlgebra ρ) = values :=
          funext (fun i => (eraseTerm_denotes_iff Γ M ρ (arguments i) _).mp (denotes i))
        change M.rel r (fun i => (arguments i).eval M.toAlgebra ρ)
        rw [valuesEqual]
        exact holds
      · intro holds
        exact ⟨_, r, _, rfl, fun i => eraseTerm_denotes Γ M ρ (arguments i), holds⟩
  | row f arguments value =>
      constructor
      · rintro ⟨profile, sort, other, values, output, named, denotes, outputDenotes, holds⟩
        obtain ⟨profiles, outputs, symbols⟩ := function_profile_unique other f named
        subst profile
        subst sort
        cases eq_of_heq symbols
        have valuesEqual : (fun i => (arguments i).eval M.toAlgebra ρ) = values :=
          funext (fun i => (eraseTerm_denotes_iff Γ M ρ (arguments i) _).mp (denotes i))
        have outputEqual := (eraseTerm_denotes_iff Γ M ρ value _).mp outputDenotes
        change M.row f (fun i => (arguments i).eval M.toAlgebra ρ) (value.eval M.toAlgebra ρ)
        rw [valuesEqual, outputEqual]
        exact holds
      · intro holds
        exact ⟨_, _, f, _, _, rfl, fun i => eraseTerm_denotes Γ M ρ (arguments i),
          eraseTerm_denotes Γ M ρ value, holds⟩

/-- Full equality/predicate/partial-row resolver adequacy against independent truth. -/
theorem resolveAtom_holds_iff {D : Declarations} (Γ : CheckedContext D) (raw : RawAtom)
    (resolved : Core.Atom D.signature Γ.profile)
    (success : resolveAtom? Γ raw = some resolved)
    (M : Core.Model D.signature) (ρ : Valuation M Γ) :
    raw.Holds M Γ ρ ↔ resolved.Holds M ρ := by
  rw [← resolveAtom_erase Γ raw resolved success]
  exact eraseAtom_holds_iff Γ M ρ resolved

theorem CheckedContext.eq_of_bindings {D : Declarations} (left right : CheckedContext D)
    (same : left.bindings = right.bindings) : left = right := by
  cases left
  cases right
  cases same
  rfl

theorem context_check_bindings (D : Declarations) (bindings : Context)
    (context : CheckedContext D) (success : Context.check D bindings = some context) :
    context.bindings = bindings := by
  unfold Context.check at success
  split at success
  · cases Option.some.inj success
    rfl
  · contradiction

private theorem rule_holds_context {D : Declarations} (Γ : CheckedContext D)
    (M : Core.Model D.signature) (body : List RawAtom) (head : RawAtom) :
    (RawSentence.rule Γ.bindings body head).Holds M ↔
      ∀ ρ : Valuation M Γ, (∀ a ∈ body, a.Holds M Γ ρ) → head.Holds M Γ ρ := by
  constructor
  · rintro ⟨other, bindings, holds⟩
    have same := CheckedContext.eq_of_bindings other Γ bindings
    subst other
    exact holds
  · intro holds
    exact ⟨Γ, rfl, holds⟩

private theorem query_holds_context {D : Declarations} (Γ : CheckedContext D)
    (M : Core.Model D.signature) (goals : List RawAtom) :
    (RawSentence.query Γ.bindings goals).Holds M ↔
      ∃ ρ : Valuation M Γ, ∀ a ∈ goals, a.Holds M Γ ρ := by
  constructor
  · rintro ⟨other, bindings, holds⟩
    have same := CheckedContext.eq_of_bindings other Γ bindings
    subst other
    exact holds
  · intro holds
    exact ⟨Γ, rfl, holds⟩

/-- A successful whole-list traversal compares every original entry, not merely
one chosen query or a subset of rules. -/
theorem mapM_forall_iff {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (success : xs.mapM f = some ys) (P : α → Prop) (Q : β → Prop)
    (adequacy : ∀ x y, f x = some y → (P x ↔ Q y)) :
    (∀ x ∈ xs, P x) ↔ ∀ y ∈ ys, Q y := by
  induction xs generalizing ys with
  | nil =>
      simp at success
      subst ys
      simp
  | cons first rest ih =>
      cases hf : f first with
      | none => simp [hf] at success
      | some value =>
          cases hr : rest.mapM f with
          | none => simp [hf, hr] at success
          | some tail =>
              simp [hf, hr] at success
              subst ys
              simp only [List.forall_mem_cons]
              exact and_congr (adequacy first value hf) (ih tail hr)

/-- Exact rule/query adequacy retains all universal/existential context entries,
including unused variables at empty sorts and one shared assignment per query. -/
theorem resolveSentence_holds_iff (D : Declarations) (raw : RawSentence)
    (resolved : Core.Sentence D.signature) (success : resolveSentence? D raw = some resolved)
    (M : Core.Model D.signature) : raw.Holds M ↔ resolved.Holds M := by
  cases raw with
  | rule context body head =>
      cases hc : Context.check D context with
      | none => simp [resolveSentence?, hc] at success
      | some Γ =>
          cases hb : body.mapM (resolveAtom? Γ) with
          | none => simp [resolveSentence?, hc, hb] at success
          | some typedBody =>
              cases hh : resolveAtom? Γ head with
              | none => simp [resolveSentence?, hc, hb, hh] at success
              | some typedHead =>
                  simp [resolveSentence?, hc, hb, hh] at success
                  subst resolved
                  have bindings := context_check_bindings D context Γ hc
                  change (RawSentence.rule context body head).Holds M ↔
                    ∀ ρ, (∀ a ∈ typedBody, a.Holds M ρ) → typedHead.Holds M ρ
                  rw [← bindings, rule_holds_context]
                  apply forall_congr'
                  intro ρ
                  exact imp_congr
                    (mapM_forall_iff _ body typedBody hb _ _
                      (fun a typed accepted => resolveAtom_holds_iff Γ a typed accepted M ρ))
                    (resolveAtom_holds_iff Γ head typedHead hh M ρ)
  | query context goals =>
      cases hc : Context.check D context with
      | none => simp [resolveSentence?, hc] at success
      | some Γ =>
          cases hg : goals.mapM (resolveAtom? Γ) with
          | none => simp [resolveSentence?, hc, hg] at success
          | some typedGoals =>
              simp [resolveSentence?, hc, hg] at success
              subst resolved
              have bindings := context_check_bindings D context Γ hc
              change (RawSentence.query context goals).Holds M ↔
                ∃ ρ, ∀ a ∈ typedGoals, a.Holds M ρ
              rw [← bindings, query_holds_context]
              apply exists_congr
              intro ρ
              exact mapM_forall_iff _ goals typedGoals hg _ _
                (fun a typed accepted => resolveAtom_holds_iff Γ a typed accepted M ρ)

namespace Task
/-- Exact open-context resolver adequacy with independent raw meaning,
discharged below by `termAdequacy_task`. -/
def termAdequacy : Prop :=
  ∀ (D : Declarations) (Γ : CheckedContext D) (raw : RawTerm) (term : PackedTerm Γ),
    resolveTerm? Γ raw = some term →
    ∀ (M : Core.Model D.signature) (ρ : Valuation M Γ) (value : M.carrier term.1),
      raw.Denotes M Γ ρ term.1 value ↔ term.2.eval M.toAlgebra ρ = value

def atomAdequacy : Prop :=
  ∀ (D : Declarations) (Γ : CheckedContext D) (raw : RawAtom)
    (atom : Core.Atom D.signature Γ.profile), resolveAtom? Γ raw = some atom →
    ∀ (M : Core.Model D.signature) (ρ : Valuation M Γ),
      raw.Holds M Γ ρ ↔ atom.Holds M ρ

def sentenceAdequacy : Prop :=
  ∀ (D : Declarations) (raw : RawSentence) (sentence : Core.Sentence D.signature),
    resolveSentence? D raw = some sentence →
    ∀ M : Core.Model D.signature, raw.Holds M ↔ sentence.Holds M
end Task

theorem sentenceAdequacy_task : Task.sentenceAdequacy := by
  intro D raw resolved success M
  exact resolveSentence_holds_iff D raw resolved success M

theorem atomAdequacy_task : Task.atomAdequacy := by
  intro D Γ raw resolved success M ρ
  exact resolveAtom_holds_iff Γ raw resolved success M ρ

theorem termAdequacy_task : Task.termAdequacy := by
  intro D Γ raw resolved success M ρ value
  exact resolveTerm_denotes_iff Γ raw resolved success M ρ value

end Silmaril.Logic.Egglog.Source.Named
