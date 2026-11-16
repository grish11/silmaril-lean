module

public import Silmaril.Proofs.Logic.Smt.Uflia.Quantified.SExpr.Renaming.Mapping
public import Silmaril.Logic.Smt.Uflia.SExpr.Renaming.Lexical.Thms

@[expose] public section
namespace Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
open CategoryTheory Silmaril.Logic.Smt.Uflia.SExpr
variable {E F : Environment} {k : Nat} {Γ : Fin k → SortCode String}

@[simp] theorem freshName_length (index : Nat) : (freshName index).length = index + 1 := by
  simp only [freshName, String.length_ofList, List.length_cons, List.length_replicate]

theorem freshName_injective : Function.Injective freshName := by
  intro i j same
  have lengths := congrArg String.length same
  simpa only [freshName_length, Nat.add_right_cancel_iff] using lengths

private theorem freshName_not (index : Nat) (word : String)
    (head : word.toList.head? ≠ some '$') : freshName index ≠ word := by
  intro same
  apply head
  rw [← same]
  rfl

@[simp] theorem freshName_simple (index : Nat) : simpleSymbol (freshName index) = true := by
  simp [simpleSymbol, freshName, List.all_replicate]
  repeat' constructor
  all_goals simpa [freshName] using freshName_not index _ (by decide)

@[simp] theorem freshName_not_reserved (index : Nat) :
    reserved.contains (freshName index) = false := by
  simp only [reserved, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_false_iff, beq_eq_false_iff_ne]
  repeat' constructor
  all_goals exact freshName_not index _ (by decide)

theorem freshName_legal (index : Nat) : Silmaril.Logic.Smt.SExpr.Writer.LegalAtom (freshName index) :=
  Uflia.SExpr.Renaming.simpleSymbol_legalAtom _ (freshName_simple index)

/-- One entry records exactly the old value retained by source lexical binding,
plus its fresh target spelling. The target value is always the actual typed map. -/
structure Local (E : Environment) {k : Nat} (Γ : Fin k → SortCode String) where
  source : String
  target : String
  value : PackedTerm E Γ

def sourceLocals (locals : List (Local E Γ)) : SExpr.Locals E Γ :=
  locals.map (fun entry => (entry.source, entry.value))
def targetLocals (f : E.signature ⟶ F.signature) (locals : List (Local E Γ)) : SExpr.Locals F Γ :=
  locals.map (fun entry => (entry.target, mapPacked f entry.value))
def localScope (locals : List (Local E Γ)) : Scope :=
  locals.map (fun entry => (entry.source, entry.target))

def selected? : List (Local E Γ) → String → Option (Local E Γ)
  | [], _ => none
  | entry :: rest, name => if entry.source = name then some entry else selected? rest name

@[simp] theorem selected_source (locals : List (Local E Γ)) (name : String) :
    SExpr.local? (sourceLocals locals) name = (selected? locals name).map Local.value := by
  induction locals with
  | nil => rfl
  | cons entry rest ih =>
    simp only [sourceLocals, List.map_cons, SExpr.local?, selected?]
    split
    · rfl
    · simpa only [sourceLocals] using ih

@[simp] theorem selected_name (locals : List (Local E Γ)) (name : String) :
    localName? (localScope locals) name = (selected? locals name).map Local.target := by
  induction locals with
  | nil => rfl
  | cons entry rest ih =>
    simp only [localScope, List.map_cons, localName?, selected?]
    split
    · rfl
    · simpa only [localScope] using ih

theorem selected_mem {locals : List (Local E Γ)} {name : String} {entry : Local E Γ}
    (selected : selected? locals name = some entry) : entry ∈ locals := by
  induction locals with
  | nil => cases selected
  | cons first rest ih =>
    simp only [selected?] at selected
    split at selected
    · cases selected
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih selected)

/-- Target spellings are distinct; fresh binders cannot shadow a mapped global
or a previously allocated target local. Source keys may repeat freely. -/
def ValidScope (F : Environment) (next : Nat) (locals : List (Local E Γ)) : Prop :=
  (locals.map Local.target).Nodup ∧
    (∀ entry ∈ locals, entry.target.length < next + 1) ∧
    (∀ entry ∈ locals, ∀ declaration ∈ F.declarations, entry.target ≠ declaration.name) ∧
    (∀ entry ∈ locals, simpleSymbol entry.target = true ∧ reserved.contains entry.target = false)

theorem target_lookup_of_mem (f : E.signature ⟶ F.signature)
    {locals : List (Local E Γ)} (distinct : (locals.map Local.target).Nodup)
    {entry : Local E Γ} (member : entry ∈ locals) :
    SExpr.local? (targetLocals f locals) entry.target = some (mapPacked f entry.value) := by
  induction locals with
  | nil => cases member
  | cons first rest ih =>
    simp only [List.map_cons, List.nodup_cons] at distinct
    rcases List.mem_cons.mp member with same | member
    · subst entry
      simp [targetLocals, SExpr.local?]
    · have different : first.target ≠ entry.target := by
        intro same
        apply distinct.1
        exact List.mem_map.mpr ⟨entry, member, same.symm⟩
      simp only [targetLocals, List.map_cons, SExpr.local?, different, ↓reduceIte]
      exact ih distinct.2 member

theorem lookup_commute (f : E.signature ⟶ F.signature)
    (locals : List (Local E Γ)) (distinct : (locals.map Local.target).Nodup) (name : String) :
    (localName? (localScope locals) name).bind (SExpr.local? (targetLocals f locals)) =
      (SExpr.local? (sourceLocals locals) name).map (mapPacked f) := by
  rw [selected_name, selected_source]
  cases selected : selected? locals name with
  | none => rfl
  | some entry => exact target_lookup_of_mem f distinct (selected_mem selected)

theorem target_lookup_none (f : E.signature ⟶ F.signature)
    (locals : List (Local E Γ)) (name : String)
    (absent : ∀ entry ∈ locals, entry.target ≠ name) :
    SExpr.local? (targetLocals f locals) name = none := by
  induction locals with
  | nil => rfl
  | cons entry rest ih =>
    simp only [targetLocals, List.map_cons, SExpr.local?, absent entry (by simp), ↓reduceIte]
    apply ih
    intro other member
    exact absent other (List.mem_cons_of_mem _ member)

theorem global_unshadowed (f : NameMap E F) {next : Nat} (locals : List (Local E Γ))
    (valid : ValidScope F next locals) (name : String) (i : Fin E.declarations.length)
    (lookup : lookup? E name = some i) :
    SExpr.local? (targetLocals f.abstract locals) (f.rename name) = none := by
  have targetName := f.targetName name i lookup
  have declaration_mem : F.declarations.get
      (Uflia.SExpr.Renaming.symbolIndex (f.abstract.operations (.declared i))) ∈ F.declarations :=
    List.get_mem _ _
  have absent : ∀ entry ∈ locals, entry.target ≠ f.rename name := by
    intro entry member
    rw [← targetName]
    exact valid.2.2.1 entry member _ declaration_mem
  exact target_lookup_none f.abstract locals (f.rename name) absent

private theorem declaration_le_fold (declarations : List Declaration) (bound : Nat)
    (declaration : Declaration) (member : declaration ∈ declarations) :
    declaration.name.length ≤
      declarations.foldl (fun n d => max n d.name.length) bound := by
  induction declarations generalizing bound with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | member
    · subst declaration
      have monotone : ∀ (ds : List Declaration) (n : Nat),
          n ≤ ds.foldl (fun n d => max n d.name.length) n := by
        intro ds
        induction ds with
        | nil => intro n; exact Nat.le_refl _
        | cons d ds ih =>
          intro n
          exact Nat.le_trans (Nat.le_max_left _ _) (ih _)
      exact Nat.le_trans (Nat.le_max_right _ _) (monotone rest _)
    · exact ih _ member

theorem declaration_lt_firstFresh (F : Environment) (declaration : Declaration)
    (member : declaration ∈ F.declarations) : declaration.name.length < firstFresh F := by
  exact Nat.lt_succ_of_le (declaration_le_fold F.declarations 0 declaration member)

def weakenLocal (sort : SortCode String) (entry : Local E Γ) : Local E (Fin.cases sort Γ) :=
  ⟨entry.source, entry.target, ⟨entry.value.sort, entry.value.term.weaken sort⟩⟩

theorem valid_weaken (F : Environment) (next : Nat) (locals : List (Local E Γ))
    (valid : ValidScope F next locals) (sort : SortCode String) :
    ValidScope F next (locals.map (weakenLocal sort)) := by
  rcases valid with ⟨distinct, short, away, legal⟩
  constructor
  · simpa only [List.map_map, Function.comp_def, weakenLocal] using distinct
  constructor
  · intro entry member
    obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
    subst entry
    exact short old oldMember
  · constructor
    · intro entry member declaration declared
      obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
      subst entry
      exact away old oldMember declaration declared
    · intro entry member
      obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
      subst entry
      exact legal old oldMember

theorem valid_fresh_cons (F : Environment) (next : Nat) (locals : List (Local E Γ))
    (valid : ValidScope F next locals) (bound : firstFresh F ≤ next)
    (name : String) (term : PackedTerm E Γ) :
    ValidScope F (next + 1) (⟨name, freshName next, term⟩ :: locals) := by
  rcases valid with ⟨distinct, short, away, legal⟩
  have fresh : freshName next ∉ locals.map Local.target := by
    intro member
    obtain ⟨entry, member, same⟩ := List.mem_map.mp member
    have shorter := short entry member
    rw [same, freshName_length] at shorter
    exact Nat.lt_irrefl _ shorter
  constructor
  · exact List.nodup_cons.mpr ⟨fresh, distinct⟩
  constructor
  · intro entry member
    rcases List.mem_cons.mp member with same | member
    · subst entry
      simp only [freshName_length]
      omega
    · exact Nat.lt_trans (short entry member) (by omega)
  · constructor
    · intro entry member declaration declared
      rcases List.mem_cons.mp member with same | member
      · subst entry
        intro same
        have shorter := declaration_lt_firstFresh F declaration declared
        have lengths := congrArg String.length same
        simp only [freshName_length] at lengths
        omega
      · exact away entry member declaration declared
    · intro entry member
      rcases List.mem_cons.mp member with same | member
      · subst entry
        exact ⟨freshName_simple next, freshName_not_reserved next⟩
      · exact legal entry member

@[simp] theorem localScope_weaken (sort : SortCode String) (locals : List (Local E Γ)) :
    localScope (locals.map (weakenLocal sort)) = localScope locals := by
  simp only [localScope, List.map_map, Function.comp_def, weakenLocal]

@[simp] theorem sourceLocals_weaken (sort : SortCode String) (locals : List (Local E Γ)) :
    sourceLocals (locals.map (weakenLocal sort)) =
      (sourceLocals locals).map (fun entry =>
        ((entry.1, ⟨entry.2.sort, entry.2.term.weaken sort⟩) : String × PackedTerm E _)) := by
  simp only [sourceLocals, List.map_map, Function.comp_def, weakenLocal]

@[simp] theorem targetLocals_weaken (f : E.signature ⟶ F.signature)
    (sort : SortCode String) (locals : List (Local E Γ)) :
    targetLocals f (locals.map (weakenLocal sort)) =
      (targetLocals f locals).map (fun entry =>
        ((entry.1, ⟨entry.2.sort, entry.2.term.weaken sort⟩) : String × PackedTerm F _)) := by
  simp only [targetLocals, List.map_map, Function.comp_def, weakenLocal, mapPacked,
    Term.map_weaken]

end Silmaril.Logic.Smt.Uflia.Quantified.SExpr.Renaming
