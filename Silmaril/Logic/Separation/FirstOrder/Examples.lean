module

public import Silmaril.Logic.Separation.FirstOrder.Institution

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Logic.Separation.FirstOrder.Examples
open CategoryTheory Silmaril.Logic.Institution.Examples

/-- A genuinely empty symbol vocabulary; no source truth is supplied to the target. -/
def pure : FixedSignature Unit := ⟨fun _ _ _ => PEmpty, fun _ _ => PEmpty⟩

def pureModel (X : Type) : FOL.Structure pure.fol where
  carrier := fun _ => X
  op o := PEmpty.elim o
  rel r := PEmpty.elim r

def ctx (k : Nat) : Fin k → Unit := fun _ => ()

/-- ∀ x, ∃ y, y ≠ x, using only the actual public formula constructors. -/
def different : FOL.Sentence pure.fol :=
  ⟨ctx 0, .all (Δ := ctx 1) rfl (.not (.all (Δ := ctx 2) rfl (.not (.not (.eq (.var 0) (.var 1))))))⟩

/-- ∀ x, ∀ y, x = y. -/
def collapse : FOL.Sentence pure.fol :=
  ⟨ctx 0, .all (Δ := ctx 1) rfl (.all (Δ := ctx 2) rfl (.eq (.var 0) (.var 1)))⟩

theorem bool_different : different.Holds (pureModel Bool) := by
  intro ρ _ h
  have hn := h (Fin.cases (!(ρ 0)) ρ) (fun _ => HEq.rfl)
  apply hn
  change ¬ ((!(ρ 0)) = ρ 0)
  cases ρ 0 <;> decide

theorem unit_not_different : ¬ different.Holds (pureModel Unit) := by
  intro h
  apply h (fun _ => ()) (fun i => i.elim0)
  intro σ _ hn
  exact hn (show (σ 0 : Unit) = (σ 1 : Unit) from Unit.ext _ _)

theorem empty_different : different.Holds (pureModel Empty) := by
  intro ρ _
  exact (ρ 0).elim

theorem bool_not_collapse : ¬ collapse.Holds (pureModel Bool) := by
  intro h
  have he := h (fun _ => false) (fun i => i.elim0)
    (Fin.cases true (fun _ => false)) (fun _ => HEq.rfl)
  exact Bool.noConfusion he

theorem bool_native_different : (sentence different).Satisfies (native (pureModel Bool)) :=
  (sentence_correct _ _).2 bool_different

theorem unit_native_not_different : ¬ (sentence different).Satisfies (native (pureModel Unit)) :=
  fun h => unit_not_different ((sentence_correct _ _).1 h)

theorem empty_native_different : (sentence different).Satisfies (native (pureModel Empty)) :=
  (sentence_correct _ _).2 empty_different

theorem bool_native_not_collapse : ¬ (sentence collapse).Satisfies (native (pureModel Bool)) :=
  fun h => bool_not_collapse ((sentence_correct _ _).1 h)

/-- Concrete malformed binder translation: both binders reuse slot zero. -/
def duplicated : Assertion (signature pure.fol) :=
  .wand (.atom (.cell 0 ()))
    (.wand (.atom (.cell 0 ())) (.atom (.eq (ctx 2) (.var 0) (.var 1))))

theorem duplicate_slot_join_impossible {V : Type} (x y : V) (h : Store V) :
    ¬ Join (singleton 0 x) (singleton 0 y) h := by
  intro hj
  have hn := hj 0
  simp [SlotJoin, singleton] at hn

/-- Native proof independent of compiler correctness: the second wand is vacuous. -/
theorem duplicated_native_true :
    (⟨.emp, duplicated⟩ : BaseSentence (signature pure.fol)).Satisfies (native (pureModel Bool)) := by
  intro h hh
  have he : h = empty := hh
  subst h
  intro a b hj ha
  obtain ⟨x,rfl⟩ := ha
  have hb := ((resource (Value (pureModel Bool))).unit_join _ _).1 hj
  subst b
  intro c d hcd hc
  obtain ⟨y,rfl⟩ := hc
  exact (duplicate_slot_join_impossible _ _ _ hcd).elim

/-- Explicit two-cell ownership witness for disjoint slots. -/
theorem two_cells :
    merge (singleton 0 (⟨(),false⟩ : Value (pureModel Bool))) (singleton 1 ⟨(),true⟩) ∈
      (Assertion.sep (A := signature pure.fol) (.atom (Atom.cell 0 ())) (.atom (Atom.cell 1 ()))).denote (native (pureModel Bool)) := by
  refine ⟨singleton 0 ⟨(),false⟩, singleton 1 ⟨(),true⟩, ?_, ⟨false,rfl⟩, ⟨true,rfl⟩⟩
  intro n
  by_cases h0 : n = 0
  · subst n; exact Or.inr ⟨by simp [singleton], by simp [merge, singleton]⟩
  · exact Or.inl ⟨by simp [singleton, h0], by simp [merge, singleton, h0]⟩

theorem same_slot_sep_empty :
    (Assertion.sep (A := signature pure.fol) (.atom (Atom.cell 0 ()))
      (.atom (Atom.cell 0 ()))).denote (native (pureModel Bool)) = ∅ := by
  apply Set.ext
  intro h
  constructor
  · rintro ⟨a,b,hj,⟨x,rfl⟩,⟨y,rfl⟩⟩
    exact duplicate_slot_join_impossible _ _ _ hj
  · exact False.elim

/-- An actual two-value counterstore, independent of the formula compiler. -/
theorem concrete_equality_failure :
    store (pureModel Bool) (ctx 2) (Fin.cases true (fun _ => false)) ∉
      atom (pureModel Bool) (.eq (ctx 2) (.var 0) (.var 1)) := by
  rintro ⟨σ,hh,he⟩
  have hs := encodes_unique (pureModel Bool) (ctx 2) (Fin.cases true (fun _ => false)) σ hh
  subst σ
  exact Bool.noConfusion he

/-- Actual noninjective model homomorphism, retained by the native realization. -/
def squash : FOL.Structure.Hom (pureModel Bool) (pureModel Unit) where
  map _ _ := ()
  map_op o := PEmpty.elim o
  map_rel r := PEmpty.elim r

theorem squash_not_injective : ¬ Function.Injective (squash.map ()) := by
  intro h
  exact Bool.noConfusion (h (show squash.map () false = squash.map () true from rfl))

theorem squash_cells (n : Nat) (b : Bool) :
    (nativeHom squash).map (singleton n ⟨(),b⟩) ∈ atom (pureModel Unit) (.cell n ()) :=
  ⟨(), mapStore_singleton squash n ⟨(),b⟩⟩

def allFalse : FOL.Sentence pure.fol := ⟨ctx 0, .all (Δ := ctx 1) rfl (.not .tt)⟩
def existsTrue : FOL.Sentence pure.fol := ⟨ctx 0, .not (.all (Δ := ctx 1) rfl (.not .tt))⟩

theorem empty_allFalse : allFalse.Holds (pureModel Empty) := by
  intro ρ _; exact (ρ 0).elim

theorem empty_not_existsTrue : ¬ existsTrue.Holds (pureModel Empty) := by
  intro h; exact h empty_allFalse

theorem empty_cell (n : Nat) : atom (pureModel Empty) (.cell n ()) = ∅ := by
  apply Set.ext
  intro h
  constructor
  · rintro ⟨x,_⟩; exact x.elim
  · exact False.elim

/-- Valid FOL reflexivity, used to delimit unrestricted native targets. -/
def reflexive : FOL.Sentence pure.fol := ⟨ctx 0, .all (Δ := ctx 1) rfl (.eq (.var 0) (.var 0))⟩

theorem reflexive_valid (X : Type) : reflexive.Holds (pureModel X) := by
  intro _ _; rfl

/-- A genuine native model, excluded by the canonical atomic interpretation. -/
def badNative : Separation.Model (signature pure.fol) where
  resource := ⟨Unit, (), fun _ _ _ => True, fun _ _ => Subsingleton.elim _ _,
    fun _ _ => ⟨fun _ => Subsingleton.elim _ _, fun _ => trivial⟩,
    fun _ _ _ => Iff.rfl,
    fun _ _ _ _ => ⟨fun _ => ⟨(),trivial,trivial⟩, fun _ => ⟨(),trivial,trivial⟩⟩⟩
  atom a := match a with
    | .cell _ _ => Set.univ
    | _ => ∅

theorem unrestricted_reflexive_failure : ¬ (sentence reflexive).Satisfies badNative := by
  intro h
  have hw := h (show () ∈ (Assertion.emp : Assertion (signature pure.fol)).denote badNative from rfl)
  exact hw () () trivial trivial

end Silmaril.Logic.Separation.FirstOrder.Examples
