module

public import Silmaril.Logic.Separation.Thms
public import Silmaril.Logic.Institution.Examples.FirstOrder

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Separation.FirstOrder
open CategoryTheory Silmaril.Logic.Institution.Examples

/-- Disjoint union of optional values, independently of their value type. -/
def SlotJoin {V : Type} (a b c : Option V) : Prop :=
  (a = none ∧ b = c) ∨ (b = none ∧ a = c)

abbrev Store (V : Type) := Nat → Option V

def empty {V : Type} : Store V := fun _ => none

def Join {V : Type} (a b c : Store V) : Prop := ∀ n, SlotJoin (a n) (b n) (c n)

def merge {V : Type} (a b : Store V) : Store V := fun n => (a n).or (b n)

theorem slot_functional {V : Type} {a b c d : Option V}
    (h : SlotJoin a b c) (h' : SlotJoin a b d) : c = d := by
  rcases h with ⟨ha,hb⟩ | ⟨hb,ha⟩ <;>
    rcases h' with ⟨ha',hb'⟩ | ⟨hb',ha'⟩ <;> simp_all

theorem slot_merge {V : Type} {a b c : Option V} (h : SlotJoin a b c) :
    a.or b = c := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem slot_assoc {V : Type} {a b c d ab : Option V}
    (h : SlotJoin a b ab) (h' : SlotJoin ab c d) :
    SlotJoin b c (b.or c) ∧ SlotJoin a (b.or c) d := by
  cases a <;> cases b <;> cases c <;> cases ab <;>
    simp_all [SlotJoin]

/-- All partial stores, including the empty store even if `V` is empty. -/
def resource (V : Type) : Resource where
  carrier := Store V
  unit := empty
  join := Join
  functional h h' := funext fun n => slot_functional (h n) (h' n)
  unit_join a b := by
    constructor
    · intro h
      funext n
      rcases h n with ⟨_,he⟩ | ⟨ha,hb⟩
      · exact he
      · exact ha.trans hb
    · rintro rfl
      exact fun _ => Or.inl ⟨rfl,rfl⟩
  comm a b c := by
    unfold Join SlotJoin
    exact forall_congr' fun _ => or_comm
  assoc a b c d := by
    constructor
    · rintro ⟨ab, hab, hcd⟩
      exact ⟨merge b c, fun n => (slot_assoc (hab n) (hcd n)).1,
        fun n => (slot_assoc (hab n) (hcd n)).2⟩
    · rintro ⟨bc, hbc, had⟩
      have swap : ∀ {x y z : Store V}, Join x y z → Join y x z :=
        fun h n => (h n).elim Or.inr Or.inl
      obtain ⟨ba, hba, hcd⟩ :=
        (show ∃ ba, Join b a ba ∧ Join c ba d from
          ⟨merge b a, fun n => (slot_assoc ((swap hbc) n) ((swap had) n)).1,
            fun n => (slot_assoc ((swap hbc) n) ((swap had) n)).2⟩)
      exact ⟨ba, swap hba, swap hcd⟩

abbrev Value {A : FOL.Signature} (M : FOL.Structure A) := Sigma M.carrier
abbrev ModelStore {A : FOL.Signature} (M : FOL.Structure A) := Store (Value M)

/-- Position zero is newest; extending the context preserves all old slots. -/
def slot {k : Nat} (i : Fin k) : Nat := k - 1 - i.val

/-- Primitive vocabulary only: owned cells and actual first-order atomic terms. -/
inductive Atom (A : FOL.Signature) where
  | cell (n : Nat) (s : A.S)
  | eq {k} (Γ : Fin k → A.S) {s} (t u : EQ.Term A.toSignature Γ s)
  | rel {k} (Γ : Fin k → A.S) {n w} (r : A.Rel n w)
      (args : ∀ j, EQ.Term A.toSignature Γ (w j))

abbrev signature (A : FOL.Signature) : Separation.Signature := ⟨Atom A⟩

def singleton {V : Type} (n : Nat) (x : V) : Store V :=
  fun m => if m = n then some x else none

def Encodes {A : FOL.Signature} (M : FOL.Structure A) {k} (Γ : Fin k → A.S)
    (ρ : ∀ i, M.carrier (Γ i)) (h : ModelStore M) : Prop :=
  ∀ i, h (slot i) = some ⟨Γ i, ρ i⟩

/-- Atomic observations ignore unrelated slots; cells own exactly one slot. -/
def atom {A : FOL.Signature} (M : FOL.Structure A) : Atom A → Set (ModelStore M)
  | .cell n s => {h | ∃ x : M.carrier s, h = singleton n ⟨s,x⟩}
  | .eq Γ t u => {h | ∃ ρ, Encodes M Γ ρ h ∧ t.eval M.toAlgebra ρ = u.eval M.toAlgebra ρ}
  | .rel Γ r args => {h | ∃ ρ, Encodes M Γ ρ h ∧ M.rel r (fun j => (args j).eval M.toAlgebra ρ)}

def native {A : FOL.Signature} (M : FOL.Structure A) : Separation.Model (signature A) :=
  ⟨resource (Value M), atom M⟩

/-- Exact finite domain, not just presence of context values. -/
def store {A : FOL.Signature} (M : FOL.Structure A) {k} (Γ : Fin k → A.S) (ρ : ∀ i, M.carrier (Γ i)) : ModelStore M :=
  fun n => if hn : n < k then
    let i : Fin k := ⟨k - 1 - n, by omega⟩
    some ⟨Γ i, ρ i⟩
  else none

/-- An extension exists for every value, without requiring a nonempty sort. -/
def extend {A : FOL.Signature} (M : FOL.Structure A) {k} {Γ : Fin k → A.S} {Δ : Fin (k+1) → A.S}
    (hc : Δ ∘ Fin.succ = Γ) (ρ : ∀ i, M.carrier (Γ i)) (x : M.carrier (Δ 0)) :
    ∀ i, M.carrier (Δ i) :=
  Fin.cases x (fun i => (congrArg M.carrier (congrFun hc i).symm) ▸ ρ i)


variable {A : FOL.Signature}

def truth : Assertion (signature A) := .neg (.conj .emp (.neg .emp))

/-- Binders use independent native wand, allocating the next owned slot. -/
def compile : {k : Nat} → {Γ : Fin k → A.S} → FOL.Formula A Γ → Assertion (signature A)
  | _, _, .eq t u => .atom (.eq _ t u)
  | _, _, .rel r args => .atom (.rel _ r args)
  | _, _, .tt => truth
  | _, _, .not φ => .neg (compile φ)
  | _, _, .and φ ψ => .conj (compile φ) (compile ψ)
  | k, _, .all (Δ := Δ) _ φ => .wand (.atom (.cell k (Δ 0))) (compile φ)

/-- Closed formulas assert an entailment from emp, evaluated at all native stores. -/
def sentence (φ : FOL.Sentence A) : BaseSentence (signature A) :=
  ⟨.emp, compile φ.formula⟩


end Silmaril.Logic.Separation.FirstOrder
