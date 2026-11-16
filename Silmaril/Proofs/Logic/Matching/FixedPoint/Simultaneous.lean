module

public import Silmaril.Logic.Matching.FixedPoint.Simultaneous.Defs

set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Matching.FixedPoint.Simultaneous
universe u v
open Algebraic.ManySorted (Signature)
open Silmaril.Logic.ModalMu
open Silmaril.Logic.ModalMu.FiniteVector (orderMap fixed_conjugate)
variable {S : Type} {A : Signature S}

private theorem cast_heq {α : Sort u} {D : α → Sort v} {a b : α}
    (h : a = b) (x : D a) : HEq (h ▸ x : D b) x := by
  cases h
  rfl

theorem joinEnv_left_heq (M : Model A) {r l : Nat}
    {P : Fin r → S} {Q : Fin l → S} (η : SetEnv A M Q) (X : SetEnv A M P) (i : Fin r) :
    HEq (joinEnv M η X (Fin.castAdd l i)) (X i) := by
  simp only [joinEnv, Fin.addCases_left]
  exact cast_heq (D := fun s => Set (M.carrier s)) (append_left P Q i).symm (X i)

theorem joinEnv_right_heq (M : Model A) {r l : Nat}
    {P : Fin r → S} {Q : Fin l → S} (η : SetEnv A M Q) (X : SetEnv A M P) (i : Fin l) :
    HEq (joinEnv M η X (Fin.natAdd r i)) (η i) := by
  simp only [joinEnv, Fin.addCases_right]
  exact cast_heq (D := fun s => Set (M.carrier s)) (append_right P Q i).symm (η i)

private theorem pull_heq {D : S → Type} {r l : Nat} {P : Fin r → S} {Q : Fin l → S}
    (ρ : Ren P Q) (η : ∀ i, D (Q i)) (i : Fin r) :
    HEq (Ren.pull D η ρ i) (η (ρ i).val) :=
  cast_heq _ _

private theorem denote_sort_cast_heq (M : Model A) {r k : Nat}
    {P : Fin r → S} {Γ : Fin k → S} {s t : S} (h : s = t)
    (p : Pattern A P Γ s) (v : ObjEnv A M Γ) (η : SetEnv A M P) :
    HEq ((h ▸ p : Pattern A P Γ t).denote M v η) (p.denote M v η) := by
  cases h
  rfl

private theorem tailRen_head_val {r l : Nat} (P : Fin (r+1) → S) (Q : Fin l → S) :
    (tailRen P Q (Fin.castAdd l 0)).val = Fin.natAdd r 0 := by
  unfold tailRen
  rw [Fin.addCases_left]
  rfl

private theorem tailRen_tail_val {r l : Nat} (P : Fin (r+1) → S) (Q : Fin l → S)
    (i : Fin r) :
    (tailRen P Q (Fin.castAdd l i.succ)).val = Fin.castAdd (l+1) i := by
  unfold tailRen
  rw [Fin.addCases_left]
  rfl

private theorem tailRen_outer_val {r l : Nat} (P : Fin (r+1) → S) (Q : Fin l → S)
    (i : Fin l) :
    (tailRen P Q (Fin.natAdd (r+1) i)).val = Fin.natAdd r i.succ := by
  unfold tailRen
  rw [Fin.addCases_right]

theorem System.tail_operator {r l k : Nat} {P : Fin (r+1) → S}
    {Q : Fin l → S} {Γ : Fin k → S} (s : System A P Q Γ)
    (M : Model A) (v : ObjEnv A M Γ) (η : SetEnv A M Q)
    (X : Set (M.carrier (P 0))) (Y : SetEnv A M (P ∘ Fin.succ)) :
    s.tail.operator M v (Fin.cases X η) Y =
      fun i : Fin r => s.operator M v η (Fin.cases X Y) i.succ := by
  funext i
  change ((s.body i.succ).renameSets _).denote M v _ = _
  rw [Pattern.denote_renameSets]
  let outerSorts : Fin (l+1) → S :=
    @Fin.cases l (fun _ : Fin (l+1) => S) (P 0) Q
  let outer : SetEnv A M outerSorts :=
    @Fin.cases l (fun j => Set (M.carrier (outerSorts j))) X η
  let source : SetEnv A M P :=
    @Fin.cases r (fun j => Set (M.carrier (P j))) X Y
  apply congrArg (fun ζ => (s.body i.succ).denote M v ζ)
  funext j
  change Ren.pull (fun s => Set (M.carrier s))
    (joinEnv M outer Y) (tailRen P Q) j = joinEnv M η source j
  apply eq_of_heq
  refine Fin.addCases ?_ ?_ j
  · intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · have h := pull_heq (D := fun s => Set (M.carrier s))
        (tailRen P Q) (joinEnv M outer Y) (Fin.castAdd l 0)
      rw [tailRen_head_val] at h
      have ht : HEq (joinEnv M outer Y (Fin.natAdd r 0)) X :=
        (joinEnv_right_heq M (P := P ∘ Fin.succ)
          (Q := Fin.cases (P 0) Q) outer Y 0).trans
            (heq_of_eq (show outer 0 = X from rfl))
      have hs : HEq (joinEnv M η source (Fin.castAdd l 0)) X :=
        (joinEnv_left_heq M (P := P) (Q := Q) η source 0).trans
          (heq_of_eq (show source 0 = X from rfl))
      exact h.trans (ht.trans hs.symm)
    · have h := pull_heq (D := fun s => Set (M.carrier s))
        (tailRen P Q) (joinEnv M outer Y) (Fin.castAdd l i.succ)
      rw [tailRen_tail_val] at h
      have ht : HEq (joinEnv M outer Y (Fin.castAdd (l+1) i)) (Y i) :=
        joinEnv_left_heq M (P := P ∘ Fin.succ)
          (Q := Fin.cases (P 0) Q) outer Y i
      have hs : HEq (joinEnv M η source (Fin.castAdd l i.succ)) (Y i) :=
        (joinEnv_left_heq M (P := P) (Q := Q) η source i.succ).trans
          (heq_of_eq (show source i.succ = Y i from rfl))
      exact h.trans (ht.trans hs.symm)
  · intro j
    have h := pull_heq (D := fun s => Set (M.carrier s))
      (tailRen P Q) (joinEnv M outer Y) (Fin.natAdd (r+1) j)
    rw [tailRen_outer_val] at h
    have ht : HEq (joinEnv M outer Y (Fin.natAdd r j.succ)) (η j) :=
      (joinEnv_right_heq M (P := P ∘ Fin.succ)
        (Q := Fin.cases (P 0) Q) outer Y j.succ).trans
          (heq_of_eq (show outer j.succ = η j from rfl))
    have hs : HEq (joinEnv M η source (Fin.natAdd (r+1) j)) (η j) :=
      joinEnv_right_heq M (P := P) (Q := Q) η source j
    exact h.trans (ht.trans hs.symm)

/-- The denotation of every compiled scalar component is the corresponding
component of the independently defined simultaneous least fixed point.
No inhabitance assumption on any generated subset is used. -/
theorem System.compile_correct :
    ∀ {r l k : Nat} {P : Fin r → S} {Q : Fin l → S} {Γ : Fin k → S}
      (s : System A P Q Γ) (M : Model A) (v : ObjEnv A M Γ) (η : SetEnv A M Q),
      (fun i => (s.compile i).denote M v η) = s.denote M v η := by
  intro r
  induction r with
  | zero => intro l k P Q Γ s M v η; funext i; exact i.elim0
  | succ r ih =>
      intro l k P Q Γ s M v η
      let e := splitEnv M P
      let f := s.operator M v η
      let g := (orderMap e).comp (f.comp (orderMap e.symm))
      let tail := s.tail.compile
      have tail_sem (X : Set (M.carrier (P 0))) :
          (fun i => (tail i).denote M v (Fin.cases X η)) =
            Vector.secondSolutions false g X := by
        rw [ih]
        change (s.tail.operator M v (Fin.cases X η)).lfp = (Vector.secondAt g X).lfp
        apply congrArg OrderHom.lfp
        apply OrderHom.ext
        funext Y
        exact s.tail_operator M v η X Y
      let head : Pattern A Q Γ (P 0) :=
        Pattern.mu (P' := Fin.cases (P 0) Q)
          ((s.body 0).substituteSets (Q := Fin.cases (P 0) Q) (headSub tail))
      have head_sem : head.denote M v η = (Vector.reduced false g).lfp := by
        change (((s.body 0).substituteSets (headSub tail)).denote M v |>.comp
          (insert A M η)).lfp = _
        apply congrArg OrderHom.lfp
        apply OrderHom.ext
        funext X
        change ((s.body 0).substituteSets _).denote M v (Fin.cases X η) = _
        rw [Pattern.denote_substituteSets]
        change (s.body 0).denote M v _ = (s.body 0).denote M v _
        apply congrArg (fun ζ => (s.body 0).denote M v ζ)
        funext j
        refine Fin.addCases ?_ ?_ j
        · intro j
          refine Fin.cases ?_ (fun i => ?_) j
          · apply eq_of_heq
            simp only [headSub, Fin.addCases_left, Fin.cases_zero]
            exact (denote_sort_cast_heq M (append_left P Q 0).symm
              (.setvar 0 : Pattern A (Fin.cases (P 0) Q) Γ (P 0))
              v (Fin.cases X η)).trans
              (joinEnv_left_heq M η
                (e.symm (X, Vector.secondSolutions false g X)) 0).symm
          · apply eq_of_heq
            simp only [headSub, Fin.addCases_left, Fin.cases_succ]
            exact (denote_sort_cast_heq M (append_left P Q i.succ).symm
              (tail i) v (Fin.cases X η)).trans
              ((heq_of_eq (congrFun (tail_sem X) i)).trans
                (joinEnv_left_heq M η
                  (e.symm (X, Vector.secondSolutions false g X)) i.succ).symm)
        · intro j
          apply eq_of_heq
          simp only [headSub, Fin.addCases_right]
          exact (denote_sort_cast_heq M (append_right P Q j).symm
            (.setvar j.succ : Pattern A (Fin.cases (P 0) Q) Γ (Q j))
            v (Fin.cases X η)).trans
            (joinEnv_right_heq M η
              (e.symm (X, Vector.secondSolutions false g X)) j).symm
      have output_sem :
          e (fun i => (s.compile i).denote M v η) =
            ((Vector.reduced false g).lfp,
              Vector.secondSolutions false g (Vector.reduced false g).lfp) := by
        apply Prod.ext
        · exact head_sem
        · change (fun i =>
            ((tail i).substituteSets (Fin.cases head Pattern.setvar)).denote M v η) = _
          have inst :
              (fun i => ((tail i).substituteSets
                (Fin.cases head Pattern.setvar)).denote M v η) =
              fun i => (tail i).denote M v (Fin.cases (head.denote M v η) η) := by
            funext i
            rw [Pattern.denote_substituteSets]
            apply congrArg (fun ζ => (tail i).denote M v ζ)
            funext j
            exact Fin.cases rfl (fun _ => rfl) j
          rw [inst, tail_sem, head_sem]
      apply e.injective
      rw [output_sem, ← Vector.bekic_lfp]
      exact (fixed_conjugate e f false).symm

end Silmaril.Logic.Matching.FixedPoint.Simultaneous
