module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable.Bisimulation.Defs
public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.ClassTables

/-! # Table morphisms and equal streams identify entered loops -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity (Eqv Step)
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature)
open Paper.TypeCategory (ofType ofRegion iterate sumIso ofRegion_id iterate_uniformity_ofBranchValue)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit)
open SingletonPhases (system)

local notation "S" => system (Φ := signature.Instr) State
local notation "N" => Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "π" => Paper.Extension.Singleton.projection (Step (τ := Ty Empty) (Φ := signature.Instr) false)

set_option backward.isDefEq.respectTransparency false

variable {K : Nat}

/-! ## Front and tail indices -/

theorem joinIdx_front {α : Type} : ∀ (P : Nat) (a : Fin (P + 1) → α) (b : Fin (K + 1) → α) (i : Fin (P + 1)),
    joinIdx P a b (frontIdx P i) = a i
  | 0, a, _, i => by
    have i0 : i = 0 := Fin.eq_zero i
    subst i0
    rfl
  | P + 1, a, b, i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · exact joinIdx_front P (fun i => a i.succ) b i

theorem joinIdx_tail {α : Type} : ∀ (P : Nat) (a : Fin (P + 1) → α) (b : Fin (K + 1) → α) (j : Fin (K + 1)),
    joinIdx P a b (tailIdx P j) = b j
  | 0, _, _, _ => rfl
  | P + 1, a, b, j => joinIdx_tail P (fun i => a i.succ) b j

theorem idx_cases : ∀ (P : Nat) (x : Fin (K + (P + 1) + 1)),
    (∃ i, x = frontIdx P i) ∨ (∃ j, x = tailIdx P j)
  | 0, x => Fin.cases (.inl ⟨0, rfl⟩) (fun j => .inr ⟨j, rfl⟩) x
  | P + 1, x => Fin.cases (.inl ⟨0, rfl⟩)
      (fun x' => (idx_cases P x').elim (fun ⟨i, h⟩ => .inl ⟨i.succ, congrArg Fin.succ h⟩)
        (fun ⟨j, h⟩ => .inr ⟨j, congrArg Fin.succ h⟩)) x

theorem append_prog_front {P : Nat} (t : Table P) (s : Table K) (i : Fin (P + 1)) :
    (t.append s).prog (frontIdx P i) = t.prog i :=
  joinIdx_front P t.prog s.prog i

theorem append_prog_tail {P : Nat} (t : Table P) (s : Table K) (j : Fin (K + 1)) :
    (t.append s).prog (tailIdx P j) = s.prog j :=
  joinIdx_tail P t.prog s.prog j

theorem append_next_front {P : Nat} (t : Table P) (s : Table K) (i : Fin (P + 1)) :
    (t.append s).next (frontIdx P i) = frontIdx P (t.next i) :=
  joinIdx_front P (fun i => frontIdx P (t.next i)) (fun j => tailIdx P (s.next j)) i

theorem append_next_tail {P : Nat} (t : Table P) (s : Table K) (j : Fin (K + 1)) :
    (t.append s).next (tailIdx P j) = tailIdx P (s.next j) :=
  joinIdx_tail P (fun i => frontIdx P (t.next i)) (fun j => tailIdx P (s.next j)) j

/-! ## The tail embedding -/

/-- The tail embedding, an arrow of default Paper given by constructors. -/
noncomputable abbrev tailArr (K P : Nat) :
    ofType (Φ := signature.Instr) (States K) ⟶ ofType (States (K + (P + 1))) :=
  ofRegion (tail_typed K P)

theorem tailArr_zero (K : Nat) : tailArr K 0 = (S).inr K :=
  (br_inr (.var rfl)).trans ((congrArg (· ≫ (S).inr K) (ofRegion_id (States K))).trans (Category.id_comp _))

theorem tailArr_succ (K P : Nat) : tailArr K (P + 1) = tailArr K P ≫ (S).inr (K + (P + 1)) :=
  br_inr (tailTm_typed (.var rfl) P)

theorem inj_tail : ∀ (P : Nat) (j : Fin (K + 1)), injArr K j ≫ tailArr K P = injArr (K + (P + 1)) (tailIdx P j)
  | 0, j => (congrArg (injArr K j ≫ ·) (tailArr_zero K)).trans (injArr_succ K j).symm
  | P + 1, j => (congrArg (injArr K j ≫ ·) (tailArr_succ K P)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (S).inr (K + (P + 1))) (inj_tail P j)).trans
          (injArr_succ (K + (P + 1)) (tailIdx P j)).symm))

/-- A state map that sends state `i` to state `cls i`, preserves the row
programs and commutes with the successors is a simulation. -/
theorem map_square {K' : Nat} (t : Table K) (t' : Table K')
    (f : ofType (Φ := signature.Instr) (States K) ⟶ ofType (States K')) (cls : Fin (K + 1) → Fin (K' + 1))
    (spec : ∀ i, injArr K i ≫ f = injArr K' (cls i))
    (hprog : ∀ i, t.prog i = t'.prog (cls i)) (hnext : ∀ i, cls (t.next i) = t'.next (cls i)) :
    (ofRegion t.step_typed ≫ (sumIso (Φ := signature.Instr) Bit (States K)).hom) ≫ coprod.map (𝟙 _) f =
      f ≫ (ofRegion t'.step_typed ≫ (sumIso (Φ := signature.Instr) Bit (States K')).hom) := by
  apply inj_ext K
  intro i
  have rows : injArr K i ≫ ofRegion t.step_typed = ofRegion (row_typed K (t.prog i) (t.next i)) :=
    inj_dispatch K (fun i => row_typed K (t.prog i) (t.next i)) i
  have rows' : injArr K' (cls i) ≫ ofRegion t'.step_typed =
      ofRegion (row_typed K' (t'.prog (cls i)) (t'.next (cls i))) :=
    inj_dispatch K' (fun i => row_typed K' (t'.prog i) (t'.next i)) (cls i)
  have row := row_class f (t'.prog (cls i)) (t.next i) (t'.next (cls i))
    ((spec (t.next i)).trans (congrArg (injArr K') (hnext i)))
  rw [hprog i] at rows
  exact glue _ _ _ _ _ _ _ _ _ _ rows rows' (spec i) row

/-- A table that sits at the tail of another one, closed under successors,
has the same entered loops. The states in front are arbitrary. This is an
equation of default Paper: the embedding is constructor-valued. -/
theorem tail_arrow {P : Nat} (w : Table (K + (P + 1))) (s : Table K)
    (hprog : ∀ j, s.prog j = w.prog (tailIdx P j)) (hnext : ∀ j, tailIdx P (s.next j) = w.next (tailIdx P j))
    (j : Fin (K + 1)) :
    ofRegion (s.entered_typed j) = ofRegion (w.entered_typed (tailIdx P j)) := by
  have uni := iterate_uniformity_ofBranchValue (tailTm_typed (K := K) (.var (i := 0) rfl) P) _ _
    (map_square s w (tailArr K P) (tailIdx P) (inj_tail P) hprog hnext)
  rw [entered_arrow s j, entered_arrow w (tailIdx P j), loop_arrow s, loop_arrow w]
  exact (congrArg (injArr K j ≫ ·) uni).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ Paper.TypeCategory.iterate _) (inj_tail P j)))

theorem tail_eqv {P : Nat} (w : Table (K + (P + 1))) (s : Table K)
    (hprog : ∀ j, s.prog j = w.prog (tailIdx P j)) (hnext : ∀ j, tailIdx P (s.next j) = w.next (tailIdx P j))
    (j : Fin (K + 1)) :
    Eqv false [State] (s.entered j) (w.entered (tailIdx P j)) [Bit] :=
  (Paper.Extension.Singleton.ofRegion_eq_iff N (s.entered_typed j) (w.entered_typed (tailIdx P j))).1
    (congrArg (π).map (tail_arrow w s hprog hnext j))

/-! ## Morphisms -/

/-- Any map of states that preserves row programs and commutes with
successors identifies the entered loops. It need not be surjective. -/
theorem morphism_eqv {P : Nat} (s : Table K) (t : Table P) (ρ : Fin (K + 1) → Fin (P + 1))
    (hprog : ∀ j, s.prog j = t.prog (ρ j)) (hnext : ∀ j, ρ (s.next j) = t.next (ρ j)) (j : Fin (K + 1)) :
    Eqv false [State] (s.entered j) (t.entered (ρ j)) [Bit] := by
  have tail := tail_eqv (t.append s) s (fun j => (append_prog_tail t s j).symm)
    (fun j => (append_next_tail t s j).symm) j
  have cprog : ∀ x, (t.append s).prog x = t.prog (joinIdx P id ρ x) := by
    intro x
    rcases idx_cases P x with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact (append_prog_front t s i).trans (congrArg t.prog (joinIdx_front P id ρ i)).symm
    · exact (append_prog_tail t s j).trans
        ((hprog j).trans (congrArg t.prog (joinIdx_tail P id ρ j)).symm)
  have cnext : ∀ x, joinIdx P id ρ ((t.append s).next x) = t.next (joinIdx P id ρ x) := by
    intro x
    rcases idx_cases P x with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact (congrArg (joinIdx P id ρ) (append_next_front t s i)).trans
        ((joinIdx_front P id ρ (t.next i)).trans (congrArg t.next (joinIdx_front P id ρ i)).symm)
    · exact (congrArg (joinIdx P id ρ) (append_next_tail t s j)).trans
        ((joinIdx_tail P id ρ (s.next j)).trans
          ((hnext j).trans (congrArg t.next (joinIdx_tail P id ρ j)).symm))
  have quot := quotient_eqv (t.append s) t (joinIdx P id ρ)
    (fun i => ⟨frontIdx P i, joinIdx_front P id ρ i⟩) cprog cnext (tailIdx P j)
  exact tail.trans (joinIdx_tail P id ρ j ▸ quot)

/-! ## Equal streams -/

theorem rep_stream (t : Table K) (x : Fin (K + 1)) (n : Nat) : t.stream (t.rep x) n = t.stream x n := by
  have h : t.streamSetoid.r (t.rep x) x := Quotient.exact (Quotient.out_eq (Quotient.mk t.streamSetoid x))
  exact h n

theorem rep_congr (t : Table K) {x y : Fin (K + 1)} (h : ∀ n, t.stream x n = t.stream y n) :
    t.rep x = t.rep y :=
  congrArg Quotient.out (Quotient.sound (s := t.streamSetoid) h)

/-- Two states of one table with equal streams have equal entered loops. -/
theorem stream_eqv (t : Table K) (x y : Fin (K + 1)) (h : ∀ n, t.stream x n = t.stream y n) :
    Eqv false [State] (t.entered x) (t.entered y) [Bit] := by
  have hp : ∀ x, t.prog x = t.minimized.prog (t.rep x) := fun x => (rep_stream t x 0).symm
  have hn : ∀ x, t.rep (t.next x) = t.minimized.next (t.rep x) :=
    fun x => rep_congr t (fun n => (rep_stream t x (n + 1)).symm)
  exact (morphism_eqv t t.minimized t.rep hp hn x).trans
    (rep_congr t h ▸ (morphism_eqv t t.minimized t.rep hp hn y).symm)

theorem iterate_tail {P : Nat} (t : Table P) (s : Table K) : ∀ (n : Nat) (j : Fin (K + 1)),
    (t.append s).next^[n] (tailIdx P j) = tailIdx P (s.next^[n] j)
  | 0, _ => rfl
  | n + 1, j => (congrArg (t.append s).next^[n] (append_next_tail t s j)).trans (iterate_tail t s n (s.next j))

theorem iterate_front {P : Nat} (t : Table P) (s : Table K) : ∀ (n : Nat) (i : Fin (P + 1)),
    (t.append s).next^[n] (frontIdx P i) = frontIdx P (t.next^[n] i)
  | 0, _ => rfl
  | n + 1, i => (congrArg (t.append s).next^[n] (append_next_front t s i)).trans (iterate_front t s n (t.next i))

/-- Entries of two tables with equal streams have equal entered loops. -/
theorem bisim_eqv {K₁ K₂ : Nat} (t₁ : Table K₁) (t₂ : Table K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))
    (h : ∀ n, t₁.stream i₁ n = t₂.stream i₂ n) :
    Eqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] := by
  have e₁ := tail_eqv (t₂.append t₁) t₁ (fun j => (append_prog_tail t₂ t₁ j).symm)
    (fun j => (append_next_tail t₂ t₁ j).symm) i₁
  have e₂ := morphism_eqv t₂ (t₂.append t₁) (frontIdx K₂) (fun i => (append_prog_front t₂ t₁ i).symm)
    (fun i => (append_next_front t₂ t₁ i).symm) i₂
  have tail : ∀ n, (t₂.append t₁).stream (tailIdx K₂ i₁) n = t₁.stream i₁ n := fun n =>
    (congrArg (t₂.append t₁).prog (iterate_tail t₂ t₁ n i₁)).trans (append_prog_tail t₂ t₁ _)
  have front : ∀ n, (t₂.append t₁).stream (frontIdx K₂ i₂) n = t₂.stream i₂ n := fun n =>
    (congrArg (t₂.append t₁).prog (iterate_front t₂ t₁ n i₂)).trans (append_prog_front t₂ t₁ _)
  exact e₁.trans ((stream_eqv (t₂.append t₁) _ _ (fun n => (tail n).trans ((h n).trans (front n).symm))).trans
    e₂.symm)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.Tables
