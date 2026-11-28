module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableReflection

/-! # Rows with equal keys, and completeness for tables of polls -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.WithAdministrativeReturns
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity.BitTable
open Paper.WithAdministrativeReturns.WithGuardedTablePacking.BitLoop
open Paper.WithAdministrativeReturns.BitFragment.Recursive (Program)
open Paper.WithCaseBind.BitQuery (signature Trace model modelCoherent Event)
open Paper.WithCaseBind.BitQuery.RequestTree
open Paper.Extension.Singleton (ofRegion ofType projection iterateSum iterateSum_map)
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.Extension.Singleton.Generation (exactCopair_ofRegion)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Kleisli (value instructions)
open _root_.Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Reply.Payload (Bit bit)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.BitLoop

local notation "N" => WithGuardedTablePacking.Step (τ := Ty Empty) (Φ := signature.Instr) false
local notation "Lit" => ofRegion N
local notation "PEqv" => WithGuardedTablePacking.WithPhaseUniformity.Eqv

set_option backward.isDefEq.respectTransparency false

/-! ## Rows with equal keys -/

theorem dispatch_congr {D : Ty Empty} : ∀ (K : Nat) {rows rows' : Fin (K + 1) → Region signature.Instr}
    (h : ∀ i, ValueBranches [State] (rows i) [D]) (h' : ∀ i, ValueBranches [State] (rows' i) [D]),
    (∀ i, Lit (h i) = Lit (h' i)) → Lit (dispatch_typed K h) = Lit (dispatch_typed K h')
  | 0, _, _, _, _, e => e 0
  | K + 1, _, _, h, h', e => by
    have a : Lit (dispatch_typed (K + 1) h) =
        exactCopair N (Lit (h 0)) (Lit (dispatch_typed K fun i => h i.succ)) :=
      (exactCopair_ofRegion N (h 0) (dispatch_typed K fun i => h i.succ)).symm
    have b : Lit (dispatch_typed (K + 1) h') =
        exactCopair N (Lit (h' 0)) (Lit (dispatch_typed K fun i => h' i.succ)) :=
      (exactCopair_ofRegion N (h' 0) (dispatch_typed K fun i => h' i.succ)).symm
    rw [a, b, e 0, dispatch_congr K (fun i => h i.succ) (fun i => h' i.succ) (fun i => e i.succ)]

theorem row_lit (K : Nat) (p : Program) (j : Fin (K + 1)) :
    Lit (row_typed K p j) = stepArrow p ≫ Lit (route_typed K j) :=
  (congrArg (projection N).map (Tables.row_arrow K p j)).trans ((projection N).map_comp _ _)

theorem loop_lit {K : Nat} (t : Table K) : Lit t.loop_typed = iterateSum N (Lit t.step_typed) :=
  ((iterateSum_map N (Paper.TypeCategory.ofRegion t.step_typed)).trans
    (congrArg (projection N).map (Paper.TypeCategory.iterateSum_ofRegion t.step_typed))).symm

theorem entered_lit {K : Nat} (t : Table K) (i : Fin (K + 1)) :
    Lit (t.entered_typed i) = Lit (entry_typed K i) ≫ Lit t.loop_typed :=
  (congrArg (projection N).map
    (Paper.TypeCategory.ofRegion_comp (entry_typed K i) t.loop_typed (t.entered_typed i)).symm).trans
    ((projection N).map_comp _ _)

/-- Two tables with the same wiring whose rows have equal keys are equal
at every entry, already in `WithGuardedTablePacking`. -/
theorem rows_eqv {K : Nat} (t t' : Table K) (hnext : ∀ i, t.next i = t'.next i)
    (hkey : ∀ i, (t.prog i).tree.key = (t'.prog i).tree.key) (i : Fin (K + 1)) :
    WithGuardedTablePacking.Eqv false [State] (t.entered i) (t'.entered i) [Bit] := by
  apply (Paper.Extension.Singleton.ofRegion_eq_iff N (t.entered_typed i) (t'.entered_typed i)).1
  have steps : Lit t.step_typed = Lit t'.step_typed :=
    dispatch_congr K (fun i => row_typed K (t.prog i) (t.next i)) (fun i => row_typed K (t'.prog i) (t'.next i))
      (fun i => by rw [row_lit, row_lit, step_of_key (hkey i), hnext i])
  rw [entered_lit, entered_lit, loop_lit, loop_lit, steps]

theorem canon_key (p : Program) : (canonProgram p).tree.key = p.tree.key := by
  have h : keySetoid.r (canonProgram p) p := Quotient.exact (Quotient.out_eq (Quotient.mk keySetoid p))
  exact h

theorem canon_congr {p q : Program} (h : p.tree.key = q.tree.key) : canonProgram p = canonProgram q :=
  congrArg Quotient.out (Quotient.sound (s := keySetoid) h)

theorem canonical_eqv {K : Nat} (t : Table K) (i : Fin (K + 1)) :
    PEqv false [State] (t.entered i) (t.canonical.entered i) [Bit] :=
  WithGuardedTablePacking.WithPhaseUniformity.ofTablePacking false
    (rows_eqv t t.canonical (fun _ => rfl) (fun i => (canon_key (t.prog i)).symm) i)

/-- Entries of two tables whose streams of row keys agree are equal. -/
theorem key_bisim_eqv {K₁ K₂ : Nat} (t₁ : Table K₁) (t₂ : Table K₂) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))
    (h : ∀ n, (t₁.stream i₁ n).tree.key = (t₂.stream i₂ n).tree.key) :
    PEqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] :=
  (canonical_eqv t₁ i₁).trans
    ((Tables.bisim_eqv t₁.canonical t₂.canonical i₁ i₂ (fun n => canon_congr (h n))).trans
      (canonical_eqv t₂ i₂).symm)

theorem iterate_rel {α β : Type} (R : α → β → Prop) (f : α → α) (g : β → β)
    (h : ∀ x y, R x y → R (f x) (g y)) : ∀ (n : Nat) (x : α) (y : β), R x y → R (f^[n] x) (g^[n] y)
  | 0, _, _, r => r
  | n + 1, x, y, r => iterate_rel R f g h n (f x) (g y) (h x y r)

/-- A bisimulation that preserves row keys and successors. -/
theorem key_bisimulation_eqv {K₁ K₂ : Nat} (t₁ : Table K₁) (t₂ : Table K₂)
    (R : Fin (K₁ + 1) → Fin (K₂ + 1) → Prop)
    (hkey : ∀ x y, R x y → (t₁.prog x).tree.key = (t₂.prog y).tree.key)
    (hnext : ∀ x y, R x y → R (t₁.next x) (t₂.next y)) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))
    (r : R i₁ i₂) : PEqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] :=
  key_bisim_eqv t₁ t₂ i₁ i₂ (fun n => hkey _ _ (iterate_rel R t₁.next t₂.next hnext n i₁ i₂ r))

/-! ## Tables whose rows spell polls -/

section Polls

variable {K₁ K₂ : Nat} (t₁ : Table K₁) (t₂ : Table K₂) (poll₁ : Fin (K₁ + 1) → Poll)
  (poll₂ : Fin (K₂ + 1) → Poll) (h₁ : ∀ i, Spells (t₁.prog i) (poll₁ i))
  (h₂ : ∀ i, Spells (t₂.prog i) (poll₂ i)) (i₁ : Fin (K₁ + 1)) (i₂ : Fin (K₂ + 1))

/-- A table whose rows spell polls equals the table of the written polls. -/
theorem written_eqv {K : Nat} (t : Table K) (poll : Fin (K + 1) → Poll) (h : ∀ i, Spells (t.prog i) (poll i))
    (i : Fin (K + 1)) :
    PEqv false [State] (t.entered i) ((Table.ofPolls poll t.next).entered i) [Bit] :=
  WithGuardedTablePacking.WithPhaseUniformity.ofTablePacking false
    (rows_eqv t (Table.ofPolls poll t.next) (fun _ => rfl) h i)

include h₁ h₂ in
theorem polls_of_obs (obs : t₁.observations i₁ false = t₂.observations i₂ false) (n : Nat) :
    poll₁ (t₁.next^[n] i₁) = poll₂ (t₂.next^[n] i₂) :=
  polls_of_observations poll₁ t₁.next poll₂ t₂.next i₁ i₂
    ((observations_of_eqv (written_eqv t₁ poll₁ h₁ i₁) false).symm.trans
      (obs.trans (observations_of_eqv (written_eqv t₂ poll₂ h₂ i₂) false))) n

include h₁ h₂ in
theorem eqv_of_polls (h : ∀ n, poll₁ (t₁.next^[n] i₁) = poll₂ (t₂.next^[n] i₂)) :
    PEqv false [State] (t₁.entered i₁) (t₂.entered i₂) [Bit] :=
  key_bisim_eqv t₁ t₂ i₁ i₂ (fun n =>
    (h₁ _).trans ((congrArg (fun a : Poll => a.program.tree.key) (h n)).trans (h₂ _).symm))

end Polls

/-! ## The ring and the lasso -/

/-- The joint orbit of the two entries. -/
abbrev ringLasso (x y : Fin 4) : Prop :=
  (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 1) ∨ (x = 2 ∧ y = 2) ∨ (x = 3 ∧ y = 1) ∨ (x = 0 ∧ y = 2)

theorem ringLasso_next (x y : Fin 4) (r : ringLasso x y) : ringLasso (ringNext x) (lassoNext y) := by
  rcases r with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

theorem ringLasso_poll (a b c : Poll) (x y : Fin 4) (r : ringLasso x y) :
    ringPolls a b x = lassoPolls a b c a y := by
  rcases r with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem ring_lasso_polls (a b c : Poll) (n : Nat) :
    ringPolls a b (ringNext^[n] 0) = lassoPolls a b c a (lassoNext^[n] 0) :=
  ringLasso_poll a b c _ _ (iterate_rel ringLasso ringNext lassoNext ringLasso_next n 0 0 (.inl ⟨rfl, rfl⟩))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithAdministrativeReturns.GuardedTablePacking.PhaseUniformity.TableModel
