module

public import Silmaril.Logic.STLCRestriction.Defs

@[expose] public section
noncomputable section
namespace Silmaril.Proofs.Logic.STLCRestriction
open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Logic Silmaril.Logic.STLCRestriction Silmaril.Logic.Algebraic.Lambda
variable {B : Type} {S : STLCMatching.FixedSignature B}

theorem expansion_iff (M : LambdaModel S.source) :
    (∃ N : STLCMatching.Model S.source, (forgetFunctor S).obj N = M) ↔
      ∀ b, Nonempty (M.toSetModel.base b) := by
  constructor
  · rintro ⟨N, rfl⟩
    exact N.nonempty
  · intro h
    exact ⟨⟨M.toSetModel, h⟩, LambdaModel.ext rfl⟩

theorem modelExpansive_iff_isEmpty (B : Type) :
    (toInhabited B).ModelExpansive ↔ IsEmpty B := by
  change (∀ S : STLCMatching.FixedSignature B,
    ∀ M : LambdaModel S.source, ∃ N, (forgetFunctor S).obj N = M) ↔ IsEmpty B
  constructor
  · intro h
    refine ⟨fun b => ?_⟩
    have he := (expansion_iff (emptyModel B)).mp (h _ (emptyModel B)) b
    obtain ⟨x⟩ := he
    exact x.elim
  · intro h S M
    exact (expansion_iff M).mpr (fun b => (h.false b).elim)

end Silmaril.Proofs.Logic.STLCRestriction
