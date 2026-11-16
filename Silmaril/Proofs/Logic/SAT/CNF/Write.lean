module

public import Silmaril.Logic.SAT.CNF.Defs

/-! Proofs for `Dimacs.read_write` in `Silmaril.Logic.SAT.CNF.Thms`. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.SAT.CNF.Write

open Silmaril.Logic.SAT Silmaril.Logic.SAT.Dimacs

theorem step_ne (F : CNF) (c : Clause) {x : Int} (hx : x ≠ 0) :
    step (F, c) x = (F, c ++ [x]) := by
  match x, hx with
  | .ofNat 0, h => exact absurd rfl h
  | .ofNat (_ + 1), _ => rfl
  | .negSucc _, _ => rfl

/-- Reading the literals of a clause without `0` appends them to the pending clause. -/
theorem foldl_clause (F : CNF) : ∀ (c K : Clause), (0 : Lit) ∉ K →
    K.foldl step (F, c) = (F, c ++ K)
  | c, [], _ => by simp
  | c, x :: K, h => by
    have hx : x ≠ 0 := fun e => h (e ▸ List.mem_cons_self)
    have hK : (0 : Lit) ∉ K := fun e => h (List.mem_cons_of_mem _ e)
    rw [List.foldl_cons, step_ne F c hx, foldl_clause F _ K hK, List.append_assoc,
      List.singleton_append]

theorem foldl_write : ∀ (G F : CNF), (∀ C ∈ F, (0 : Lit) ∉ C) →
    (write F).foldl step (G, []) = (G ++ F, [])
  | G, [], _ => by simp [write]
  | G, K :: F, h => by
    have hK : (0 : Lit) ∉ K := h K List.mem_cons_self
    have hF : ∀ C ∈ F, (0 : Lit) ∉ C := fun C hC => h C (List.mem_cons_of_mem _ hC)
    have hw : write (K :: F) = K ++ [0] ++ write F := by simp [write]
    rw [hw, List.foldl_append, List.foldl_append, foldl_clause G [] K hK]
    simp only [List.nil_append, List.foldl_cons, List.foldl_nil, step]
    rw [foldl_write (G ++ [K]) F hF]
    simp

theorem read_write {F : CNF} (h : ∀ C ∈ F, (0 : Lit) ∉ C) : read (write F) = (F, []) := by
  have := foldl_write [] F h
  rw [List.nil_append] at this
  exact this

end Silmaril.Proofs.Logic.SAT.CNF.Write
