module

public import Silmaril.Proofs.Wasm.Abstract.ExposePStruct.Lands

/-!
Proofs for `Silmaril.Wasm.Abstract.ExposePStruct.Thms`: the stack tensor on the operations.
A passive stack below the parameters of a block, a loop or an `if` arm is appended to the
fallthrough and to the loop's states, whatever the body; a flat instruction appends it to every
stack it ends with.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Abstract.ExposePStruct

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Abstract.Body
open Silmaril.Wasm.Abstract.StoreBody Silmaril.Wasm.Abstract.StoreCall
open Silmaril.Wasm.Abstract.ExposeP Silmaril.Wasm.Abstract.ExposePStruct
open Silmaril.Wasm.Interp

variable {H : Type}

/-! ## Exits -/

theorem blockKP_whisk {np nr : Nat} {stk : List Val} (rest : List Val) (hle : np ≤ stk.length)
    (r : ResP) :
    (blockKP (H := H) np nr (stk ++ rest) r) = whiskP rest <$> blockKP np nr stk r := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal vs =>
      simp only [blockKP, map_pure, whiskP, List.drop_append_of_le_length hle, List.append_assoc]
    | brk k vs =>
      cases k <;>
        simp only [blockKP, map_pure, whiskP, List.drop_append_of_le_length hle, List.append_assoc]
    | _ => simp only [blockKP, map_pure, whiskP]
  · simp only [blockKP, map_pure, whiskP]

theorem loopKP_whisk {np nr : Nat} {stk : List Val} (rest : List Val) (hle : np ≤ stk.length)
    (r : ResP) :
    (loopKP (H := H) np nr (stk ++ rest) r) =
      Sum.map (whiskP rest) (wcfg rest) <$> loopKP np nr stk r := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | normal vs =>
      simp only [loopKP, map_pure, whiskP, Sum.map_inl, List.drop_append_of_le_length hle,
        List.append_assoc]
    | brk k vs =>
      cases k <;>
        simp only [loopKP, map_pure, whiskP, wcfg, Sum.map_inl, Sum.map_inr,
          List.drop_append_of_le_length hle, List.append_assoc]
    | _ => simp only [loopKP, map_pure, whiskP, Sum.map_inl]
  · simp only [loopKP, map_pure, whiskP, Sum.map_inl]

theorem tryKP_whisk {np nr : Nat} {stk : List Val} {cs : List Catch} (rest : List Val)
    (hle : np ≤ stk.length) (r : ResP) (hr : ∀ f a, r ≠ ⟨(f, .flow (.throw a))⟩) :
    (tryKP (H := H) np nr (stk ++ rest) cs r) = whiskP rest <$> tryKP np nr stk cs r := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | throw a => exact absurd rfl (hr f a)
    | _ => first | exact blockKP_whisk rest hle _ | (simp only [tryKP]; exact blockKP_whisk rest hle _)
  · simp only [tryKP]; exact blockKP_whisk rest hle _

/-! ## Operations -/

theorem blockP_whisk (bt : BlockType) (g : PHom H Cfg ResP) (rest : List Val) (c : Cfg)
    {np nr : Nat} (hc : arity c.down.1 bt = some (np, nr)) (hle : np ≤ c.down.2.length) :
    blockP bt g (wcfg rest c) = whiskP rest <$> blockP bt g c := by
  simp only [blockP, wcfg, hc, List.take_append_of_le_length hle, map_bind]
  congr 1
  funext r
  exact blockKP_whisk rest hle r

theorem loopStepP_whisk (bt : BlockType) (g : PHom H Cfg ResP) (rest : List Val) (c : Cfg)
    {np nr : Nat} (hc : arity c.down.1 bt = some (np, nr)) (hle : np ≤ c.down.2.length) :
    loopStepP bt g (wcfg rest c) = Sum.map (whiskP rest) (wcfg rest) <$> loopStepP bt g c := by
  simp only [loopStepP, wcfg, hc, List.take_append_of_le_length hle, map_bind]
  congr 1
  funext r
  exact loopKP_whisk rest hle r

theorem tryP_whisk (bt : BlockType) (cs : List Catch) (g : PHom H Cfg ResP) (rest : List Val)
    (c : Cfg) {np nr : Nat} (hc : arity c.down.1 bt = some (np, nr)) (hle : np ≤ c.down.2.length)
    (hg : Lands (fun r : ResP => ∀ f a, r ≠ ⟨(f, .flow (.throw a))⟩)
      (g ⟨(c.down.1, c.down.2.take np)⟩)) :
    tryP bt cs g (wcfg rest c) = whiskP rest <$> tryP bt cs g c := by
  simp only [tryP, wcfg, hc, List.take_append_of_le_length hle, map_bind]
  exact bind_congr_lands hg fun r hr => tryKP_whisk rest hle r hr

/-- The loop invariant of the stack tensor: the parameters are present and the block type has
the arity `(np, nr)` in the frame. -/
def LoopInv (bt : BlockType) (np nr : Nat) (c : Cfg) : Prop :=
  arity c.down.1 bt = some (np, nr) ∧ np ≤ c.down.2.length

/-- What a loop body must ensure of its `br 0`: the parameters are carried, and the frame
keeps the block type's arity. -/
def BrkOk (bt : BlockType) (np nr : Nat) (r : ResP) : Prop :=
  ∀ f vs, r = ⟨(f, .flow (.brk 0 vs))⟩ → arity f bt = some (np, nr) ∧ np ≤ vs.length

theorem loopKP_lands {bt : BlockType} {np nr : Nat} {stk : List Val} (r : ResP)
    (hr : BrkOk bt np nr r) :
    Lands (H := H) (Sum.elim (fun _ => True) (LoopInv bt np nr)) (loopKP np nr stk r) := by
  rcases r with ⟨f, (fl | ⟨a, args, n⟩)⟩
  · cases fl with
    | brk k vs =>
      cases k with
      | zero =>
        obtain ⟨ha, hle⟩ := hr f vs rfl
        refine lands_pure ⟨ha, ?_⟩
        simp only [List.length_append, List.length_take, List.length_drop]
        omega
      | succ k => exact lands_pure trivial
    | _ => exact lands_pure trivial
  · exact lands_pure trivial

theorem loopStepP_lands (bt : BlockType) (g : PHom H Cfg ResP) {np nr : Nat}
    (hg : ∀ c : Cfg, LoopInv bt np nr c → Lands (BrkOk bt np nr) (g ⟨(c.down.1, c.down.2.take np)⟩))
    (c : Cfg) (hc : LoopInv bt np nr c) :
    Lands (Sum.elim (fun _ => True) (LoopInv bt np nr)) (loopStepP bt g c) := by
  simp only [loopStepP, hc.1]
  exact lands_bind (hg c hc) fun r hr => loopKP_lands r hr

/-- **Loops are stack-polymorphic**: if the body carries its parameters on `br 0` and keeps
the block type's arity, a passive stack below the loop's parameters is appended to its exits. -/
theorem loopP_whisk (bt : BlockType) (g : PHom H Cfg ResP) (rest : List Val) {np nr : Nat}
    (hg : ∀ c : Cfg, LoopInv bt np nr c → Lands (BrkOk bt np nr) (g ⟨(c.down.1, c.down.2.take np)⟩))
    (c : Cfg) (hc : LoopInv bt np nr c) :
    loopP bt g (wcfg rest c) = whiskP rest <$> loopP bt g c :=
  iter_conj (loopStepP bt g) (LoopInv bt np nr) (wcfg rest) (whiskP rest)
    (loopStepP_lands bt g hg) (fun c hc => loopStepP_whisk bt g rest c hc.1 hc.2) c hc

/-- The arms of an `if` with a passive stack below the condition's remaining stack. -/
theorem ifKP_whisk (bt : BlockType) (gt ge : PHom H Cfg ResP) (rest : List Val) (f₁ : Frame)
    (cv : Val) (stk₁ : List Val) {np nr : Nat} (hc : arity f₁ bt = some (np, nr))
    (hle : np ≤ stk₁.length) :
    ifKP bt gt ge ⟨(f₁, .flow (.normal (cv :: (stk₁ ++ rest))))⟩ =
      whiskP rest <$> ifKP bt gt ge ⟨(f₁, .flow (.normal (cv :: stk₁)))⟩ := by
  simp only [ifKP, hc]
  cases truthy cv with
  | none => rw [map_eq_bind_pure_comp, stuck_bind']
  | some b =>
    simp only [List.take_append_of_le_length hle, map_bind]
    congr 1
    funext r
    exact blockKP_whisk rest hle r

end Silmaril.Proofs.Wasm.Abstract.ExposePStruct
