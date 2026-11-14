module

public import Silmaril.Wasm.Cfg.BlockTyping.Defs

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.BlockTyping

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Validation

theorem ifaceOf?_sound {id : BlockId} {C : Context} {s : List CValType} {poly : Bool}
    {is : List Instr} {x : BlockIface} (h : ifaceOf? id C s poly is = some x) : x.Typed := by
  unfold ifaceOf? at h
  split at h
  · rename_i hs
    split at h
    · rename_i out xs k hc
      cases h
      exact (checkSeq_sound atomC_sound tyOkC_sound _ hc (resOk_sound tyOkC_sound hs)).1
    · cases h
  · cases h

theorem mem_toList_typed {o : Option BlockIface} {x : BlockIface}
    (ho : ∀ y, o = some y → y.Typed) (hx : x ∈ o.toList) : x.Typed := by
  cases o with
  | none => simp at hx
  | some y => simp at hx; subst hx; exact ho _ rfl

theorem armOf_size {i : Instr} {a : Nat} {c : List Instr} (h : armOf i a = some c) :
    sizeOf c < sizeOf i := by
  cases i <;> rcases a with _ | _ | a <;> simp [armOf] at h <;> subst h <;> first | (simp; done) | (simp; omega)

/-- The sequences a terminator opens are typed, given that its arms' walks are. -/
theorem typeNested_of (path : List SeqStep) (k : Nat) (C : Context) (i : Instr)
    (IH : ∀ a c, armOf i a = some c → ∀ (path' : List SeqStep) (C' : Context)
      (s' : List CValType), ∀ x ∈ typeWalk path' 0 C' s' false [] c, x.Typed) :
    ∀ x ∈ typeNested path k C i, x.Typed := by
  intro x hx
  cases i
  case block bt b =>
    simp only [typeNested] at hx; split at hx
    · exact IH 0 b rfl _ _ _ x hx
    · simp at hx
  case tryTable bt cs b =>
    simp only [typeNested] at hx; split at hx
    · exact IH 0 b rfl _ _ _ x hx
    · simp at hx
  case loop bt b =>
    simp only [typeNested] at hx; split at hx
    · exact IH 0 b rfl _ _ _ x hx
    · simp at hx
  case if_ bt t e =>
    simp only [typeNested] at hx; split at hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact IH 0 t rfl _ _ _ x hx
      · exact IH 1 e rfl _ _ _ x hx
    · simp at hx
  all_goals simp [typeNested] at hx

/-- **Every interface the walk records is typed.** -/
theorem typeWalk_typed (path : List SeqStep) (k : Nat) (C : Context) (s : List CValType)
    (poly : Bool) (acc : List Instr) (is : List Instr) :
    ∀ x ∈ typeWalk path k C s poly acc is, x.Typed := by
  intro x hx
  match is with
  | [] =>
    unfold typeWalk at hx
    split at hx
    · simp at hx
    · exact mem_toList_typed (fun _ h => ifaceOf?_sound h) hx
  | i :: is =>
    unfold typeWalk at hx
    split at hx
    · simp only [List.mem_append] at hx
      rcases hx with hx | hx | hx
      · exact mem_toList_typed (fun _ h => ifaceOf?_sound h) hx
      · split at hx
        · exact typeNested_of path k _ i (fun a c hc path' C' s' y hy =>
            have := armOf_size hc
            typeWalk_typed path' 0 C' s' false [] c y hy) x hx
        · simp at hx
      · split at hx
        · exact typeWalk_typed path (k + 1) _ _ _ [] is x hx
        · simp at hx
    · exact typeWalk_typed path k C s poly (i :: acc) is x hx
termination_by sizeOf is
decreasing_by
  all_goals first | (simp_wf; done) | (simp_wf; omega)

end Silmaril.Wasm.Cfg.Proofs.BlockTyping
