module

public import Silmaril.Wasm.Cfg.BlockTyping.Defs
public import Silmaril.Wasm.Cfg.BlockTree.Defs

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

/-! ## The recorded instructions are the block's segment -/

theorem ifaceOf?_id {id : BlockId} {C : Context} {s : List CValType} {poly : Bool}
    {is : List Instr} {x : BlockIface} (h : ifaceOf? id C s poly is = some x) :
    x.id = id ∧ x.instrs = is := by
  unfold ifaceOf? at h
  split at h
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h
  · cases h

theorem typeNested_mem_of (path : List SeqStep) (k : Nat) (C : Context) (i : Instr)
    (IH : ∀ a c, armOf i a = some c → ∀ (path' : List SeqStep) (C' : Context)
      (s' : List CValType), ∀ x ∈ typeWalk path' 0 C' s' false [] c,
        ∃ seg, (x.id, seg) ∈ walk path' 0 [] c ∧ x.instrs = seg.instrs) :
    ∀ x ∈ typeNested path k C i, ∃ seg, (x.id, seg) ∈ nested path k i ∧ x.instrs = seg.instrs := by
  intro x hx
  cases i
  case block bt b =>
    simp only [typeNested] at hx; split at hx
    · simpa [nested] using IH 0 b rfl _ _ _ x hx
    · simp at hx
  case tryTable bt cs b =>
    simp only [typeNested] at hx; split at hx
    · simpa [nested] using IH 0 b rfl _ _ _ x hx
    · simp at hx
  case loop bt b =>
    simp only [typeNested] at hx; split at hx
    · simpa [nested] using IH 0 b rfl _ _ _ x hx
    · simp at hx
  case if_ bt t e =>
    simp only [typeNested] at hx; split at hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨seg, h1, h2⟩ := IH 0 t rfl _ _ _ x hx
        exact ⟨seg, by simp [nested, h1], h2⟩
      · obtain ⟨seg, h1, h2⟩ := IH 1 e rfl _ _ _ x hx
        exact ⟨seg, by simp [nested, h1], h2⟩
    · simp at hx
  all_goals simp [typeNested] at hx

/-- Every interface the walk records names a block of `walk` with the same instructions. -/
theorem typeWalk_mem (path : List SeqStep) (k : Nat) (C : Context) (s : List CValType)
    (poly : Bool) (acc : List Instr) (is : List Instr) :
    ∀ x ∈ typeWalk path k C s poly acc is,
      ∃ seg, (x.id, seg) ∈ walk path k acc is ∧ x.instrs = seg.instrs := by
  intro x hx
  match is with
  | [] =>
    unfold typeWalk at hx
    unfold walk
    split at hx
    · simp at hx
    · rename_i hacc
      cases ho : ifaceOf? ⟨path, k⟩ C s poly acc.reverse with
      | none => simp [ho] at hx
      | some y =>
        simp [ho] at hx; subst hx
        obtain ⟨h1, h2⟩ := ifaceOf?_id ho
        refine ⟨⟨acc.reverse, none⟩, ?_, ?_⟩
        · simp [hacc, h1]
        · simp [h2, Segment.instrs]
  | i :: is =>
    unfold typeWalk at hx
    unfold walk
    split at hx
    · rename_i hi
      simp only [hi, ite_true, List.mem_append, List.mem_cons]
      simp only [List.mem_append] at hx
      rcases hx with hx | hx | hx
      · cases ho : ifaceOf? ⟨path, k⟩ C s poly (acc.reverse ++ [i]) with
        | none => simp [ho] at hx
        | some y =>
          simp [ho] at hx; subst hx
          obtain ⟨h1, h2⟩ := ifaceOf?_id ho
          exact ⟨⟨acc.reverse, some i⟩, Or.inl (by rw [h1]), by simp [h2, Segment.instrs]⟩
      · split at hx
        · obtain ⟨seg, h1, h2⟩ := typeNested_mem_of path k _ i (fun a c hc path' C' s' y hy =>
            have := armOf_size hc
            typeWalk_mem path' 0 C' s' false [] c y hy) x hx
          exact ⟨seg, Or.inr (Or.inl h1), h2⟩
        · simp at hx
      · split at hx
        · obtain ⟨seg, h1, h2⟩ := typeWalk_mem path (k + 1) _ _ _ [] is x hx
          exact ⟨seg, Or.inr (Or.inr h1), h2⟩
        · simp at hx
    · rename_i hi
      simp only [hi]
      exact typeWalk_mem path k C s poly (i :: acc) is x hx
termination_by sizeOf is
decreasing_by
  all_goals first | (simp_wf; done) | (simp_wf; omega)

end Silmaril.Wasm.Cfg.Proofs.BlockTyping
