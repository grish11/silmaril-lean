module

public import Silmaril.Proofs.Logic.SAT.Carrier.Basic

/-! Proofs for `Silmaril.Logic.SAT.Carrier.Thms`: the flat LRAT certificate stream is decoded
losslessly on representable steps. -/

@[expose] public section

namespace Silmaril.Proofs.Logic.SAT.Carrier.LratStream

open Silmaril.Logic.SAT Silmaril.Logic.SAT.Carrier Silmaril.Logic.SAT.Carrier.LratStream
open Silmaril.Proofs.Logic.SAT.Carrier (toInt_encodeLit encodeLit_toInt litWord_iff
  litWord_encodeLit toInt_bounds two_pow_31)

/-! ## Words of ids -/

theorem natWord_eq (n : Nat) : natWord n = encodeLit (n : Int) := by
  simp [natWord, encodeLit]

theorem inRange_of_natRange {n : Nat} (h : NatRange n) : InRange (n : Int) := by
  obtain ⟨_, h2⟩ := h
  simp only [InRange, two_pow_31]
  omega

theorem toInt_natWord {n : Nat} (h : NatRange n) : (natWord n).toInt = n := by
  rw [natWord_eq, toInt_encodeLit (inRange_of_natRange h)]

theorem posWord?_natWord {n : Nat} (h : NatRange n) : posWord? (natWord n) = some n := by
  have := h.1
  simp [posWord?, toInt_natWord h, this]

theorem posWord?_eq_some {x : S32} {n : Nat} (h : posWord? x = some n) :
    natWord n = x ∧ NatRange n := by
  unfold posWord? at h
  split at h
  · next hp =>
    cases h
    have hb := (toInt_bounds x).2
    have hn : ((x.toInt.toNat : Nat) : Int) = x.toInt := Int.toNat_of_nonneg (Int.le_of_lt hp)
    refine ⟨?_, by omega, by omega⟩
    rw [natWord_eq, hn, encodeLit_toInt]
  · cases h

theorem posWord?_zero : posWord? 0 = none := by decide

theorem natWord_ne_zero {n : Nat} (h : NatRange n) : natWord n ≠ 0 := by
  intro h0
  have := posWord?_natWord h
  rw [h0, posWord?_zero] at this
  cases this

theorem encodeLit_ne_zero {l : Lit} (h : LitRange l) : encodeLit l ≠ 0 := by
  intro h0
  have := toInt_encodeLit h.2
  rw [h0] at this
  exact h.1 this.symm

/-! ## Literals and ids -/

theorem lits_enc {ls : Clause} (h : ∀ l ∈ ls, LitRange l) (r : List S32) :
    lits (encLits ls ++ r) = some (ls, r) := by
  induction ls with
  | nil => simp [encLits, lits]
  | cons l ls ih =>
    have hl := h l (List.mem_cons_self ..)
    have ih := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have hz : ¬ encodeLit l = 0#32 := encodeLit_ne_zero hl
    have e : encLits (l :: ls) ++ r = encodeLit l :: (encLits ls ++ r) := by simp [encLits]
    rw [e]
    simp [lits, hz, litWord_encodeLit hl, ih, toInt_encodeLit hl.2]

theorem lits_eq_some {xs : List S32} {ls : Clause} {r : List S32}
    (h : lits xs = some (ls, r)) : encLits ls ++ r = xs ∧ ∀ l ∈ ls, LitRange l := by
  induction xs generalizing ls with
  | nil => simp [lits] at h
  | cons x xs ih =>
    unfold lits at h
    split at h
    · next hx =>
      cases h
      subst hx
      simp [encLits]
    · next hx =>
      split at h
      · next hw =>
        obtain ⟨⟨ls', r'⟩, hq, he⟩ := Option.map_eq_some_iff.1 h
        cases he
        obtain ⟨he, hr⟩ := ih hq
        refine ⟨?_, ?_⟩
        · simp only [encLits, List.map_cons, List.cons_append] at he ⊢
          rw [encodeLit_toInt, ← he]
        · intro l hl
          rcases List.mem_cons.1 hl with rfl | hl
          · exact (litWord_iff x).1 hw
          · exact hr l hl
      · cases h

theorem ids_enc {is : List Nat} (h : ∀ i ∈ is, NatRange i) (r : List S32) :
    ids (encIds is ++ r) = some (is, r) := by
  induction is with
  | nil => simp [encIds, ids]
  | cons i is ih =>
    have hi := h i (List.mem_cons_self ..)
    have ih := ih fun i' hi' => h i' (List.mem_cons_of_mem _ hi')
    have hz : ¬ natWord i = 0#32 := natWord_ne_zero hi
    have e : encIds (i :: is) ++ r = natWord i :: (encIds is ++ r) := by simp [encIds]
    rw [e]
    simp [ids, hz, posWord?_natWord hi, ih]

theorem ids_eq_some {xs : List S32} {is : List Nat} {r : List S32}
    (h : ids xs = some (is, r)) : encIds is ++ r = xs ∧ ∀ i ∈ is, NatRange i := by
  induction xs generalizing is with
  | nil => simp [ids] at h
  | cons x xs ih =>
    unfold ids at h
    split at h
    · next hx =>
      cases h
      subst hx
      simp [encIds]
    · obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨⟨is', r'⟩, hq, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      obtain ⟨he, hr⟩ := ih hq
      obtain ⟨hw, hnr⟩ := posWord?_eq_some hn
      refine ⟨?_, ?_⟩
      · simp only [encIds, List.map_cons, List.cons_append] at he ⊢
        rw [hw, ← he]
      · intro i hi
        rcases List.mem_cons.1 hi with rfl | hi
        · exact hnr
        · exact hr i hi

/-! ## RAT groups -/

/-- The ranges of RAT groups. -/
def GroupsRange (gs : List (Nat × List Nat)) : Prop := ∀ g ∈ gs, NatRange g.1 ∧ ∀ h ∈ g.2, NatRange h

theorem groups_enc {gs : List (Nat × List Nat)} (h : GroupsRange gs) {f : Nat}
    (hf : gs.length < f) (r : List S32) : groups f (encGroups gs ++ r) = some (gs, r) := by
  induction gs generalizing f with
  | nil =>
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    simp [encGroups, groups]
  | cons g gs ih =>
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hg := h g (List.mem_cons_self ..)
    have ih := ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')) (f := f)
      (by simp at hf; omega)
    have he : encGroups (g :: gs) ++ r = natWord g.1 :: (encIds g.2 ++ (encGroups gs ++ r)) := by
      simp [encGroups]
    have hz : ¬ natWord g.1 = 0#32 := natWord_ne_zero hg.1
    rw [he]
    simp [groups, hz, posWord?_natWord hg.1, ids_enc hg.2, ih]

theorem groups_eq_some {f : Nat} {xs : List S32} {gs : List (Nat × List Nat)} {r : List S32}
    (h : groups f xs = some (gs, r)) : encGroups gs ++ r = xs ∧ GroupsRange gs := by
  induction f generalizing xs gs with
  | zero =>
    cases xs with
    | nil => simp [groups] at h
    | cons x xs => simp [groups] at h
  | succ f ih =>
    cases xs with
    | nil => simp [groups] at h
    | cons x xs =>
      unfold groups at h
      split at h
      · next hx =>
        cases h
        subst hx
        exact ⟨by simp [encGroups], by simp [GroupsRange]⟩
      · obtain ⟨j, hj, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨⟨hs, r₁⟩, hq, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨⟨gs', r₂⟩, hq', he⟩ := Option.map_eq_some_iff.1 h
        cases he
        obtain ⟨hw, hjr⟩ := posWord?_eq_some hj
        obtain ⟨hie, hir⟩ := ids_eq_some hq
        obtain ⟨hge, hgr⟩ := ih hq'
        refine ⟨?_, ?_⟩
        · simp only [encGroups, List.flatMap_cons, List.append_assoc, List.cons_append] at hge ⊢
          rw [hw, hge, hie]
        · intro g hg
          rcases List.mem_cons.1 hg with rfl | hg
          · exact ⟨hjr, hir⟩
          · exact hgr g hg

theorem length_encGroups (gs : List (Nat × List Nat)) : gs.length < (encGroups gs).length := by
  induction gs with
  | nil => simp [encGroups]
  | cons g gs ih =>
    simp only [encGroups, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

/-! ## Steps -/

theorem step_enc {s : LRAT.Step} (h : StepRange s) {fuel : Nat}
    (hf : (encodeStep s).length ≤ fuel) (r : List S32) :
    step fuel (encodeStep s ++ r) = some (s, r) := by
  cases s with
  | add id ls hs =>
    obtain ⟨hid, hl, hh⟩ := h
    have he : encodeStep (.add id ls hs) ++ r = 1 :: natWord id :: (encLits ls ++ (encIds hs ++ r)) := by
      simp [encodeStep]
    rw [he]
    simp [step, posWord?_natWord hid, lits_enc hl, ids_enc hh]
  | del is =>
    obtain ⟨x, xs, hx⟩ : ∃ x xs, encIds is ++ r = x :: xs := by
      cases is <;> simp [encIds]
    have he : encodeStep (.del is) ++ r = 2 :: x :: xs := by simp [encodeStep, ← hx]
    rw [he]
    simp only [step]
    rw [← hx, ids_enc h]
    simp
  | rat id ls gs =>
    obtain ⟨hid, hl, hg⟩ := h
    have hlen : gs.length < fuel := by
      have := length_encGroups gs
      simp only [encodeStep, List.length_append] at hf
      omega
    have he : encodeStep (.rat id ls gs) ++ r =
        3 :: natWord id :: (encLits ls ++ (encGroups gs ++ r)) := by
      simp [encodeStep]
    rw [he]
    simp [step, posWord?_natWord hid, lits_enc hl, groups_enc hg hlen]

theorem step_eq_some {fuel : Nat} {xs : List S32} {s : LRAT.Step} {r : List S32}
    (h : step fuel xs = some (s, r)) : encodeStep s ++ r = xs ∧ StepRange s := by
  rcases xs with _ | ⟨t, _ | ⟨x, xs⟩⟩
  · simp [step] at h
  · simp [step] at h
  simp only [step] at h
  split at h
  · next ht =>
    subst ht
    obtain ⟨id, hid, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨ls, r₁⟩, hq, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨⟨hs, r₂⟩, hq', he⟩ := Option.map_eq_some_iff.1 h
    cases he
    obtain ⟨hw, hir⟩ := posWord?_eq_some hid
    obtain ⟨hle, hlr⟩ := lits_eq_some hq
    obtain ⟨hhe, hhr⟩ := ids_eq_some hq'
    refine ⟨?_, hir, hlr, hhr⟩
    simp only [encodeStep, List.cons_append, List.nil_append, List.append_assoc]
    rw [hhe, hle, hw]
  · split at h
    · next ht =>
      subst ht
      obtain ⟨⟨is, r₁⟩, hq, he⟩ := Option.map_eq_some_iff.1 h
      cases he
      obtain ⟨hie, hir⟩ := ids_eq_some hq
      refine ⟨?_, hir⟩
      simp only [encodeStep, List.cons_append]
      rw [hie]
    · split at h
      · next ht =>
        subst ht
        obtain ⟨id, hid, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨⟨ls, r₁⟩, hq, h⟩ := Option.bind_eq_some_iff.1 h
        obtain ⟨⟨gs, r₂⟩, hq', he⟩ := Option.map_eq_some_iff.1 h
        cases he
        obtain ⟨hw, hir⟩ := posWord?_eq_some hid
        obtain ⟨hle, hlr⟩ := lits_eq_some hq
        obtain ⟨hge, hgr⟩ := groups_eq_some hq'
        refine ⟨?_, hir, hlr, hgr⟩
        simp only [encodeStep, List.cons_append, List.nil_append, List.append_assoc]
        rw [hge, hle, hw]
      · cases h

theorem encodeStep_ne_nil (s : LRAT.Step) : encodeStep s ≠ [] := by
  cases s <;> simp [encodeStep]

theorem length_le_encode (ss : List LRAT.Step) : ss.length ≤ (encode ss).length := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    have := encodeStep_ne_nil s
    have : 0 < (encodeStep s).length := List.length_pos_iff.2 this
    simp only [encode, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

theorem steps_enc {ss : List LRAT.Step} (h : ∀ s ∈ ss, StepRange s) {f : Nat}
    (hf : ss.length ≤ f) : steps f (encode ss) = some ss := by
  induction ss generalizing f with
  | nil => cases f <;> simp [encode, steps]
  | cons s ss ih =>
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by simp at hf; omega⟩
    have hs := h s (List.mem_cons_self ..)
    have ih := ih (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')) (f := f)
      (by simp at hf; omega)
    obtain ⟨x, xs, hx⟩ : ∃ x xs, encodeStep s ++ encode ss = x :: xs := by
      obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil (encodeStep_ne_nil s)
      exact ⟨x, xs ++ encode ss, by rw [hx]; rfl⟩
    have he : encode (s :: ss) = x :: xs := by simp [encode, ← hx]
    rw [he]
    simp only [steps]
    rw [← hx, step_enc hs (by simp) (encode ss)]
    simp [ih]

theorem steps_eq_some {f : Nat} {xs : List S32} {ss : List LRAT.Step}
    (h : steps f xs = some ss) : encode ss = xs ∧ ∀ s ∈ ss, StepRange s := by
  induction f generalizing xs ss with
  | zero =>
    cases xs with
    | nil => simp [steps] at h; subst h; simp [encode]
    | cons x xs => simp [steps] at h
  | succ f ih =>
    cases xs with
    | nil => simp [steps] at h; subst h; simp [encode]
    | cons x xs =>
      simp only [steps] at h
      obtain ⟨⟨s, r⟩, hq, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨ss', hq', he⟩ := Option.map_eq_some_iff.1 h
      cases he
      obtain ⟨hse, hsr⟩ := step_eq_some hq
      obtain ⟨hre, hrr⟩ := ih hq'
      refine ⟨?_, ?_⟩
      · simp only [encode, List.flatMap_cons] at hre ⊢
        rw [hre, hse]
      · intro s' hs'
        rcases List.mem_cons.1 hs' with rfl | hs'
        · exact hsr
        · exact hrr s' hs'

/-! ## The decoder -/

theorem decode_encode {ss : List LRAT.Step} (h : ∀ s ∈ ss, StepRange s) :
    decode (encode ss) = some ss :=
  steps_enc h (length_le_encode ss)

theorem encode_decode {xs : List S32} {ss : List LRAT.Step} (h : decode xs = some ss) :
    encode ss = xs :=
  (steps_eq_some h).1

theorem stepRange_of_decode {xs : List S32} {ss : List LRAT.Step} (h : decode xs = some ss) :
    ∀ s ∈ ss, StepRange s :=
  (steps_eq_some h).2

end Silmaril.Proofs.Logic.SAT.Carrier.LratStream
