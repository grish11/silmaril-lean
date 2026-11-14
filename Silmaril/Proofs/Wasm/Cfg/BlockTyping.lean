module

public import Silmaril.Wasm.Cfg.BlockTyping.Defs
public import Silmaril.Wasm.Cfg.BlockTree.Defs

@[expose] public section

namespace Silmaril.Wasm.Cfg.Proofs.BlockTyping

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Validation

theorem ifaceOf?_sound {id : BlockId} {st : CkSt}
    {is : List Instr} {x : BlockIface} (h : ifaceOf? id st is = some x) : x.Typed := by
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
    (IH : ∀ a c, armOf i a = some c → ∀ (path' : List SeqStep) (st' : CkSt),
      ∀ x ∈ typeWalk path' 0 st' [] c, x.Typed) :
    ∀ x ∈ typeNested path k C i, x.Typed := by
  intro x hx
  cases i
  case block bt b =>
    simp only [typeNested] at hx; split at hx
    · exact IH 0 b rfl _ _ x hx
    · simp at hx
  case tryTable bt cs b =>
    simp only [typeNested] at hx; split at hx
    · exact IH 0 b rfl _ _ x hx
    · simp at hx
  case loop bt b =>
    simp only [typeNested] at hx; split at hx
    · exact IH 0 b rfl _ _ x hx
    · simp at hx
  case if_ bt t e =>
    simp only [typeNested] at hx; split at hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact IH 0 t rfl _ _ x hx
      · exact IH 1 e rfl _ _ x hx
    · simp at hx
  all_goals simp [typeNested] at hx

/-- **Every interface the walk records is typed.** -/
theorem typeWalk_typed (path : List SeqStep) (k : Nat) (st : CkSt) (acc : List Instr)
    (is : List Instr) : ∀ x ∈ typeWalk path k st acc is, x.Typed := by
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
        · exact typeNested_of path k _ i (fun a c hc path' st' y hy =>
            have := armOf_size hc
            typeWalk_typed path' 0 st' [] c y hy) x hx
        · simp at hx
      · split at hx
        · exact typeWalk_typed path (k + 1) _ [] is x hx
        · simp at hx
    · exact typeWalk_typed path k st (i :: acc) is x hx
termination_by sizeOf is
decreasing_by
  all_goals first | (simp_wf; done) | (simp_wf; omega)

/-! ## The recorded instructions are the block's segment -/

theorem ifaceOf?_id {id : BlockId} {st : CkSt}
    {is : List Instr} {x : BlockIface} (h : ifaceOf? id st is = some x) :
    x.id = id ∧ x.instrs = is := by
  unfold ifaceOf? at h
  split at h
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases h
  · cases h

theorem typeNested_mem_of (path : List SeqStep) (k : Nat) (C : Context) (i : Instr)
    (IH : ∀ a c, armOf i a = some c → ∀ (path' : List SeqStep) (st' : CkSt),
      ∀ x ∈ typeWalk path' 0 st' [] c,
        ∃ seg, (x.id, seg) ∈ walk path' 0 [] c ∧ x.instrs = seg.instrs) :
    ∀ x ∈ typeNested path k C i, ∃ seg, (x.id, seg) ∈ nested path k i ∧ x.instrs = seg.instrs := by
  intro x hx
  cases i
  case block bt b =>
    simp only [typeNested] at hx; split at hx
    · simpa [nested] using IH 0 b rfl _ _ x hx
    · simp at hx
  case tryTable bt cs b =>
    simp only [typeNested] at hx; split at hx
    · simpa [nested] using IH 0 b rfl _ _ x hx
    · simp at hx
  case loop bt b =>
    simp only [typeNested] at hx; split at hx
    · simpa [nested] using IH 0 b rfl _ _ x hx
    · simp at hx
  case if_ bt t e =>
    simp only [typeNested] at hx; split at hx
    · rw [List.mem_append] at hx
      rcases hx with hx | hx
      · obtain ⟨seg, h1, h2⟩ := IH 0 t rfl _ _ x hx
        exact ⟨seg, by simp [nested, h1], h2⟩
      · obtain ⟨seg, h1, h2⟩ := IH 1 e rfl _ _ x hx
        exact ⟨seg, by simp [nested, h1], h2⟩
    · simp at hx
  all_goals simp [typeNested] at hx

/-- Every interface the walk records names a block of `walk` with the same instructions. -/
theorem typeWalk_mem (path : List SeqStep) (k : Nat) (st : CkSt) (acc : List Instr)
    (is : List Instr) : ∀ x ∈ typeWalk path k st acc is,
      ∃ seg, (x.id, seg) ∈ walk path k acc is ∧ x.instrs = seg.instrs := by
  intro x hx
  match is with
  | [] =>
    unfold typeWalk at hx
    unfold walk
    split at hx
    · simp at hx
    · rename_i hacc
      cases ho : ifaceOf? ⟨path, k⟩ st acc.reverse with
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
      · cases ho : ifaceOf? ⟨path, k⟩ st (acc.reverse ++ [i]) with
        | none => simp [ho] at hx
        | some y =>
          simp [ho] at hx; subst hx
          obtain ⟨h1, h2⟩ := ifaceOf?_id ho
          exact ⟨⟨acc.reverse, some i⟩, Or.inl (by rw [h1]), by simp [h2, Segment.instrs]⟩
      · split at hx
        · obtain ⟨seg, h1, h2⟩ := typeNested_mem_of path k _ i (fun a c hc path' st' y hy =>
            have := armOf_size hc
            typeWalk_mem path' 0 st' [] c y hy) x hx
          exact ⟨seg, Or.inr (Or.inl h1), h2⟩
        · simp at hx
      · split at hx
        · obtain ⟨seg, h1, h2⟩ := typeWalk_mem path (k + 1) _ [] is x hx
          exact ⟨seg, Or.inr (Or.inr h1), h2⟩
        · simp at hx
    · rename_i hi
      simp only [hi]
      exact typeWalk_mem path k st (i :: acc) is x hx
termination_by sizeOf is
decreasing_by
  all_goals first | (simp_wf; done) | (simp_wf; omega)

end Silmaril.Wasm.Cfg.Proofs.BlockTyping

namespace Silmaril.Wasm.Cfg.Proofs.BlockTyping

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Validation

/-! ## Completeness: the checker's run and `checkSeq` -/

theorem run_checkSeq : ∀ (l : List Instr) (st st' : CkSt), ckRun st l = some st' →
    ∃ xs k, checkSeq atomC tyOkC st.C st.s st.poly none l = some (st'.s, xs, k)
  | [], st, st', h => by
    simp [ckRun] at h; subst h
    exact ⟨[], 0, by simp [checkSeq]⟩
  | i :: is, st, st', h => by
    simp only [ckRun, List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st1, h1, h2⟩ := h
    obtain ⟨xs, k, hc⟩ := run_checkSeq is st1 st' h2
    unfold ckStep at h1
    rw [checkSeq]
    split at h1
    · rename_i n xs0 out heq
      split at h1
      · rename_i hcond
        cases h1
        rw [heq]; simp only [hcond, ite_true]
        rw [hc]; exact ⟨_, _, rfl⟩
      · cases h1
    · rename_i t heq
      cases h1
      rw [heq]; simp only
      rw [hc]; exact ⟨_, _, rfl⟩
    · cases h1

theorem checkSeq_run : ∀ (l : List Instr) (C : Context) (s : List CValType) (poly : Bool) r,
    checkSeq atomC tyOkC C s poly none l = some r → ∃ st', ckRun ⟨C, s, poly⟩ l = some st'
  | [], C, s, poly, r, h => ⟨_, rfl⟩
  | i :: is, C, s, poly, r, h => by
    rw [checkSeq] at h
    split at h
    · rename_i n xs0 out heq
      split at h
      · rename_i hcond
        split at h
        · rename_i r' hr
          obtain ⟨st', h'⟩ := checkSeq_run is _ _ _ _ hr
          refine ⟨st', ?_⟩
          simp only [ckRun, List.foldlM_cons, Option.bind_eq_bind]
          unfold ckStep; simp only [heq, hcond, ite_true, Option.bind_some]
          exact h'
        · cases h
      · cases h
    · rename_i t heq
      split at h
      · rename_i r' hr
        obtain ⟨st', h'⟩ := checkSeq_run is _ _ _ _ hr
        refine ⟨st', ?_⟩
        simp only [ckRun, List.foldlM_cons, Option.bind_eq_bind]
        unfold ckStep; simp only [heq, Option.bind_some]
        exact h'
      · cases h
    · cases h

theorem checkSeq_goal_none : ∀ (l : List Instr) (C : Context) (s : List CValType) (poly : Bool)
    (g : List CValType) r, checkSeq atomC tyOkC C s poly (some g) l = some r →
      ∃ r', checkSeq atomC tyOkC C s poly none l = some r'
  | [], C, s, poly, g, r, h => ⟨(s, [], 0), by simp [checkSeq]⟩
  | i :: is, C, s, poly, g, r, h => by
    rw [checkSeq] at h
    rw [checkSeq]
    split at h
    · rename_i n xs0 out heq
      split at h
      · rename_i hcond
        simp only [hcond, ite_true]
        split at h
        · rename_i r' hr
          obtain ⟨r'', h'⟩ := checkSeq_goal_none is _ _ _ _ _ hr
          rw [h']; exact ⟨_, rfl⟩
        · cases h
      · cases h
    · rename_i t heq
      split at h
      · rename_i r' hr
        obtain ⟨r'', h'⟩ := checkSeq_goal_none is _ _ _ _ _ hr
        rw [h']; exact ⟨_, rfl⟩
      · cases h
    · cases h

theorem withLocals_toTypeCtx : ∀ (C : Context) (xs : List Nat) (lts : List LocalType),
    (C.withLocals xs lts).toTypeCtx = C.toTypeCtx
  | C, x :: xs, lt :: lts => by
    rw [Context.withLocals, withLocals_toTypeCtx]; rfl
  | C, [], _ => by unfold Context.withLocals; rfl
  | C, _ :: _, [] => by unfold Context.withLocals; rfl

theorem initLocals_toTypeCtx (C : Context) (xs : List Nat) :
    (C.initLocals xs).toTypeCtx = C.toTypeCtx := withLocals_toTypeCtx _ _ _

theorem ckStep_res {st st' : CkSt} {i : Instr} (h : ckStep st i = some st')
    (hs : resOk tyOkC st.C.toTypeCtx st.s = true) : resOk tyOkC st'.C.toTypeCtx st'.s = true := by
  unfold ckStep at h
  split at h
  · split at h
    · rename_i hcond
      cases h
      simp only [Bool.and_eq_true] at hcond
      simp only [resOk, List.all_append, Bool.and_eq_true, initLocals_toTypeCtx] at hs hcond ⊢
      exact ⟨List.all_eq_true.2 fun t ht => List.all_eq_true.1 hs t (List.mem_of_mem_take ht), hcond.2⟩
    · cases h
  · cases h; simp [resOk]
  · cases h

theorem ckRun_res : ∀ (l : List Instr) {st st' : CkSt}, ckRun st l = some st' →
    resOk tyOkC st.C.toTypeCtx st.s = true → resOk tyOkC st'.C.toTypeCtx st'.s = true
  | [], st, st', h, hs => by simp [ckRun] at h; subst h; exact hs
  | i :: is, st, st', h, hs => by
    simp only [ckRun, List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨st1, h1, h2⟩ := h
    exact ckRun_res is h2 (ckStep_res h1 hs)

theorem ckRun_append (st : CkSt) (l₁ l₂ : List Instr) :
    ckRun st (l₁ ++ l₂) = (ckRun st l₁).bind fun st' => ckRun st' l₂ := by
  simp [ckRun, List.foldlM_append]

theorem ckStep_some {st st' : CkSt} {i : Instr} (h : ckStep st i = some st') :
    ∃ r, checkInstr atomC tyOkC st.C (padStack (padFor st.C st.poly i) st.s) i = some r := by
  unfold ckStep at h
  split at h
  · rename_i heq; exact ⟨_, heq⟩
  · rename_i heq; exact ⟨_, heq⟩
  · cases h

/-- A structured instruction's arm, as the checker checks it: entry stack `t₁`, label `lbl`. -/
def ArmChecked (C : Context) (t₁ lbl : List CValType) (c : List Instr) : Prop :=
  resOk tyOkC C.toTypeCtx t₁ = true ∧ ∃ r, checkSeq atomC tyOkC (C.withLabel lbl) t₁ false none c = some r

theorem checkInstr_block {C : Context} {S : List CValType} {bt : BlockType} {b : List Instr}
    {r : StepRes} (h : checkInstr atomC tyOkC C S (.block bt b) = some r) :
    ∃ t₁ t₂, CheckInstrs.blockType? tyOkC C bt = some (t₁, t₂) ∧ ArmChecked C t₁ t₂ b := by
  rw [checkInstr] at h
  split at h
  · rename_i t₁ t₂ hbt
    split at h
    · rename_i hok
      split at h
      · rename_i r' hr
        simp only [Bool.and_eq_true] at hok
        exact ⟨t₁, t₂, hbt, hok.1, checkSeq_goal_none _ _ _ _ _ _ hr⟩
      · simp at h
    · simp at h
  · simp at h

theorem checkInstr_loop {C : Context} {S : List CValType} {bt : BlockType} {b : List Instr}
    {r : StepRes} (h : checkInstr atomC tyOkC C S (.loop bt b) = some r) :
    ∃ t₁ t₂, CheckInstrs.blockType? tyOkC C bt = some (t₁, t₂) ∧ ArmChecked C t₁ t₁ b := by
  rw [checkInstr] at h
  split at h
  · rename_i t₁ t₂ hbt
    split at h
    · rename_i hok
      split at h
      · rename_i r' hr
        simp only [Bool.and_eq_true] at hok
        exact ⟨t₁, t₂, hbt, hok.1, checkSeq_goal_none _ _ _ _ _ _ hr⟩
      · simp at h
    · simp at h
  · simp at h

theorem checkInstr_tryTable {C : Context} {S : List CValType} {bt : BlockType} {cs : List Catch}
    {b : List Instr} {r : StepRes} (h : checkInstr atomC tyOkC C S (.tryTable bt cs b) = some r) :
    ∃ t₁ t₂, CheckInstrs.blockType? tyOkC C bt = some (t₁, t₂) ∧ ArmChecked C t₁ t₂ b := by
  rw [checkInstr] at h
  split at h
  · rename_i t₁ t₂ hbt
    split at h
    · rename_i hok
      split at h
      · rename_i r' hr
        simp only [Bool.and_eq_true] at hok
        exact ⟨t₁, t₂, hbt, hok.1.1, checkSeq_goal_none _ _ _ _ _ _ hr⟩
      · simp at h
    · simp at h
  · simp at h

theorem checkInstr_if {C : Context} {S : List CValType} {bt : BlockType} {t e : List Instr}
    {r : StepRes} (h : checkInstr atomC tyOkC C S (.if_ bt t e) = some r) :
    ∃ t₁ t₂, CheckInstrs.blockType? tyOkC C bt = some (t₁, t₂) ∧ ArmChecked C t₁ t₂ t ∧
      ArmChecked C t₁ t₂ e := by
  rw [checkInstr] at h
  split at h
  · rename_i t₁ t₂ hbt
    split at h
    · rename_i hok
      split at h
      · rename_i r₁ r₂ hr₁ hr₂
        simp only [Bool.and_eq_true] at hok
        exact ⟨t₁, t₂, hbt, ⟨hok.1, checkSeq_goal_none _ _ _ _ _ _ hr₁⟩,
          ⟨hok.1, checkSeq_goal_none _ _ _ _ _ _ hr₂⟩⟩
      · simp at h
    · simp at h
  · simp at h

theorem run_split {st : CkSt} {l₁ l₂ : List Instr} (h : ∃ st', ckRun st (l₁ ++ l₂) = some st') :
    ∃ st₁, ckRun st l₁ = some st₁ ∧ ∃ st', ckRun st₁ l₂ = some st' := by
  obtain ⟨st', h⟩ := h
  rw [ckRun_append] at h
  cases h₁ : ckRun st l₁ with
  | none => simp [h₁] at h
  | some st₁ => simp only [h₁, Option.bind_some] at h; exact ⟨st₁, rfl, st', h⟩

theorem ifaceOf?_some (id : BlockId) {st : CkSt} {l : List Instr}
    (hres : resOk tyOkC st.C.toTypeCtx st.s = true) (hrun : ∃ st', ckRun st l = some st') :
    ∃ x, ifaceOf? id st l = some x ∧ x.id = id := by
  obtain ⟨st', h⟩ := hrun
  obtain ⟨xs, k, hc⟩ := run_checkSeq l st st' h
  exact ⟨⟨id, st.C, l, k, st.s, xs, st'.s⟩, by simp [ifaceOf?, hres, hc], rfl⟩

theorem typeNested_complete_of (path : List SeqStep) (k : Nat) (C : Context) (S : List CValType)
    (i : Instr) (hstep : ∃ r, checkInstr atomC tyOkC C S i = some r)
    (IH : ∀ a c, armOf i a = some c → ∀ (path' : List SeqStep) (st₀ : CkSt),
      (∃ st', ckRun st₀ c = some st') → resOk tyOkC st₀.C.toTypeCtx st₀.s = true →
      ∀ y ∈ walk path' 0 [] c, ∃ x ∈ typeWalk path' 0 st₀ [] c, x.id = y.1) :
    ∀ y ∈ nested path k i, ∃ x ∈ typeNested path k C i, x.id = y.1 := by
  intro y hy
  obtain ⟨r, hr⟩ := hstep
  cases i
  case block bt b =>
    obtain ⟨t₁, t₂, hbt, hres, r', hc⟩ := checkInstr_block hr
    simp only [nested] at hy
    simp only [typeNested, hbt]
    exact IH 0 b rfl _ ⟨C.withLabel t₂, t₁, false⟩ (checkSeq_run _ _ _ _ _ hc) hres y hy
  case loop bt b =>
    obtain ⟨t₁, t₂, hbt, hres, r', hc⟩ := checkInstr_loop hr
    simp only [nested] at hy
    simp only [typeNested, hbt]
    exact IH 0 b rfl _ ⟨C.withLabel t₁, t₁, false⟩ (checkSeq_run _ _ _ _ _ hc) hres y hy
  case tryTable bt cs b =>
    obtain ⟨t₁, t₂, hbt, hres, r', hc⟩ := checkInstr_tryTable hr
    simp only [nested] at hy
    simp only [typeNested, hbt]
    exact IH 0 b rfl _ ⟨C.withLabel t₂, t₁, false⟩ (checkSeq_run _ _ _ _ _ hc) hres y hy
  case if_ bt t e =>
    obtain ⟨t₁, t₂, hbt, ⟨hres, r₁, hc₁⟩, ⟨-, r₂, hc₂⟩⟩ := checkInstr_if hr
    simp only [nested, List.mem_append] at hy
    simp only [typeNested, hbt, List.mem_append]
    rcases hy with hy | hy
    · obtain ⟨x, hx, hid⟩ :=
        IH 0 t rfl _ ⟨C.withLabel t₂, t₁, false⟩ (checkSeq_run _ _ _ _ _ hc₁) hres y hy
      exact ⟨x, Or.inl hx, hid⟩
    · obtain ⟨x, hx, hid⟩ :=
        IH 1 e rfl _ ⟨C.withLabel t₂, t₁, false⟩ (checkSeq_run _ _ _ _ _ hc₂) hres y hy
      exact ⟨x, Or.inr hx, hid⟩
  all_goals simp [nested] at hy

/-- **Completeness of the typing walk**: if the checker runs through a sequence, every block of
the sequence gets an interface. -/
theorem typeWalk_complete (path : List SeqStep) (k : Nat) (st : CkSt) (acc : List Instr)
    (is : List Instr) (hrun : ∃ st', ckRun st (acc.reverse ++ is) = some st')
    (hres : resOk tyOkC st.C.toTypeCtx st.s = true) :
    ∀ y ∈ walk path k acc is, ∃ x ∈ typeWalk path k st acc is, x.id = y.1 := by
  intro y hy
  match is with
  | [] =>
    unfold walk at hy
    unfold typeWalk
    split at hy
    · simp at hy
    · rename_i hacc
      simp only [List.mem_singleton] at hy; subst hy
      obtain ⟨x, hx, hid⟩ := ifaceOf?_some ⟨path, k⟩ hres (by simpa using hrun)
      exact ⟨x, by simp [hacc, hx], hid⟩
  | i :: is =>
    unfold walk at hy
    unfold typeWalk
    by_cases hi : isTerminator i = true
    · simp only [hi, ite_true, List.mem_cons, List.mem_append] at hy ⊢
      have hsplit : acc.reverse ++ i :: is = (acc.reverse ++ [i]) ++ is := by simp
      rw [hsplit] at hrun
      obtain ⟨st₂, h₂, hrest⟩ := run_split hrun
      obtain ⟨st₁, h₁, ⟨st₂', h₁₂⟩⟩ := run_split ⟨st₂, h₂⟩
      rcases hy with rfl | hy | hy
      · obtain ⟨x, hx, hid⟩ := ifaceOf?_some ⟨path, k⟩ hres ⟨st₂, h₂⟩
        exact ⟨x, Or.inl (by simp [hx]), hid⟩
      · have hs : ckStep st₁ i = some st₂' := by simpa [ckRun] using h₁₂
        obtain ⟨x, hx, hid⟩ := typeNested_complete_of path k st₁.C _ i (ckStep_some hs)
          (fun a c hc path' st₀ hr0 hres0 y' hy' =>
            have := armOf_size hc
            typeWalk_complete path' 0 st₀ [] c (by simpa using hr0) hres0 y' hy') y hy
        exact ⟨x, Or.inr (Or.inl (by rw [h₁]; exact hx)), hid⟩
      · obtain ⟨x, hx, hid⟩ := typeWalk_complete path (k + 1) st₂ [] is (by simpa using hrest)
          (ckRun_res _ h₂ hres) y hy
        exact ⟨x, Or.inr (Or.inr (by rw [h₂]; exact hx)), hid⟩
    · simp only [hi] at hy ⊢
      exact typeWalk_complete path k st (i :: acc) is (by simpa using hrun) hres y hy
termination_by sizeOf is
decreasing_by
  all_goals first | (simp_wf; done) | (simp_wf; omega)

end Silmaril.Wasm.Cfg.Proofs.BlockTyping