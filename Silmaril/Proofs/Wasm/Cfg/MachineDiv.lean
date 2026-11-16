module

public import Silmaril.Proofs.Wasm.Cfg.MachineComplete
import Silmaril.Proofs.Wasm.Cfg.RegionDiv
import Silmaril.Foundations.InfiniteTrace

@[expose] public section

/-!
# Divergence of the block-CFG machine for the region semantics

A diverging region run of a function body (`RunDiv`) is an infinite machine run from its
initial state. Proof: the states that stand (`Rep`) for a diverging code always make progress
(at least one machine step to another such state). Between machine steps the code shrinks, or
stays inside one block.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineDiv

set_option linter.unusedSimpArgs false

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
  Silmaril.Wasm.Cfg.Proofs.MachineComplete

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
  {D : Store H → Nat → List Val → Prop}

theorem div_unfold {s : Store H} {f : Frame} {vs : List Val} {code : List Admin}
    (h : RunDivC P host C D s f vs code) : DivFC P host C D (RunDivC P host C D) s f vs code :=
  Proofs.Region.runDiv_unfold h

theorem div_nil {s : Store H} {f : Frame} {vs : List Val} :
    ¬ RunDivC P host C D s f vs [] := fun h => by cases div_unfold h

theorem div_head_val {s : Store H} {f : Frame} {vs : List Val} {a : Admin} {v : Val}
    {code : List Admin} (h : RunDivC P host C D s f vs (a :: code)) (hv : a.val? = some v) :
    RunDivC P host C D s f (vs ++ [v]) code := by
  cases div_unfold h with
  | val hv' h' => rw [hv] at hv'; cases hv'; exact h'
  | simple hi => rw [val_none_of_noncontrol hi] at hv; cases hv
  | brData hb => rw [brStep_val_none hb] at hv; cases hv
  | _ => simp [Admin.val?] at hv

theorem div_vals {s : Store H} {f : Frame} : ∀ {vs W : List Val},
    ¬ RunDivC P host C D s f vs (vals W)
  | _, [], h => div_nil h
  | _, w :: W, h => div_vals (div_head_val (v := w) (by simpa [vals] using h) (by simp))

theorem div_br {s : Store H} {f : Frame} {vs : List Val} {l : LabelIdx} {code : List Admin} :
    ¬ RunDivC P host C D s f vs (.plain (.br l) :: code) := fun h => by
  cases div_unfold h with
  | simple hi => simp [SingleThreaded.Det.famOf] at hi
  | brData hb => cases hb
  | val hv => simp [Admin.val?] at hv

/-- The machine states standing for a diverging code. -/
def S (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H)
    (D : Store H → Nat → List Val → Prop) (body : Expr) (st : MState H) : Prop :=
  ∃ (lv : Lv H) (s : Store H) (f : Frame) (vs : List Val) (code : List Admin),
    Rep P host C body lv s f vs code st ∧ RunDivC P host C D s f vs code

/-- Progress: at least one machine step to another state standing for a diverging code, or a
finite run to a block whose body reaches a call `D` names. -/
abbrev Prog (P : Profile) (host : HostSemantics H) (C : Abstract.CallRel H)
    (D : Store H → Nat → List Val → Prop) (body : Expr) (st : MState H) : Prop :=
  (∃ st', Relation.TransGen (MStepC P host C body) st st' ∧ S P host C D body st') ∨
    ∃ st', MRun P host C body st st' ∧ BodyCallDiv P host C D body st'

theorem prog_run {body : Expr} {st st₁ : MState H} (h1 : MRun P host C body st st₁)
    (h : Prog P host C D body st₁) : Prog P host C D body st := by
  rcases h with ⟨st₂, h2, hS⟩ | ⟨st₂, h2, hB⟩
  · exact .inl ⟨st₂, Relation.TransGen.trans_right h1 h2, hS⟩
  · exact .inr ⟨st₂, h1.trans h2, hB⟩

theorem term_call {c : List Instr} {i : Nat} {sg : Segment} {x : FuncIdx}
    (hsg : (segment c)[i]? = some sg) (ht : sg.term = some (.call x)) : False := by
  have hseg := segment_isSegmentation c
  have hwf := (hseg.2.1 sg (List.mem_of_getElem? hsg)).2 (.call x) (by simp [ht])
  simp [isTerminator] at hwf

theorem prog_entry_step {body : Expr} {st : MState H} {p : List SeqStep} {c : List Instr}
    {i : Nat} {ls : List LFrame} {s : Store H} {f : Frame} {vs : List Val}
    (hc : seqAt body p = some c) (hs : MStepC P host C body st (goto (entry body p i) p.length ls vs s f))
    (hd : RunDivC P host C D s f vs (expression (restAt c i))) : Prog P host C D body st := by
  have hr := rep_entry (P := P) (host := host) (C := C) (s := s) (f := f) i ls vs [] hc
  exact .inl ⟨_, .single hs, _, _, _, _, _, by simpa using hr, hd⟩


/-- **Progress at a block's terminator.** -/
theorem prog_term {body : Expr} {p : List SeqStep} {ls : List LFrame} {c : List Instr} {i : Nat}
    {sg : Segment} {t : Instr} {stk₀ vs : List Val} {s₀ s : Store H} {f₀ f : Frame}
    (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg) (ht : sg.term = some t)
    (hpre : RunC P host C s₀ f₀ stk₀ (expression sg.body) s f (.normal vs))
    (hd : RunDivC P host C D s f vs (.plain t :: expression (restAt c (i + 1)))) :
    Prog P host C D body ⟨.block ⟨p, i⟩, stk₀, ls, s₀, f₀⟩ := by
  have hb := lookup_of hc hsg
  cases div_unfold hd with
  | val hv => rw [term_val_none hsg ht] at hv; cases hv
  | call => exact (term_call hsg ht).elim
  | callDiv => exact (term_call hsg ht).elim
  | simple hi h₁ =>
    cases term_noncontrol hsg ht hi
    exact (steps_unreachable_not_vals h₁).elim
  | @brIf _ ws k l _ h =>
    by_cases hk : k = 0
    · subst hk
      exact prog_entry_step hc (MStepC.brIfNot hb ht hpre) (by simpa using h)
    · simp only [hk, ↓reduceIte, List.singleton_append] at h
      exact (div_br h).elim
  | @brData _ ws us us' _ X _ hbs h =>
    rcases brStep_X hbs with rfl | ⟨l, rfl⟩
    · exact prog_entry_step hc (MStepC.brDataNot (ws := ws) (us := us) (us' := us') hb ht hpre hbs)
        (by simpa using h)
    · exact (div_br (by simpa using h)).elim
  | @block _ ws us bt b t₁ t₂ _ hbt hm h =>
    have hs := MStepC.enter (ls := ls) (a := 0) hb ht rfl .block hpre (.plain (by intros; simp)) hbt hm
    exact .inl ⟨_, .single hs, _, _, _, _, _, Rep.lab (V := []) (L := ⟨t₂.length, ws, false, false, [], bt⟩)
      hc hsg ht rfl .block rfl (by simp [LoopOk]) (by simp) (rep_arm ls _ us hc hsg ht rfl), h⟩
  | @loop _ ws us bt b t₁ t₂ _ hbt hm h =>
    have hs := MStepC.enter (ls := ls) (a := 0) hb ht rfl .loop hpre (.plain (by intros; simp)) hbt hm
    exact .inl ⟨_, .single hs, _, _, _, _, _, Rep.lab (V := []) (L := ⟨t₁.length, ws, true, false, [], bt⟩)
      hc hsg ht rfl .loop rfl (fun _ => ⟨t₁, t₂, hbt, rfl⟩) (by simp)
      (rep_arm ls _ us hc hsg ht rfl), h⟩
  | @tryTable _ ws us bt cs b t₁ t₂ _ hbt hm h =>
    have hs := MStepC.enter (ls := ls) (a := 0) hb ht rfl .tryTable hpre (.plain (by intros; simp)) hbt hm
    exact .inl ⟨_, .single hs, _, _, _, _, _, Rep.hnd (V := []) (L := ⟨t₂.length, ws, false, true, cs, bt⟩)
      hc hsg ht rfl .tryTable rfl (by simp)
      (Rep.hlab (isLoopAt_kind hc hsg ht .tryTable) rfl (rep_arm ls _ us hc hsg ht rfl)), h⟩
  | @if_ _ ws k bt te ee _ h =>
    cases div_unfold h with
    | val hv => simp [Admin.val?] at hv
    | simple hi => simp [SingleThreaded.Det.famOf] at hi
    | brData hbs => cases hbs
    | @block _ ws' us _ _ t₁ t₂ _ hbt hm h' =>
      by_cases hk : k = 0
      · subst hk
        simp only [↓reduceIte] at h'
        have hs := MStepC.enter (ls := ls) (a := 1) hb ht rfl .if_ hpre CondArm.ifFalse hbt hm
        exact .inl ⟨_, .single hs, _, _, _, _, _,
          Rep.lab (V := []) (L := ⟨t₂.length, ws', false, false, [], bt⟩)
          hc hsg ht rfl .if_ rfl (by simp [LoopOk]) (by simp) (rep_arm ls _ us hc hsg ht rfl), h'⟩
      · simp only [hk, ↓reduceIte] at h'
        have hs := MStepC.enter (ls := ls) (a := 0) hb ht rfl .if_ hpre (CondArm.ifTrue hk) hbt hm
        exact .inl ⟨_, .single hs, _, _, _, _, _,
          Rep.lab (V := []) (L := ⟨t₂.length, ws', false, false, [], bt⟩)
          hc hsg ht rfl .if_ rfl (by simp [LoopOk]) (by simp) (rep_arm ls _ us hc hsg ht rfl), h'⟩


/-- **Progress inside a block**: a diverging rest of block `i` (body suffix `sfx`, after the
prefix `pre` ran from the block's state) makes the machine step. -/
theorem prog_blk {body : Expr} {p : List SeqStep} {ls : List LFrame} {c : List Instr} {i : Nat}
    {sg : Segment} {stk₀ : List Val} {s₀ : Store H} {f₀ : Frame}
    (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg) :
    ∀ (sfx pre : List Instr) (V vs : List Val) (s : Store H) (f : Frame),
      sg.body = pre ++ sfx → (sfx ≠ [] ∨ sg.term.isSome) →
      RunC P host C s₀ f₀ stk₀ (expression pre) s f (.normal (vs ++ V)) →
      RunDivC P host C D s f vs (vals V ++ expression (sfx ++ sg.term.toList ++ restAt c (i + 1))) →
      Prog P host C D body ⟨.block ⟨p, i⟩, stk₀, ls, s₀, f₀⟩ := by
  intro sfx
  induction sfx with
  | nil =>
    intro pre V
    induction V with
    | nil =>
      intro vs s f hbody hne hpre hd
      cases ht : sg.term with
      | none => simp [ht] at hne
      | some t =>
        simp only [ht, Option.toList_some, List.nil_append, vals, List.map_nil,
          List.singleton_append, expression, List.map_cons] at hd
        exact prog_term hc hsg ht (by rw [hbody]; simpa using hpre) (by simpa [expression] using hd)
    | cons w V ih =>
      intro vs s f hbody hne hpre hd
      exact ih (vs ++ [w]) s f hbody hne (by simpa using hpre)
        (div_head_val (by simpa [vals] using hd) (by simp))
  | cons x sfx ihs =>
    intro pre V
    induction V with
    | nil =>
      intro vs s f hbody hne hpre hd
      have hx : isTerminator x = false := (seg_wf hsg).2 x (by simp [hbody])
      -- one body instruction ran: extend the prefix, or fall through
      have adv : ∀ {s₁ : Store H} {f₁ : Frame} {vs₁ : List Val},
          RunC P host C s f vs [.plain x] s₁ f₁ (.normal vs₁) →
          RunDivC P host C D s₁ f₁ vs₁ (expression (sfx ++ sg.term.toList ++ restAt c (i + 1))) →
          Prog P host C D body ⟨.block ⟨p, i⟩, stk₀, ls, s₀, f₀⟩ := by
        intro s₁ f₁ vs₁ hx1 hd1
        have hpre' : RunC P host C s₀ f₀ stk₀ (expression (pre ++ [x])) s₁ f₁ (.normal vs₁) := by
          have hp : RunC P host C s₀ f₀ stk₀ (expression pre) s f (.normal vs) := by simpa using hpre
          simpa [expression] using Proofs.Region.run_append hp (by simp only [ThenC]; exact hx1)
        by_cases hne' : sfx ≠ [] ∨ sg.term.isSome
        · exact ihs (pre ++ [x]) [] vs₁ s₁ f₁ (by simp [hbody]) hne' (by simpa using hpre')
            (by simpa using hd1)
        · have hsfx : sfx = [] := by by_contra h'; exact hne' (Or.inl h')
          have hterm : sg.term = none := by
            cases ht : sg.term with
            | none => rfl
            | some t => exact absurd (Or.inr (by simp [ht])) hne'
          subst hsfx
          have hr : RunC P host C s₀ f₀ stk₀ (expression sg.body) s₁ f₁ (.normal vs₁) := by
            rw [hbody]; simpa using hpre'
          exact prog_entry_step hc (MStepC.fall (b := ⟨p, i⟩) (lookup_of hc hsg) hterm hr)
            (by simpa [hterm] using hd1)
      simp only [vals, List.map_nil, List.nil_append, List.cons_append, expression,
        List.map_cons] at hd
      cases div_unfold hd with
      | val hv h => exact adv (.val hv .nil) (by simpa [expression] using h)
      | simple hi h₁ h => exact adv (.simple hi h₁ .nil) (by simpa [expression] using h)
      | call hfi hty hn hcall hvs h =>
        exact adv (.call hfi hty hn hcall hvs .nil) (by simpa [expression] using h)
      | @callDiv _ ws us x' a fi ps rs _ hfi hty hn hD =>
        exact .inr ⟨_, .refl, ⟨p, i⟩, sg, pre, sfx, x', s, f, ws, us, a, fi, ps, rs, rfl,
          lookup_of hc hsg, hbody, by simpa using hpre, hfi, hty, hn, hD⟩
      | brIf => simp [isTerminator] at hx
      | brData hbs => cases hbs <;> simp [isTerminator] at hx
      | block => simp [isTerminator] at hx
      | loop => simp [isTerminator] at hx
      | if_ => simp [isTerminator] at hx
      | tryTable => simp [isTerminator] at hx
    | cons w V ih =>
      intro vs s f hbody hne hpre hd
      exact ih (vs ++ [w]) s f hbody hne (by simpa using hpre)
        (div_head_val (by simpa [vals] using hd) (by simp))


open Silmaril.Wasm.Cfg.Proofs.Machine in
/-- **Progress from a sequence position.** -/
theorem prog_entry {body : Expr} {q : List SeqStep} {c : List Instr} (i : Nat) (ls : List LFrame)
    {s : Store H} {f : Frame} {vs V : List Val} (hc : seqAt body q = some c)
    (hd : RunDivC P host C D s f vs (vals V ++ expression (restAt c i))) :
    Prog P host C D body (goto (entry body q i) q.length ls (vs ++ V) s f) := by
  unfold entry
  split
  · rename_i hl
    rw [lookup_eq] at hl
    simp only [hc, Option.bind_some, Option.isSome_iff_exists] at hl
    obtain ⟨sg, hsg⟩ := hl
    have hne : sg.body ≠ [] ∨ sg.term.isSome := by
      by_contra hn
      simp only [not_or, ne_eq, not_not, Option.not_isSome_iff_eq_none] at hn
      exact (seg_wf hsg).1 (by simp [Segment.instrs, hn.1, hn.2])
    rw [restAt_cons hsg] at hd
    simp only [goto, depthT, Nat.sub_self, popL]
    exact prog_blk hc hsg sg.body [] V vs s f (by simp) hne .nil
      (by simpa [Segment.instrs] using hd)
  · rename_i hl
    rw [restAt_none hc (by simpa using hl)] at hd
    exact (div_vals (by simpa [expression] using hd)).elim

theorem prog_blkIf {body : Expr} {p : List SeqStep} {ls : List LFrame} {c : List Instr} {i : Nat}
    {sg : Segment} {bt : BlockType} {te ee : List Instr} {k : BitVec 32} {stk₀ ws : List Val}
    {s₀ s : Store H} {f₀ f : Frame}
    (hc : seqAt body p = some c) (hsg : (segment c)[i]? = some sg)
    (ht : sg.term = some (.if_ bt te ee))
    (hpre : RunC P host C s₀ f₀ stk₀ (expression sg.body) s f (.normal (ws ++ [.i32 k]))) :
    ∀ {vs V : List Val}, vs ++ V = ws →
      RunDivC P host C D s f vs
        (vals V ++ .plain (.block bt (if k = 0 then ee else te)) :: expression (restAt c (i + 1))) →
      Prog P host C D body ⟨.block ⟨p, i⟩, stk₀, ls, s₀, f₀⟩
  | vs, w :: V, hstk, hd =>
    prog_blkIf hc hsg ht hpre (vs := vs ++ [w]) (V := V) (by simpa using hstk)
      (div_head_val (by simpa [vals] using hd) (by simp))
  | vs, [], hstk, hd => by
    simp only [List.append_nil] at hstk; subst hstk
    have hb := lookup_of hc hsg
    simp only [vals, List.map_nil, List.nil_append] at hd
    cases div_unfold hd with
    | val hv => simp [Admin.val?] at hv
    | simple hi => simp [SingleThreaded.Det.famOf] at hi
    | brData hbs => cases hbs
    | @block _ ws' us _ _ t₁ t₂ _ hbt hm h' =>
      by_cases hk : k = 0
      · subst hk
        simp only [↓reduceIte] at h'
        have hs := MStepC.enter (ls := ls) (a := 1) hb ht rfl .if_ hpre CondArm.ifFalse hbt hm
        exact .inl ⟨_, .single hs, _, _, _, _, _,
          Rep.lab (V := []) (L := ⟨t₂.length, ws', false, false, [], bt⟩)
          hc hsg ht rfl .if_ rfl (by simp [LoopOk]) (by simp) (rep_arm ls _ us hc hsg ht rfl), h'⟩
      · simp only [hk, ↓reduceIte] at h'
        have hs := MStepC.enter (ls := ls) (a := 0) hb ht rfl .if_ hpre (CondArm.ifTrue hk) hbt hm
        exact .inl ⟨_, .single hs, _, _, _, _, _,
          Rep.lab (V := []) (L := ⟨t₂.length, ws', false, false, [], bt⟩)
          hc hsg ht rfl .if_ rfl (by simp [LoopOk]) (by simp) (rep_arm ls _ us hc hsg ht rfl), h'⟩


theorem size_vals_cons {w : Val} {V : List Val} {X : List Admin} :
    sizeOf (vals V ++ X) < sizeOf (vals (w :: V) ++ X) := by
  simp [vals]

/-- After a label's body branched to it with values `us₂` (`labelBr0`), the machine is at a
state standing for the code after the label (or at the re-entered loop's body). -/
theorem br0_state {body : Expr} {p : List SeqStep} {ls : List LFrame} {c : List Instr}
    {m a : Nat} {sg : Segment} {t : Instr} {c' : List Instr} {L : LFrame} {st : MState H}
    {s₁ : Store H} {f₁ : Frame} {us₁ us₂ : List Val} {code : List Admin}
    (hc : seqAt body p = some c) (hsg : (segment c)[m]? = some sg) (ht : sg.term = some t)
    (harm : armOf t a = some c') (hkind : StructKind t L.bt L.loop L.tryT L.catches)
    (hlo : LoopOk f₁ L) (hn : us₂.length = L.arity)
    (hb : Relation.TransGen (MStepC P host C body) st
      (brTarget body (p ++ [(m, a)]) 0 L (L :: ls) (us₁ ++ us₂) s₁ f₁))
    (hcode : code = expression (restAt c (m + 1)))
    (h : RunDivC P host C D s₁ f₁ L.outer
      (vals us₂ ++ expression (if L.loop then [t] else []) ++ code)) :
    Prog P host C D body st := by
  subst hcode
  have htop : topVals L.arity (us₁ ++ us₂) = us₂ := by simp [topVals, ← hn]
  have hnl := isLoopAt_kind hc hsg ht hkind
  cases hlp : L.loop
  · rw [brTarget_zero_out body p m a L ls _ s₁ f₁ (hnl.trans hlp) hlp, htop] at hb
    simp only [hlp, Bool.false_eq_true, ↓reduceIte, expression, List.map_nil,
      List.append_nil] at h
    have hr := rep_entry (P := P) (host := host) (C := C) (s := s₁) (f := f₁) (m + 1) ls L.outer us₂ hc
    exact .inl ⟨_, hb, _, _, _, _, _, hr, by simpa [expression] using h⟩
  · rw [brTarget_zero_loop body p m a L ls _ s₁ f₁ (hnl.trans hlp) hlp, htop] at hb
    obtain ⟨cb, rfl, -, -⟩ := Proofs.Machine.structKind_loop (hlp ▸ hkind)
    cases kind_arm_loop harm
    simp only [hlp, ↓reduceIte, expression, List.map_cons, List.map_nil,
      List.singleton_append, List.append_assoc] at h
    have hre := Rep.loopRe (P := P) (host := host) (C := C) (s := s₁) (ls := ls) (vs := L.outer)
      (V := us₂) (W := us₂) hc hsg ht hkind hlo rfl hn
    exact .inl ⟨_, hb, _, _, _, _, _, hre, by simpa [expression] using h⟩


/-- **Progress**: a machine state standing for a diverging code steps, at least once, to
another such state. By induction on the size of the code: between machine steps the code
shrinks, except inside one block (`prog_blk`) and on re-entering a loop. -/
theorem prog {body : Expr} : ∀ (n : Nat) (lv : Lv H) (s : Store H) (f : Frame) (vs : List Val)
    (code : List Admin) (st : MState H), sizeOf code < n →
    Rep P host C body lv s f vs code st → RunDivC P host C D s f vs code → Prog P host C D body st
  | 0, _, _, _, _, _, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, lv, s, f, vs, code, st, hn, hr, hd => by
    cases hr with
    | blk hc hsg hbody hne hpre => exact prog_blk hc hsg _ _ _ _ _ _ hbody hne hpre hd
    | blkIf hc hsg ht hpre hstk => exact prog_blkIf hc hsg ht hpre hstk hd
    | fin => exact (div_vals hd).elim
    | @lab p ls c m a sg t c' L inner _ _ vs V _ hc hsg ht harm hkind hT hlo hW hin =>
      cases V with
      | cons w V =>
        exact prog n _ _ _ _ _ _ (by exact Nat.lt_of_lt_of_le size_vals_cons (Nat.le_of_lt_succ hn))
          (Rep.lab hc hsg ht harm hkind hT hlo (by simpa using hW) hin)
          (div_head_val (by simpa [vals] using hd) (by simp))
      | nil =>
        simp only [List.append_nil] at hW; subst hW
        simp only [vals, List.map_nil, List.nil_append] at hd hn
        generalize hvs : L.outer = vs0 at hd
        cases div_unfold hd with
        | val hv => simp [Admin.val?] at hv
        | labelIn h => exact prog n _ _ _ _ _ _ (by simp at hn ⊢; omega) hin h
        | labelNormal hrun h =>
          subst hvs
          have h1 : MRun P host C body st _ := complete hrun _ _ _ _ rfl rfl hin
          rw [show (seqLv body (p ++ [(m, a)]) (L :: ls)).cont _ _ _ = _ from
            seqLv_cont_arm body p m a L ls _ _ _] at h1
          have hre := rep_entry (P := P) (host := host) (C := C) (s := ‹_›) (f := ‹_›) (m + 1) ls
            (L.outer ++ ‹List Val›) [] hc
          exact prog_run h1 (prog n _ _ _ _ _ _ (by simp at hn ⊢; omega) (by simpa using hre) h)
        | labelBr0 hrun hn' h =>
          subst hvs
          have hb := (complete hrun _ _ _ _ rfl rfl hin).1 L (by simp [seqLv])
            (by simp [brVals, seqLv]; omega)
            (loopOk_of_module (Proofs.Machine.run_module hrun) hlo)
          simp only [seqLv, List.nil_append, brVals] at hb
          exact br0_state hc hsg ht harm hkind (loopOk_of_module (Proofs.Machine.run_module hrun) hlo)
            hn' hb rfl h
    | @hnd p ls c m a sg t c' L inner _ _ vs V _ hc hsg ht harm hkind hT hW hin =>
      cases V with
      | cons w V =>
        exact prog n _ _ _ _ _ _ (by exact Nat.lt_of_lt_of_le size_vals_cons (Nat.le_of_lt_succ hn))
          (Rep.hnd hc hsg ht harm hkind hT (by simpa using hW) hin)
          (div_head_val (by simpa [vals] using hd) (by simp))
      | nil =>
        simp only [List.append_nil] at hW; subst hW
        simp only [vals, List.map_nil, List.nil_append] at hd hn
        generalize hvs : L.outer = vs0 at hd
        cases div_unfold hd with
        | val hv => simp [Admin.val?] at hv
        | handlerIn h => exact prog n _ _ _ _ _ _ (by simp at hn ⊢; omega) hin h
        | handlerNormal hrun h =>
          subst hvs
          have h1 : MRun P host C body st _ := complete hrun _ _ _ _ rfl rfl hin
          rw [hlLv_cont] at h1
          have hre := rep_entry (P := P) (host := host) (C := C) (s := ‹_›) (f := ‹_›) (m + 1) ls
            (L.outer ++ ‹List Val›) [] hc
          exact prog_run h1 (prog n _ _ _ _ _ _ (by simp at hn ⊢; omega) (by simpa using hre) h)
    | hlab hnl hloop hin =>
      generalize hvs : ([] : List Val) = vs0 at hd
      cases div_unfold hd with
      | val hv => simp [Admin.val?] at hv
      | labelIn h => exact prog n _ _ _ _ _ _ (by simp at hn ⊢; omega) hin h
      | labelNormal hrun h => exact (div_nil (by simpa using h)).elim
      | labelBr0 hrun hn' h => exact (div_vals (by simpa [expression] using h)).elim
    | @loopRe p ls c m sg bt b L _ _ vs V W hc hsg ht hkind hlo hW hWl =>
      cases V with
      | cons w V =>
        exact prog n _ _ _ _ _ _ (by exact Nat.lt_of_lt_of_le size_vals_cons (Nat.le_of_lt_succ hn))
          (Rep.loopRe hc hsg ht hkind hlo (by simpa using hW) hWl)
          (div_head_val (by simpa [vals] using hd) (by simp))
      | nil =>
        simp only [List.append_nil] at hW; subst hW
        simp only [vals, List.map_nil, List.nil_append] at hd hn
        generalize hvs : L.outer ++ W = vs0 at hd
        cases div_unfold hd with
        | val hv => simp [Admin.val?] at hv
        | simple hi => simp [SingleThreaded.Det.famOf] at hi
        | brData hbs => cases hbs
        | @loop _ ws us _ _ t₁ t₂ _ hbt hm h =>
          have hL : L.loop = true ∧ L.bt = bt ∧ L.tryT = false ∧ L.catches = [] := by
            generalize hl : L.loop = lp at hkind
            generalize hb : L.bt = bb at hkind
            generalize hy : L.tryT = ty at hkind
            generalize hcs : L.catches = cc at hkind
            cases hkind; exact ⟨rfl, rfl, rfl, rfl⟩
          obtain ⟨hlp, hbb, hty, hcc⟩ := hL
          obtain ⟨t₁', t₂', hbt', hlen⟩ := hlo hlp
          rw [hbb, hbt] at hbt'
          simp only [Option.some.injEq, Prod.mk.injEq] at hbt'
          obtain ⟨rfl, rfl⟩ := hbt'
          have hl2 : us.length = W.length := by rw [hm, hlen, hWl]
          obtain ⟨rfl, rfl⟩ := List.append_inj' hvs hl2.symm
          have hin := rep_arm (P := P) (host := host) (C := C) (s := s) (f := f) (a := 0) ls L W hc hsg ht rfl
          rw [hlen] at h
          generalize hvs2 : L.outer = vs1 at h
          cases div_unfold h with
          | val hv => simp [Admin.val?] at hv
          | labelIn h' =>
            have := prog_entry (P := P) (host := host) (body := body) 0 (L :: ls) (s := s) (f := f)
              (vs := []) (V := W) (seqAt_arm (a := 0) hc hsg ht rfl)
              (by simpa [Proofs.Machine.restAt_zero] using h')
            simpa using this
          | labelNormal hrun h' =>
            subst hvs2
            have h1 : MRun P host C body _ _ := complete hrun _ _ _ _ rfl rfl hin
            rw [show (seqLv body (p ++ [(m, 0)]) (L :: ls)).cont _ _ _ = _ from
              seqLv_cont_arm body p m 0 L ls _ _ _] at h1
            have hre := rep_entry (P := P) (host := host) (C := C) (s := ‹_›) (f := ‹_›) (m + 1) ls
              (L.outer ++ ‹List Val›) [] hc
            exact prog_run h1 (prog n _ _ _ _ _ _ (by simp at hn ⊢; omega) (by simpa using hre) h')
          | labelBr0 hrun hn' h' =>
            subst hvs2
            have hlo' := loopOk_of_module (Proofs.Machine.run_module hrun) hlo
            have hb := (complete hrun _ _ _ _ rfl rfl hin).1 L (by simp [seqLv])
              (by simp [brVals, seqLv]; omega) hlo'
            simp only [seqLv, List.nil_append, brVals] at hb
            exact br0_state hc hsg ht rfl hkind hlo' hn' hb rfl
              (by rw [hlp]; simpa using h')

end Silmaril.Wasm.Cfg.Proofs.MachineDiv

namespace Silmaril.Wasm.Cfg.Proofs.MachineDiv

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.Region
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Cfg.Proofs.MachineComplete

variable {H : Type} {P : Profile} {host : HostSemantics H} {C : Abstract.CallRel H}
  {D : Store H → Nat → List Val → Prop}

/-- **States standing for a diverging code diverge as machine states**: an infinite run, or a
finite run to a block whose body reaches a call `D` names. -/
theorem mdivC_of_S {body : Expr} {st : MState H} (h : S P host C D body st) :
    MDivC P host C D body st := by
  classical
  by_cases hb : ∃ st', MRun P host C body st st' ∧ BodyCallDiv P host C D body st'
  · exact .inr hb
  refine .inl (InfiniteTrace.coinduct
    (fun a => (∃ b, Relation.ReflTransGen (MStepC P host C body) a b ∧ S P host C D body b) ∧
      ¬ ∃ st', MRun P host C body a st' ∧ BodyCallDiv P host C D body st')
    ?_ ⟨⟨st, .refl, h⟩, hb⟩)
  rintro a ⟨⟨b, hab, hb⟩, hna⟩
  rcases hab.cases_head with rfl | ⟨d, had, hdb⟩
  · obtain ⟨lv, s, f, vs, code, hr, hd⟩ := hb
    rcases prog (sizeOf code + 1) lv s f vs code a (Nat.lt_succ_self _) hr hd with
      ⟨c, hac, hc⟩ | hB
    · obtain ⟨d, had, hdc⟩ := Relation.TransGen.head'_iff.mp hac
      exact ⟨d, had, ⟨c, hdc, hc⟩, fun ⟨st', h1, h2⟩ => hna ⟨st', .head had h1, h2⟩⟩
    · exact (hna hB).elim
  · exact ⟨d, had, ⟨b, hdb, hb⟩, fun ⟨st', h1, h2⟩ => hna ⟨st', .head had h1, h2⟩⟩

/-- **Divergence from the CFG entry, with calls**: a diverging region run of a function body
(`RunDivC`) is machine divergence (`MDivC`) from its initial state. -/
theorem run_divC_initial {body : Expr} {s : Store H} {f : Frame}
    (h : RunDivC P host C D s f [] (expression body)) :
    MDivC P host C D body (initial body s f) := by
  have hinit : initial body s f = goto (entry body [] 0) ([] : List SeqStep).length [] [] s f := by
    simp [initial, goto, popL, cfgEntry]
  have hrep := rep_entry (P := P) (host := host) (C := C) (body := body) (s := s) (f := f) 0 [] [] []
    (q := []) (c := body) rfl
  simp only [Proofs.Machine.restAt_zero, vals, List.map_nil, List.nil_append] at hrep
  rw [hinit]
  exact mdivC_of_S ⟨_, _, _, _, _, hrep, h⟩

/-- **Divergence from the CFG entry**: a diverging region run of a function body is an infinite
machine run from its initial state. -/
theorem run_div_initial {body : Expr} {s : Store H} {f : Frame}
    (h : RunDiv P host s f [] (expression body)) :
    InfiniteTrace (MStep P host body) (initial body s f) := by
  rcases run_divC_initial h with h | ⟨_, _, hB⟩
  · exact h
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hD⟩ := hB
    exact hD.elim

end Silmaril.Wasm.Cfg.Proofs.MachineDiv
