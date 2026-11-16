module

public import Silmaril.Proofs.Wasm.Cfg.RegionDiv

@[expose] public section

/-! # Termination of non-control instructions (`AtomTerm`)

Strong normalisation (`Acc` of the reversed step relation) of `vals vs ++ [plain i]` for every
non-control `i`, every profile and host. Stuck states are leaves of `Acc`: this is the
absence of infinite reductions, not a claim that a value or trap is reached.

The measure `rank i vs` is the instruction's level, plus, for the bulk instructions
(`fill`/`copy`/`init` of memories, tables and arrays), the count on top of the stack. Every rule
of an instruction rewrites it into code whose instructions have smaller rank (`Good`).
-/

namespace Silmaril.Wasm.Cfg.Proofs.Region

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Numerics Silmaril.Wasm.Validation
open Silmaril.Wasm.SingleThreaded (Det.famOf)

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

variable {H : Type} {P : Profile} {host : HostSemantics H}

/-- Expansion level of an instruction. -/
def lvl : Instr → Nat
  | .localTee _ | .structNewDefault _ | .arrayNew _ | .arrayNewDefault _ | .arrayNewData .. 
  | .arrayNewElem .. => 1
  | .memoryFill _ | .memoryCopy .. | .memoryInit .. | .tableFill _ | .tableCopy .. | .tableInit ..
  | .arrayFill _ | .arrayCopy .. | .arrayInitData .. | .arrayInitElem .. => 2
  | _ => 0

/-- The integer on top of the stack (the count of a bulk instruction). -/
def cnt (vs : List Val) : Nat :=
  match vs.getLast? with
  | some (.num ⟨.int _, b⟩) => b.toNat
  | _ => 0

def rank (i : Instr) (vs : List Val) : Nat := lvl i + if lvl i = 2 then cnt vs else 0

abbrev SNc (P : Profile) (host : HostSemantics H) (c : Config H) : Prop :=
  Acc (fun a b => Step P host b a) c

/-- Code all of whose reductions terminate, by construction from terminating atoms. -/
inductive Good (P : Profile) (host : HostSemantics H) : List Admin → Prop where
  | allv {X : List Admin} (h : ∀ x ∈ X, x.val? ≠ none) : Good P host X
  | trap {X : List Admin} (h : TrapForm X) : Good P host X
  | cons {w : List Val} {p : Instr} {Z : List Admin}
      (hA : ∀ s f, SNc P host (⟨s, f, vals w ++ [.plain p]⟩ : Config H))
      (hk : Det.famOf (.plain p) ≠ .control) (hZ : ∀ w', Good P host (vals w' ++ Z)) :
      Good P host (vals w ++ .plain p :: Z)

theorem sn_trapForm {c : Config H} (ht : TrapForm c.code) : SNc P host c := by
  by_contra h
  exact trapForm_not_div ht (InfiniteTrace.iff_not_acc.2 h)

theorem sn_allv {c : Config H} (h : ∀ x ∈ c.code, x.val? ≠ none) : SNc P host c := by
  refine ⟨_, fun c' hs => ?_⟩
  rcases c with ⟨s, f, x⟩
  have := SingleThreaded.Det.eq_vals_of_all h
  dsimp only at this
  rw [this] at hs
  exact (Step.not_vals hs).elim

/-- Sequencing terminating code. -/
theorem sn_seq {Z : List Admin} (hZ : ∀ w s f, SNc P host (⟨s, f, vals w ++ Z⟩ : Config H)) :
    ∀ {c : Config H}, SNc P host c → AtomInv c.code →
      SNc P host ⟨c.store, c.frame, c.code ++ Z⟩ := by
  intro c hc
  induction hc with
  | intro c _ ih =>
  intro hinv
  refine ⟨_, fun c' hs => ?_⟩
  rcases c with ⟨s, f, A⟩
  dsimp only at hinv hs ⊢
  by_cases hv : A.all Admin.isVal = true
  · obtain ⟨W, rfl⟩ := Sim.exists_vals_of_all hv
    exact (hZ W s f).inv hs
  · rcases hinv with hS | ht
    · obtain ⟨A', hA', he⟩ := seq_step hS (by simpa using hv) hs
      have := ih _ hA' (atomInv_step hA' (.inl hS))
      rcases c' with ⟨_, _, _⟩; dsimp only at he; subst he; exact this
    · obtain ⟨ws, rest, rfl⟩ := ht
      exact (sn_trapForm (c := ⟨s, f, vals ws ++ .trap :: (rest ++ Z)⟩) ⟨ws, rest ++ Z, rfl⟩).inv
        (by simpa using hs)

theorem good_sn {X : List Admin} (h : Good P host X) : ∀ s f, SNc P host (⟨s, f, X⟩ : Config H) := by
  induction h with
  | allv h => exact fun s f => sn_allv h
  | trap h => exact fun s f => sn_trapForm h
  | @cons w p Z hA hk _ ih =>
    intro s f
    have := sn_seq (Z := Z) (fun w' s f => ih w' s f) (hA s f) (.inl (by
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact .inl (SingleThreaded.Det.mem_vals hx)
      · exact .inr ⟨p, rfl, hk⟩))
    simpa using this

/-- Simple code of terminating atoms, then good code. -/
theorem good_simple {T : List Admin} (hT : ∀ w, Good P host (vals w ++ T)) :
    ∀ {X : List Admin}, (∀ x ∈ X, x.val? ≠ none ∨ ∃ p, x = .plain p ∧
        Det.famOf (.plain p) ≠ .control ∧ ∀ w s f, SNc P host (⟨s, f, vals w ++ [.plain p]⟩ : Config H)) →
      ∀ ws, Good P host (vals ws ++ X ++ T)
  | [], _, ws => by simpa using hT ws
  | x :: X, hX, ws => by
    have ih := good_simple hT (X := X) (fun y hy => hX y (by simp [hy]))
    rcases hX x (by simp) with hv | ⟨p, rfl, hk, hp⟩
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hv
      have := ih (ws ++ [v])
      rw [Admin.eq_of_val? hv]; simpa [vals] using this
    · have := Good.cons (P := P) (host := host) (w := ws) (Z := X ++ T) (hp ws) hk
        (fun w' => by simpa using ih w')
      simpa using this

/-! ## Ranks of expansions -/

theorem cnt_append {w L : List Val} (h : L ≠ []) : cnt (w ++ L) = cnt L := by
  have e : (w ++ L).getLast? = L.getLast? := by
    rw [List.getLast?_append]
    cases hL : L.getLast? <;> simp_all [List.getLast?_eq_none_iff]
  simp only [cnt, e]

theorem filterMap_vals (us : List Val) : (vals us).filterMap Admin.val? = us := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [vals] at ih ⊢; try exact ih

theorem cnt_of_vals {us : List Val} {L : List Admin} (h : vals us = L) :
    cnt us = cnt (L.filterMap Admin.val?) := by
  rw [← h, filterMap_vals]

/-- Values, or non-control instructions of level `0`. -/
def NonRec (x : Admin) : Prop :=
  x.val? ≠ none ∨ ∃ p, x = .plain p ∧ Det.famOf (.plain p) ≠ .control ∧ lvl p = 0

theorem good_nonrec
    (IH0 : ∀ p w s f, lvl p = 0 → Det.famOf (.plain p) ≠ .control →
      SNc P host (⟨s, f, vals w ++ [.plain p]⟩ : Config H))
    {X T : List Admin} (hX : ∀ x ∈ X, NonRec x) (hT : ∀ w, Good P host (vals w ++ T))
    (ws : List Val) : Good P host (vals ws ++ X ++ T) :=
  good_simple hT (fun x hx => (hX x hx).imp id
    (fun ⟨p, h1, h2, h3⟩ => ⟨p, h1, h2, fun w s f => IH0 p w s f h3 h2⟩)) ws

theorem good_tail {Lit : List Admin} {q : Instr} {m : Nat} (hL : ∀ x ∈ Lit, x.val? ≠ none)
    (hne : Lit ≠ []) (hm : cnt (Lit.filterMap Admin.val?) = m)
    (hk : Det.famOf (.plain q) ≠ .control)
    (IHq : ∀ w s f, cnt w = m → SNc P host (⟨s, f, vals w ++ [.plain q]⟩ : Config H)) :
    ∀ w, Good P host (vals w ++ (Lit ++ [.plain q])) := by
  intro w
  have hL' := SingleThreaded.Det.eq_vals_of_all hL
  have hne' : Lit.filterMap Admin.val? ≠ [] := by
    intro h0; rw [h0] at hL'; exact hne (by simpa [vals] using hL')
  rw [hL']
  have := Good.cons (P := P) (host := host) (w := w ++ Lit.filterMap Admin.val?) (p := q) (Z := [])
    (fun s f => IHq _ s f (by rw [cnt_append hne', hm])) hk
    (fun w' => .allv (fun x hx => by simpa using SingleThreaded.Det.mem_vals (by simpa using hx)))
  simpa using this

theorem rank_pos {i : Instr} {vs : List Val} (h : 1 ≤ lvl i) : 1 ≤ rank i vs := by
  unfold rank; omega

theorem ih0_of {i : Instr} {vs : List Val}
    (IH : ∀ p w, rank p w < rank i vs → Det.famOf (.plain p) ≠ .control →
      ∀ s f, SNc P host (⟨s, f, vals w ++ [.plain p]⟩ : Config H)) (hi : 1 ≤ lvl i) :
    ∀ p w s f, lvl p = 0 → Det.famOf (.plain p) ≠ .control →
      SNc P host (⟨s, f, vals w ++ [.plain p]⟩ : Config H) := fun p w s f hp hk =>
  IH p w (by
    have h1 := rank_pos (vs := vs) hi
    have h0 : rank p w = 0 := by simp [rank, hp]
    omega) hk s f

set_option hygiene false in
/-- Non-recursive members and values. -/
local macro "nonrec_tac" : tactic => `(tactic| (
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
    List.append_nil] at hx
  repeat' (rcases hx with hx | hx)
  all_goals first
    | exact .inl (SingleThreaded.Det.mem_vals ‹_›)
    | (left; simp [constI32, aconst, arrRef]; done)
    | (right; refine ⟨_, rfl, ?_, ?_⟩ <;> simp [Det.famOf, lvl, store8, load8u]; done)
    | (obtain ⟨r, -, rfl⟩ := List.mem_map.1 ‹_›; left; simp [Admin.val?]; done)))

set_option hygiene false in
local macro "nonrec_vals" : tactic => `(tactic| (
  intro x hx
  simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  repeat' (rcases hx with hx | hx)
  all_goals simp [constI32, aconst, arrRef]))

set_option hygiene false in
/-- A level-1 instruction: its expansion has only values and level-0 instructions. -/
local macro "lvl1_case" : tactic => `(tactic| (
  have hi := congrArg (fun c : Config H => c.code.getLast?) hc
  simp at hi
  subst hi
  have IH0 := ih0_of IH (by simp [lvl])
  dsimp only
  apply (show ∀ X, Good P host (vals ws ++ X ++ []) → Good P host (vals ws ++ X) from
    fun X h => by simpa using h)
  refine good_nonrec IH0 ?_ (fun w => .allv (fun x hx => by
    simpa using SingleThreaded.Det.mem_vals (by simpa using hx))) ws
  nonrec_tac))

theorem bv_pred_lt {w : Nat} {n : BitVec w} (h : n ≠ 0) : (n - 1).toNat < n.toNat := by
  have h0 : 0 < n.toNat := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
    · exact absurd (BitVec.eq_of_toNat_eq (by simp [h0])) h
    · exact h0
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with rfl | hw
    · exact absurd (Subsingleton.elim (α := BitVec 0) n 0) h
    · exact hw
  have h2 : 1 < 2 ^ w := Nat.one_lt_pow (by omega) (by norm_num)
  have h1 : (1 : BitVec w).toNat = 1 := by
    simp [Nat.mod_eq_of_lt h2]
  have hle : (1 : BitVec w) ≤ n := by rw [BitVec.le_def, h1]; omega
  rw [BitVec.toNat_sub_of_le hle, h1]
  omega

theorem rank_rec_lt {i q : Instr} {ws us w : List Val} (hi : lvl i = 2) (hq : lvl q = 2)
    (hus : us ≠ []) (hlt : cnt w < cnt us) : rank q w < rank i (ws ++ us) := by
  simp only [rank, hi, hq, ↓reduceIte, cnt_append hus]
  omega

set_option hygiene false in
/-- A bulk instruction: its expansion is level-0 code `X`, then the same instruction on the
literal operands `Lit` with a smaller count. -/
local macro "rec_case" X:term "," Lit:term : tactic => `(tactic| (
  have hi := congrArg (fun c : Config H => c.code.getLast?) hc
  have hu := congrArg (fun c : Config H => c.code.dropLast) hc
  simp at hi
  simp only [List.dropLast_concat, List.dropLast] at hu
  have hus : us ≠ [] := by rintro rfl; simp [vals] at hu
  have hcnt : cnt us = n.toNat := by
    rw [cnt_of_vals hu]; simp [cnt, aconst, arrRef]; try rfl
  have hl : lvl i = 2 := by rw [hi]; rfl
  have hk : Det.famOf (.plain i) ≠ .control := by rw [hi]; simp [Det.famOf]
  have IH0 := ih0_of IH (by omega)
  dsimp only
  have := good_nonrec IH0 (X := $X) (T := $Lit ++ [.plain i]) (by nonrec_tac)
    (good_tail (Lit := $Lit) (by nonrec_vals) (by simp) rfl hk
      (fun w s f hw => IH _ w (rank_rec_lt hl hl hus (by
        rw [hw, hcnt]; simp [cnt, aconst, arrRef]
        exact bv_pred_lt ‹_›)) hk s f)) ws
  simpa [hi] using this))

set_option hygiene false in
local macro "fin_tac" : tactic => `(tactic| first
  | (exact Good.trap ⟨ws, [], rfl⟩)
  | (refine Good.allv (fun x hx => ?_)
     simp only [List.mem_append, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
       List.append_nil] at hx
     repeat' (rcases hx with hx | hx)
     all_goals first
       | exact SingleThreaded.Det.mem_vals ‹_›
       | (simp [Admin.val?, constI32, Val.i32, Val.toAdmin, aconst]; done)
       | (simp; done)
       | (obtain ⟨r, -, rfl⟩ := List.mem_map.1 ‹_›; simp [Admin.val?])))

theorem fam_good {s : Store H} {f : Frame} {us ws : List Val} {i : Instr} {c₀ : Config H}
    (hF : FamStep P ⟨s, f, vals us ++ [.plain i]⟩ c₀)
    (IH : ∀ p w, rank p w < rank i (ws ++ us) → Det.famOf (.plain p) ≠ .control →
      ∀ s f, SNc P host (⟨s, f, vals w ++ [.plain p]⟩ : Config H)) :
    Good P host (vals ws ++ c₀.code) := by
  generalize hc : (⟨s, f, vals us ++ [.plain i]⟩ : Config H) = c at hF
  cases hF with
  | parametric h => cases h <;> fin_tac
  | numeric h => cases h <;> fin_tac
  | vector h => cases h <;> fin_tac
  | «variable» h =>
    cases h <;> try fin_tac
    lvl1_case
  | table h =>
    cases h <;> try fin_tac
    case fillSucc =>
      rename_i x a i0 n v ta ti _ _ _
      rec_case [aconst a i0, v.toAdmin, .plain (.tableSet x)], [aconst a (i0 + 1), v.toAdmin, aconst a (n - 1)]
    case copyLe =>
      rename_i x₁ x₂ a₁ a₂ a' i₁ i₂ n _ _ _ _ _ _ _ _ _
      rec_case [aconst a₁ i₁, aconst a₂ i₂, .plain (.tableGet x₂), .plain (.tableSet x₁)], [aconst a₁ (i₁ + 1), aconst a₂ (i₂ + 1), aconst a' (n - 1)]
    case copyGt =>
      rename_i x₁ x₂ a₁ a₂ a' i₁ i₂ n _ _ _ _ _ _ _ _ _
      rec_case [aconst a₁ (i₁ + BitVec.ofNat _ n.toNat - 1), aconst a₂ (i₂ + BitVec.ofNat _ n.toNat - 1), .plain (.tableGet x₂), .plain (.tableSet x₁)], [aconst a₁ i₁, aconst a₂ i₂, aconst a' (n - 1)]
    case initSucc =>
      rename_i x y a i0 j n _ _ _ _ r _ _ _ _ _
      rec_case [aconst a i0, .ref r, .plain (.tableSet x)], [aconst a (i0 + 1), constI32 (j + 1), constI32 (n - 1)]

  | memory h =>
    cases h <;> try fin_tac
    case fillSucc =>
      rename_i x a i0 n v _ _ _ _ _
      rec_case [aconst a i0, v.toAdmin, store8 x], [aconst a (i0 + 1), v.toAdmin, aconst a (n - 1)]
    case copyLe =>
      rename_i x₁ x₂ a₁ a₂ a' i₁ i₂ n _ _ _ _ _ _ _ _ _
      rec_case [aconst a₁ i₁, aconst a₂ i₂, load8u x₂, store8 x₁], [aconst a₁ (i₁ + 1), aconst a₂ (i₂ + 1), aconst a' (n - 1)]
    case copyGt =>
      rename_i x₁ x₂ a₁ a₂ a' i₁ i₂ n _ _ _ _ _ _ _ _ _
      rec_case [aconst a₁ (i₁ + BitVec.ofNat _ n.toNat - 1), aconst a₂ (i₂ + BitVec.ofNat _ n.toNat - 1), load8u x₂, store8 x₁], [aconst a₁ i₁, aconst a₂ i₂, aconst a' (n - 1)]
    case initSucc =>
      rename_i x y a i0 j n _ _ _ _ byte _ _ _ _ _
      rec_case [aconst a i0, constI32 (BitVec.ofNat 32 byte.toNat), store8 x], [aconst a (i0 + 1), constI32 (j + 1), constI32 (n - 1)]
  | reference h => cases h <;> fin_tac
  | aggregate h =>
    cases h <;> try fin_tac
    case structNewDefault => lvl1_case
    case arrayNew => lvl1_case
    case arrayNewDefault => lvl1_case
    case arrayNewElemAlloc => lvl1_case
    case arrayNewDataNum => lvl1_case
    case arrayFillSucc =>
      rename_i x i0 n v a _ _ _ _
      rec_case [arrRef a, constI32 i0, v.toAdmin, .plain (.arraySet x)], [arrRef a, constI32 (i0 + 1), v.toAdmin, constI32 (n - 1)]
    case arrayCopyLe =>
      rename_i x₁ x₂ i₁ i₂ n a₁ a₂ _ _ _ ft₂ _ _ _ _ _ _ _
      rec_case [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂), .plain (.arraySet x₁)], [arrRef a₁, constI32 (i₁ + 1), arrRef a₂, constI32 (i₂ + 1), constI32 (n - 1)]
    case arrayCopyGt =>
      rename_i x₁ x₂ i₁ i₂ n a₁ a₂ _ _ _ ft₂ _ _ _ _ _ _ _
      rec_case [arrRef a₁, constI32 (i₁ + n - 1), arrRef a₂, constI32 (i₂ + n - 1), .plain (.arrayGet (storageSx (fieldStorage ft₂)) x₂), .plain (.arraySet x₁)], [arrRef a₁, constI32 i₁, arrRef a₂, constI32 i₂, constI32 (n - 1)]
    case arrayInitElemSucc =>
      rename_i x y i0 j n a _ _ _ r _ _ _ _ _
      rec_case [arrRef a, constI32 i0, .ref r, .plain (.arraySet x)], [arrRef a, constI32 (i0 + 1), constI32 (j + 1), constI32 (n - 1)]
    case arrayInitDataNum =>
      rename_i x y i0 j n a _ _ _ ft _ v _ _ _ _ _ _ _
      rec_case [arrRef a, constI32 i0, v.toAdmin, .plain (.arraySet x)], [arrRef a, constI32 (i0 + 1), constI32 (j + BitVec.ofNat 32 (storageSize (fieldStorage ft) / 8)), constI32 (n - 1)]


/-- **Every non-control instruction terminates** (strong normalisation; stuck states are
leaves), in every profile and for every host. -/
theorem atom_term : AtomTerm P host := by
  suffices h : ∀ n i vs, rank i vs = n → Det.famOf (.plain i) ≠ .control →
      ∀ (s : Store H) (f : Frame), SNc P host (⟨s, f, vals vs ++ [.plain i]⟩ : Config H) from
    fun s f vs i hk => h _ i vs rfl hk s f
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i vs hn hk s f
  refine ⟨_, fun c hs => ?_⟩
  obtain ⟨ws, us, c₀, rfl, h₀, rfl⟩ := Step.noncontrol_vals_inv hk hs
  exact good_sn (fam_good (ws := ws) h₀ (fun p w hlt hk' s f => ih _ (hn ▸ hlt) p w rfl hk' s f))
    _ _

end Silmaril.Wasm.Cfg.Proofs.Region
