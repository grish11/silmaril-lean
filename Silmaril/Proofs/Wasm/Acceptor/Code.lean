module

public import Silmaril.Wasm.Acceptor.Code.Defs
public import Silmaril.Wasm.Logic.Hoare.Thms

@[expose] public section

/-!
# The acceptor kit: code and instance facts, and call rules (proofs)

* `ibeq_sound`, `ibeqs_sound`: the Boolean code comparison is sound;
* `fn_of_fnOk`: a kernel-checked `(List.range n).all (fnOk S m mi tys)` gives, for each `j < n`,
  the function instance, the module function and the type, with the code, the module instance
  and the type agreeing;
* `w_call`: `call j` of a function with a valid specification, as a rule of the every-run
  logic; `w_callVoid`, `w_callI32`: its readings for a function that returns nothing, or one
  `i32`, in a store satisfying a given predicate.

A Silmaril addition; the rules are those of the LRAT and Farkas acceptors.
-/

namespace Silmaril.Proofs.Wasm.Acceptor

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)
open Silmaril.Wasm.Acceptor

/-! ## Comparing code -/

theorem ibeq_sound (a b : Instr) : ibeq a b = true → a = b := by
  apply ibeq.induct (motive_1 := fun a b => ibeq a b = true → a = b)
    (motive_2 := fun as bs => ibeqs as bs = true → as = bs)
  all_goals
    intros
    simp_all [ibeq, ibeqs]

theorem ibeqs_sound : ∀ (as bs : List Instr), ibeqs as bs = true → as = bs
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [ibeqs, Bool.and_eq_true] at h
    rw [ibeq_sound a b h.1, ibeqs_sound as bs h.2]
  | [], _ :: _, h => by simp [ibeqs] at h
  | _ :: _, [], h => by simp [ibeqs] at h

/-- **The instance facts of one function**, from the kernel check of all of them. -/
theorem fn_of_fnOk {H : Type} {S : Store H} {m : Module} {mi : ModuleInst} {tys : List CCompType}
    {n : Nat} (h : (List.range n).all (fnOk S m mi tys) = true) {j : Nat} (hj : j < n) :
    ∃ (fi : FuncInst H) (f : Func) (ty : CCompType),
      S.funcs[j]? = some fi ∧ m.funcs[j]? = some f ∧ tys[j]? = some ty ∧
      fi.code = .wasm f ∧ fi.module = mi ∧ Expand fi.type ty := by
  have h := List.all_eq_true.1 h j (List.mem_range.2 hj)
  unfold fnOk at h
  split at h
  · rename_i fi f ty hfi hf hty
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hc, hm⟩, he⟩ := h
    refine ⟨fi, f, ty, hfi, hf, hty, ?_, hm, Expand.iff.2 he⟩
    unfold codeMatches at hc
    split at hc
    · rename_i g hg
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨hb, hl⟩, ht⟩ := hc
      rw [hg]
      have hb' := ibeqs_sound _ _ hb
      cases g; cases f
      simp_all
    · cases hc
  · cases h

/-! ## Call rules -/

variable {H : Type} {P : Profile} {host : HostSemantics H} {s : Store H} {rest : List Admin}
  {Q : Post H}

theorem callf_toNat {j : Nat} (hj : j < 2 ^ 32) :
    (⟨⟨j % 2 ^ 32, Nat.mod_lt _ (by decide)⟩⟩ : FuncIdx).toNat = j := by
  simp [Idx.toNat]; omega

/-- **`call j`** of a function with a valid specification, as a rule of the every-run logic. -/
theorem w_call {f : Frame} {j a : Nat} {fi : FuncInst H} {S : FSpec H} {vs₀ args : List Val}
    (hj : j < 2 ^ 32) (hx : f.module.funcs[j]? = some a) (hf : s.funcs[a]? = some fi)
    (hS : FSpecValid P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, callPost f vs₀ (S.post s args) s' f o → seqPost P host rest Q s' f o) :
    HWP P host s f (vals (vs₀ ++ args) ++ .plain (callf j) :: rest) Q := by
  intro n
  cases n with
  | zero => trivial
  | succ n =>
    exact Safe.callIdx (by rw [callf_toNat hj]; exact hx) hf (hS n) hpre
      fun s' o h => (hpost s' o h).toK n

/-- `call j` of a function that returns nothing, in a store satisfying `R`. -/
theorem w_callVoid {f : Frame} {j a : Nat} {fi : FuncInst H} {S : FSpec H} {vs₀ args : List Val}
    {R : Store H → Prop} (hj : j < 2 ^ 32) (hx : f.module.funcs[j]? = some a)
    (hf : s.funcs[a]? = some fi) (hS : FSpecValid P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → o = .normal [] ∧ R s')
    (k : ∀ s', R s' → HWP P host s' f (vals vs₀ ++ rest) Q) :
    HWP P host s f (vals (vs₀ ++ args) ++ .plain (callf j) :: rest) Q := by
  refine w_call hj hx hf hS hpre fun s' o h => ?_
  obtain ⟨-, ⟨res, rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨a, rfl, hp⟩⟩ := h
  · obtain ⟨ho, hR⟩ := hpost _ _ hp
    cases ho
    simpa [seqPost] using k s' hR
  · cases (hpost _ _ hp).1
  · cases (hpost _ _ hp).1

/-- `call j` of a function that returns one `i32`, in a store satisfying `R` with it. -/
theorem w_callI32 {f : Frame} {j a : Nat} {fi : FuncInst H} {S : FSpec H} {vs₀ args : List Val}
    {R : Store H → BitVec 32 → Prop} (hj : j < 2 ^ 32) (hx : f.module.funcs[j]? = some a)
    (hf : s.funcs[a]? = some fi) (hS : FSpecValid P host a S) (hpre : S.pre s args)
    (hpost : ∀ s' o, S.post s args s' o → ∃ v : BitVec 32, o = .normal [Val.i32 v] ∧ R s' v)
    (k : ∀ s' v, R s' v → HWP P host s' f (vals (vs₀ ++ [Val.i32 v]) ++ rest) Q) :
    HWP P host s f (vals (vs₀ ++ args) ++ .plain (callf j) :: rest) Q := by
  refine w_call hj hx hf hS hpre fun s' o h => ?_
  obtain ⟨-, ⟨res, rfl, hp⟩ | ⟨rfl, hp⟩ | ⟨a, rfl, hp⟩⟩ := h
  · obtain ⟨v, ho, hR⟩ := hpost _ _ hp
    cases ho
    simpa [seqPost] using k s' v hR
  · obtain ⟨v, ho, -⟩ := hpost _ _ hp
    cases ho
  · obtain ⟨v, ho, -⟩ := hpost _ _ hp
    cases ho

end Silmaril.Proofs.Wasm.Acceptor
