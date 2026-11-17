module

public import Silmaril.Wasm.Cfg.MachineLProj.Defs
public import Silmaril.Wasm.Cfg.Bridge.Thms
public import Silmaril.Wasm.Abstract.ExposePTyped.Thms
public import Silmaril.Proofs.Wasm.Cfg.MachineLProjS
import Silmaril.Proofs.Wasm.Cfg.MachineComplete
import Silmaril.Proofs.Wasm.Cfg.MachineLProjI
import Silmaril.Proofs.Wasm.Cfg.MachineLFwd
import Silmaril.Proofs.Wasm.Cfg.MachineLProjC
import Silmaril.Proofs.Wasm.Cfg.MachineLClosed
import Silmaril.Proofs.Wasm.Cfg.Region
import Silmaril.Proofs.Wasm.Cfg.Bridge

@[expose] public section

/-!
# The stepwise projection of the logged machine to `MStepC` (proofs)

Region facts for plain code (`runC_plain_out`), then the step and run projections.
-/

namespace Silmaril.Wasm.Cfg.Proofs.MachineLProjT

open Silmaril.Wasm Silmaril.Wasm.Cfg Silmaril.Wasm.Cfg.Machine Silmaril.Wasm.Cfg.MachineL
  Silmaril.Wasm.Cfg.Region Silmaril.Wasm.Execution.Core Silmaril.Wasm.Binaryen
open Silmaril.Wasm.Cfg.Proofs.MachineLProjS (PlainI Plain)

variable {H : Type} {P : Numerics.Profile} {host : HostSemantics H} {C : Abstract.CallRel H}

/-- Region outcomes of plain code: no pending tail call. -/
def OutPlain : Region.Out → Prop
  | .tail .. | .tailNull .. => False
  | _ => True

/-- Region outcomes of straight-line code: a fallthrough, a trap or a thrown exception. -/
def OutFlat : Region.Out → Prop
  | .normal _ | .trap | .throw _ => True
  | _ => False

theorem outPlain_of_flat {o : Region.Out} (h : OutFlat o) : OutPlain o := by
  cases o <;> simp_all [OutFlat, OutPlain]

theorem run_br_out {s s' : Store H} {f f' : Frame} {vs : List Val} {l : LabelIdx}
    {code : List Admin} {o : Region.Out} (h : RunC P host C s f vs (.plain (.br l) :: code) s' f' o) :
    OutPlain o := by
  obtain ⟨rfl, -, -⟩ := Proofs.MachineComplete.run_br_inv h; trivial

/-- **Plain code ends without a pending tail call**; straight-line code ends normally, in a trap
or in a thrown exception. -/
theorem runC_plain_out : ∀ {is : List Instr}, Plain is →
    ∀ {s s' : Store H} {f f' : Frame} {vs : List Val} {o : Region.Out},
      RunC P host C s f vs (expression is) s' f' o →
        OutPlain o ∧ (Flat is → OutFlat o)
  | [], _, _, _, _, _, _, _, h => by
    cases h; exact ⟨trivial, fun _ => trivial⟩
  | i :: is, hp, s, s', f, f', vs, o, h => by
    have hi := hp i (by simp)
    have ih := @runC_plain_out is (fun j hj => hp j (List.mem_cons_of_mem _ hj))
    have hflat : Flat (i :: is) → Flat is := fun h j hj => h j (List.mem_cons_of_mem _ hj)
    have hterm : Flat (i :: is) → isTerminator i = false := fun h => (h i (by simp)).1
    simp only [expression, List.map_cons] at h
    cases h with
    | val _ h => exact ⟨(ih h).1, fun hf => (ih h).2 (hflat hf)⟩
    | simple _ _ h => exact ⟨(ih h).1, fun hf => (ih h).2 (hflat hf)⟩
    | simpleTrap => exact ⟨trivial, fun _ => trivial⟩
    | br => exact ⟨trivial, fun hf => by simp [isTerminator] at hterm; exact absurd (hterm hf) (by simp)⟩
    | ret => exact ⟨trivial, fun hf => absurd (hterm hf) (by simp [isTerminator])⟩
    | @brIf _ _ _ _ _ k l _ _ h =>
      refine ⟨?_, fun hf => absurd (hterm hf) (by simp [isTerminator])⟩
      by_cases hk : k = 0
      · simp only [hk, ↓reduceIte, List.nil_append] at h; exact (ih h).1
      · simp only [hk, ↓reduceIte, List.singleton_append] at h; exact run_br_out h
    | throw => exact absurd hi.2.1 (by simp [Abstract.CallXE.ehInstr])
    | throwRefNull => exact absurd hi.2.1 (by simp [Abstract.CallXE.ehInstr])
    | throwRefExn => exact absurd hi.2.1 (by simp [Abstract.CallXE.ehInstr])
    | @brData _ _ _ _ _ _ _ _ X _ _ hb h =>
      refine ⟨?_, fun hf => ?_⟩
      · rcases Proofs.MachineComplete.brStep_X hb with rfl | ⟨l, rfl⟩
        · exact (ih h).1
        · exact run_br_out h
      · have := hterm hf
        cases hb <;> simp [isTerminator] at this
    | call _ _ _ _ _ h => exact ⟨(ih h).1, fun hf => (ih h).2 (hflat hf)⟩
    | callTrap => exact ⟨trivial, fun _ => trivial⟩
    | callThrow => exact ⟨trivial, fun _ => trivial⟩
    | _ =>
      have h1 := hi.1
      have h2 := hi.2.2
      first
        | (simp [Abstract.CallX.isXCall] at h2; done)
        | (simp only [liftInstr, reduceCtorEq] at h1)
        | (rename_i hc
           cases i <;> simp_all [Admin.IsReturnCallRef, Abstract.CallX.isXCall])

theorem runC_nil {s s' : Store H} {f f' : Frame} {vs : List Val} {o : Region.Out}
    (h : RunC P host C s f vs [] s' f' o) : o = .normal vs ∧ s' = s ∧ f' = f := by
  generalize hc : ([] : List Admin) = c at h
  cases h <;> simp_all

/-- **What a plain terminator's region run does**, from the stack its segment left: it traps,
returns, branches (`br`, a taken `br_if`, a taken data branch), or falls through (an untaken
`br_if` or data branch), keeping the store and frame unless it traps. -/
theorem term_run {c : List Instr} {i : Nat} {sg : Segment} {t : Instr}
    (hsg : (segment c)[i]? = some sg) (ht : sg.term = some t) (hp : PlainI t)
    {s₁ s' : Store H} {f₁ f' : Frame} {stk₁ : List Val} {o : Region.Out}
    (h : RunC P host C s₁ f₁ stk₁ [.plain t] s' f' o) :
    o = .trap ∨
    (t = .return_ ∧ o = .ret stk₁ ∧ s' = s₁ ∧ f' = f₁) ∨
    (∃ l, t = .br l ∧ o = .br l.toNat stk₁ ∧ s' = s₁ ∧ f' = f₁) ∨
    (∃ (l : LabelIdx) (k : BitVec 32) (W : List Val), t = .brIf l ∧ stk₁ = W ++ [.i32 k] ∧
      ((k = 0 ∧ o = .normal W) ∨ (k ≠ 0 ∧ o = .br l.toNat W)) ∧ s' = s₁ ∧ f' = f₁) ∨
    (∃ (ws us us' : List Val) (X : List Admin), stk₁ = ws ++ us ∧ BrStep s₁ f₁ us t us' X ∧
      ((X = [] ∧ o = .normal (ws ++ us')) ∨
        ∃ l, X = [.plain (.br l)] ∧ o = .br l.toNat (ws ++ us')) ∧ s' = s₁ ∧ f' = f₁) := by
  cases h with
  | val hv => exact absurd hv (by rw [Proofs.MachineComplete.term_val_none hsg ht]; simp)
  | simple hi h₁ h =>
    have := Proofs.MachineComplete.term_noncontrol hsg ht hi; subst this
    exact (Proofs.MachineComplete.steps_unreachable_not_vals h₁).elim
  | simpleTrap => exact .inl rfl
  | br => exact .inr (.inr (.inl ⟨_, rfl, rfl, rfl, rfl⟩))
  | ret => exact .inr (.inl ⟨rfl, rfl, rfl, rfl⟩)
  | @brIf _ _ _ _ ws k l _ _ h =>
    by_cases hk : k = 0
    · subst hk
      simp only [↓reduceIte, List.nil_append] at h
      obtain ⟨rfl, rfl, rfl⟩ := runC_nil h
      exact .inr (.inr (.inr (.inl ⟨l, 0, ws, rfl, rfl, .inl ⟨rfl, rfl⟩, rfl, rfl⟩)))
    · simp only [hk, ↓reduceIte, List.singleton_append] at h
      obtain ⟨rfl, rfl, rfl⟩ := Proofs.MachineComplete.run_br_inv h
      exact .inr (.inr (.inr (.inl ⟨l, k, ws, rfl, rfl, .inr ⟨hk, rfl⟩, rfl, rfl⟩)))
  | @brData _ _ _ _ ws us us' _ X _ _ hb h =>
    rcases Proofs.MachineComplete.brStep_X hb with rfl | ⟨l, rfl⟩
    · simp only [List.nil_append] at h
      obtain ⟨rfl, rfl, rfl⟩ := runC_nil h
      exact .inr (.inr (.inr (.inr ⟨ws, us, us', [], rfl, hb, .inl ⟨rfl, rfl⟩, rfl, rfl⟩)))
    · simp only [List.singleton_append] at h
      obtain ⟨rfl, rfl, rfl⟩ := Proofs.MachineComplete.run_br_inv h
      exact .inr (.inr (.inr (.inr ⟨ws, us, us', _, rfl, hb, .inr ⟨l, rfl, rfl⟩, rfl, rfl⟩)))
  | throw => exact absurd hp.2.1 (by simp [Abstract.CallXE.ehInstr])
  | throwRefNull => exact absurd hp.2.1 (by simp [Abstract.CallXE.ehInstr])
  | throwRefExn => exact absurd hp.2.1 (by simp [Abstract.CallXE.ehInstr])
  | _ =>
    have h1 := hp.1
    have h2 := hp.2.2
    have h3 := Proofs.MachineComplete.term_isTerminator hsg ht
    first
      | (simp [Abstract.CallX.isXCall] at h2; done)
      | (simp [isTerminator] at h3; done)
      | (simp only [liftInstr, reduceCtorEq] at h1)
      | (rename_i hc
         cases t <;> simp_all [Admin.IsReturnCallRef, Abstract.CallX.isXCall])

/-- The block types the checker resolves are Core's. -/
theorem blockType_of_blockArity {mi : ModuleInst} {bt : BlockType} {np nr : Nat}
    (h : Interp.blockArity mi bt = some (np, nr)) :
    ∃ t₁ t₂, mi.blockType? bt = some (t₁, t₂) ∧ t₁.length = np ∧ t₂.length = nr := by
  cases bt with
  | empty =>
    simp [Interp.blockArity, Binaryen.arity] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨[], [], rfl, rfl, rfl⟩
  | value v =>
    simp [Interp.blockArity, Binaryen.arity] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨[], _, rfl, rfl, rfl⟩
  | typeIdx x =>
    simp only [Interp.blockArity, Binaryen.arity, Frame.type?] at h
    cases hq : (mi.types[x.toNat]? >>= Validation.DefType.funcType?) with
    | none => simp [hq] at h
    | some q =>
      obtain ⟨t₁, t₂⟩ := q
      simp only [hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨t₁, t₂, by simpa [ModuleInst.blockType?] using hq, rfl, rfl⟩

/-- The checked frame at label `k`: its block type's arities, and its recorded arity. -/
theorem frame_at {ext : Interp.ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} {rp : List SeqStep} {ls : List LFrame} {out : Option Nat}
    (hF : ChkF ext F mi nl ret body rp ls out) {k : Nat} {L : LFrame} (hL : ls[k]? = some L) :
    ∃ np nr, Interp.blockArity mi L.bt = some (np, nr) ∧ L.arity = (if L.loop then np else nr) := by
  have hk : k < ls.length := (List.getElem?_eq_some_iff.mp hL).1
  obtain ⟨outk, hFk⟩ := Proofs.MachineLProjI.chkF_drop k _ _ out (by omega) hF
  have hdl : ls.drop k = L :: ls.drop (k + 1) := by
    rw [List.drop_eq_getElem_cons hk]; congr 1; exact (List.getElem?_eq_some_iff.mp hL).2
  rw [hdl] at hFk
  rcases hdr : rp.drop k with _ | ⟨⟨m, a⟩, rp'⟩
  · rw [hdr] at hFk; exact hFk.elim
  · rw [hdr] at hFk
    obtain ⟨-, -, -, -, np, nr, -, -, -, -, -, har, hLa, -⟩ := hFk
    exact ⟨np, nr, har, hLa⟩

/-- The top values a Core branch keeps, under any values below the branch site. -/
theorem topVals_brVals_junk {n k : Nat} {ls : List LFrame} {junk N : List Val}
    (h : n ≤ N.length) : topVals n (brVals k ls (junk ++ N.reverse)) = (N.take n).reverse := by
  obtain ⟨j, hj⟩ := MachineLProjC.brVals_junk k ls (junk ++ N.reverse)
  rw [hj, ← List.append_assoc, MachineLProjC.topVals_append (by simpa using h),
    MachineLProjC.topVals_reverse]

theorem liftInstr_of_not_struct {t : Instr} (h : ¬ Instr.IsStruct t) : liftInstr t = .op t [] := by
  cases t with
  | block => exact absurd ⟨_, _, _, _, StructKind.block⟩ h
  | loop => exact absurd ⟨_, _, _, _, StructKind.loop⟩ h
  | if_ => exact absurd ⟨_, _, _, _, StructKind.if_⟩ h
  | tryTable => exact absurd ⟨_, _, _, _, StructKind.tryTable⟩ h
  | _ => rfl

theorem resOut_plain {s' : Store H} {f' : Frame} {o : Region.Out} {r : Store H × Frame × Flow}
    (ho : OutPlain o) (h : Bridge.ResOut C s' f' o r) :
    r.1 = s' ∧ r.2.1 = f' ∧ Bridge.FlowRel r.2.2 o := by
  cases o <;> first | exact ho.elim | exact h

theorem thenC_nil {s₁ s' : Store H} {f₁ f' : Frame} {o₁ o : Region.Out}
    (h : ThenC P host C s₁ f₁ o₁ [] s' f' o) : o = o₁ ∧ s' = s₁ ∧ f' = f₁ := by
  cases o₁ with
  | normal us => exact runC_nil h
  | _ => exact h

theorem flowRel_normal {fl : Flow} {W : List Val} (h : Bridge.FlowRel fl (.normal W)) :
    ∃ ws, fl = .normal ws ∧ W = ws.reverse := by
  cases fl <;> simp_all [Bridge.FlowRel]

theorem flowRel_trap {fl : Flow} (h : Bridge.FlowRel fl .trap) : fl = .trap := by
  cases fl <;> simp_all [Bridge.FlowRel]

theorem flowRel_throw {fl : Flow} {a : Nat} (h : Bridge.FlowRel fl (.throw a)) : fl = .throw a := by
  cases fl <;> simp_all [Bridge.FlowRel]

theorem flowRel_br {fl : Flow} {k : Nat} {W : List Val} (h : Bridge.FlowRel fl (.br k W)) :
    ∃ ws junk, fl = .brk k ws ∧ W = junk ++ ws.reverse := by
  cases fl <;> simp_all [Bridge.FlowRel]

theorem flowRel_ret {fl : Flow} {W : List Val} (h : Bridge.FlowRel fl (.ret W)) :
    ∃ ws junk, fl = .ret ws ∧ W = junk ++ ws.reverse := by
  cases fl <;> simp_all [Bridge.FlowRel]

section Cases
variable {ext : Interp.ExtArity H} {F : List (FuncInst H)} {mi : ModuleInst} {nl ret : Nat}
  {body : Expr}

/-- **An abrupt segment body** (a trap, or an exception from a call) is `MStepC`'s
`bodyTrap`/`bodyRaise`, to the same sink, when no frame is a `try_table`. -/
theorem abrupt_proj {b : BlockId} {sg : Segment} {stk : List Val} {ls : List LFrame}
    {s s₁ : Store H} {f f₁ : Frame} {o₁ : Region.Out} {fl : Flow} {st' : MState H}
    (hb : lookup body b = some sg)
    (hbody : RunC P host C s f stk (expression sg.body) s₁ f₁ o₁) (hfl : OutFlat o₁)
    (hn : ∀ W, o₁ ≠ .normal W) (hfr : Bridge.FlowRel fl o₁)
    (hd : DispL body b ls (s₁, f₁, .flow fl) st') (hnt : ∀ L ∈ ls, L.tryT = false) :
    ∃ stC, MStepC P host C body ⟨.block b, stk, ls, s, f⟩ stC ∧ ProjRel st' stC := by
  cases o₁ with
  | normal W => exact absurd rfl (hn W)
  | trap =>
    obtain rfl := flowRel_trap hfr
    cases hd
    exact ⟨_, .bodyTrap hb hbody, .inl rfl⟩
  | throw a =>
    obtain rfl := flowRel_throw hfr
    cases hd with
    | raise =>
      exact ⟨_, .bodyRaise hb hbody (fun k L hL hT => absurd hT (by
        rw [hnt L (List.mem_of_getElem? hL)]; simp)), .inl rfl⟩
    | catch_ _ hL hT => exact absurd hT (by rw [hnt _ (List.mem_of_getElem? hL)]; simp)
    | catchOut _ hL hT => exact absurd hT (by rw [hnt _ (List.mem_of_getElem? hL)]; simp)
  | _ => exact hfl.elim

/-- **The native fallthrough target is `MStepC`'s**, on checked states. -/
theorem next_target {b : BlockId} {ls : List LFrame} {ws : List Val} {s : Store H} {f : Frame}
    {st' : MState H} {c : List Instr} {out : Option Nat}
    (hd : DispL body b ls (s, f, .flow (.normal ws)) st') (hf : f.module = mi)
    (hc : seqAt body b.seq = some c)
    (hchk : Interp.chkE ext F mi nl ret (labs ret ls) (some ws.length)
      (liftInstrs (restAt c (b.idx + 1))) = some out)
    (hF : ChkF ext F mi nl ret body b.seq.reverse ls out) :
    st' = goto (entry body b.seq (b.idx + 1)) b.seq.length ls ws.reverse s f := by
  cases hd with
  | next hg =>
    obtain ⟨hfit, -⟩ := Proofs.MachineLProjI.entry_inv (s := s) (W := ws.reverse) hf hc
      (by simpa using hchk) hF
    rw [MachineLProjC.gotoN_eq_goto hfit] at hg
    exact (Option.some.inj hg).symm

/-- **A branch, native and `MStepC`**, on checked states: the native target of a branch to label
`k` with the branch-site stack `ws` is related to the `MStepC` branch rule's (supplied as
`hrule`, `hout`), whose stack is `ws` under further values. -/
theorem br_proj {b : BlockId} {stk stk₁ : List Val} {ls : List LFrame} {s s₁ : Store H}
    {f f₁ : Frame} {k : Nat} {ws junk : List Val} {st' : MState H} {out : Option Nat}
    {l : LabelIdx} (hd : DispL body b ls (s₁, f₁, .flow (.brk k ws)) st') (hf : f₁.module = mi)
    (hok : FramesOk body b.seq.reverse ls) (hF : ChkF ext F mi nl ret body b.seq.reverse ls out)
    (hgo : ∃ n, (labs ret ls)[k]? = some n ∧ n ≤ ws.length) (hstk : stk₁ = junk ++ ws.reverse)
    (hk : l.toNat = k)
    (hrule : ∀ L, ls[l.toNat]? = some L → L.arity ≤ (brVals l.toNat ls stk₁).length →
      (L.loop = true → ∃ t₁ t₂, f₁.module.blockType? L.bt = some (t₁, t₂) ∧
        t₁.length = L.arity) →
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩
        (if L.loop then
          goto (resolveT (labels body b.seq) l) (b.seq.length - l.toNat)
            (L :: ls.drop (l.toNat + 1)) (topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁
        else
          goto (resolveT (labels body b.seq) l) (b.seq.length - (l.toNat + 1))
            (ls.drop (l.toNat + 1)) (L.outer ++ topVals L.arity (brVals l.toNat ls stk₁)) s₁ f₁))
    (hout : l.toNat = ls.length →
      MStepC P host C body ⟨.block b, stk, ls, s, f⟩ ⟨.exit, brVals ls.length ls stk₁, [], s₁, f₁⟩) :
    ∃ stC, MStepC P host C body ⟨.block b, stk, ls, s, f⟩ stC ∧ ProjRel st' stC := by
  subst hk
  cases hd with
  | br hL hg =>
    rename_i L
    obtain ⟨n, hn, hle⟩ := hgo
    have hkl : l.toNat < ls.length := (List.getElem?_eq_some_iff.mp hL).1
    have hlk : (labs ret ls)[l.toNat]? = some L.arity := by
      rw [labs, List.getElem?_append_left (by simpa using hkl), List.getElem?_map, hL]; rfl
    rw [hlk] at hn; cases hn
    obtain ⟨hg', -⟩ := Proofs.MachineLProjI.branch_inv (s := s₁) hf hok hF hL hle
    rw [hg'] at hg; cases hg
    have hT : topVals L.arity (brVals l.toNat ls stk₁) =
        topVals L.arity (brVals l.toNat ls ws.reverse) := by
      rw [hstk, topVals_brVals_junk hle, MachineLProjC.topVals_brVals hle]
    have harity : L.arity ≤ (brVals l.toNat ls stk₁).length := by
      obtain ⟨j, hj⟩ := MachineLProjC.brVals_junk l.toNat ls stk₁
      rw [hj, hstk]; simp; omega
    have hlbt : L.loop = true → ∃ t₁ t₂, f₁.module.blockType? L.bt = some (t₁, t₂) ∧
        t₁.length = L.arity := by
      intro hloop
      obtain ⟨np, nr, har, hLa⟩ := frame_at hF hL
      obtain ⟨t₁, t₂, hbt, h1, -⟩ := blockType_of_blockArity har
      rw [hloop] at hLa
      exact ⟨t₁, t₂, by rw [hf]; exact hbt, by rw [h1, hLa]; rfl⟩
    refine ⟨_, hrule L hL harity hlbt, .inl ?_⟩
    rw [hT]; rfl
  | brOut hk =>
    refine ⟨_, hout hk, .inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
    obtain ⟨j, hj⟩ := MachineLProjC.brVals_junk ls.length ls stk₁
    exact ⟨j ++ junk, by rw [hj, hstk, List.append_assoc]⟩

end Cases

open Silmaril.Wasm.Abstract.ExposePTyped (GoodO) in
/-- **Segment goodness** for a checker `ext`, the store's functions `F`, an oracle `C` and a store
invariant `I`: a logged run of plain code whose calls are `C`-answers, from a store satisfying
`I`, checked with `ext`, is checked with `tExt` (for the bridge), keeps `I`, the frame's module and
local count, and ends as the check says (`GoodO`). `I` fixes the store's functions. -/
def SegGood (ext : Interp.ExtArity H) (F : List (FuncInst H)) (C : Abstract.CallRel H)
    (I : Store H → Prop) : Prop :=
  (∀ s, I s → s.funcs = F) ∧
  ∀ {s : Store H} {f : Frame} {N : List Val} {is : List Instr} {l : List (Abstract.SCall H)}
    {r : Store H × Frame × Abstract.CallXP.POut} {labels : List Nat} {ret : Nat} {out : Option Nat},
    Plain is → Abstract.EvalLXPS s f N (liftInstrs is) l r → (∀ e ∈ l, CloseOk C e) → I s →
    Interp.chkE ext F f.module f.locals.length ret labels (some N.length) (liftInstrs is) =
      some out →
    Interp.chkE Interp.tExt F f.module f.locals.length ret labels (some N.length) (liftInstrs is) =
      some out ∧
    I r.1 ∧ r.2.1.module = f.module ∧ r.2.1.locals.length = f.locals.length ∧
      GoodO labels ret out r.2.2

open Silmaril.Wasm.Cfg.Proofs.MachineLProjS (plain_of_flat plain_append seg_flat) in
/-- A block's straight-line code is plain on the shared fragment. -/
theorem plain_codeOf {body : Expr} (hD : DirectCalls body) (hPT : PlainTerms body)
    {p : List SeqStep} {c : List Instr} {i : Nat} {sg : Segment} (hc : seqAt body p = some c)
    (hsg : (segment c)[i]? = some sg) (ht : ∀ i, sg.term = some i → ¬ Instr.IsStruct i) :
    Plain (codeOf sg) := plain_append (plain_of_flat (seg_flat hD hc hsg)) (by
    intro t htm
    cases htt : sg.term with
    | none => simp [htt] at htm
    | some t' =>
      simp [htt] at htm; subst htm
      exact ⟨liftInstr_of_not_struct (ht _ htt), (hPT _ _ _ _ _ hc hsg htt).1,
        (hPT _ _ _ _ _ hc hsg htt).2⟩)

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp evalOXP_goodO) in
/-- **Segment goodness with exceptions on**, from an arity-respecting oracle. -/
theorem segGood_eh {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C) :
    SegGood (Interp.ehExt Γ.tags) Γ.funcs C Γ.Good := by
  refine ⟨fun s h => h.1, fun {s f N is l r labels ret out} hp hr hl hI hchk => ?_⟩
  refine ⟨(MachineLProjS.chkE_plain_tExt _ (fun i hi => ⟨(hp i hi).1, (hp i hi).2.1⟩)).symm.trans
    hchk, ?_⟩
  obtain ⟨s', f', o⟩ := r
  exact evalOXP_goodO hA (Proofs.MachineLClosed.logged_closed hr hl) hI (by rw [hI.1]; exact hchk)

open Silmaril.Wasm.Cfg.Proofs.MachineLProjS (xFreeL_plain ehFreeL_plain irFreeL_plain) in
open Silmaril.Wasm.Abstract.ExposePTyped (GoodO) in
/-- **Segment goodness with `tExt`**, from an oracle sound for `tExt` that keeps the store's
functions. -/
theorem segGood_t {P₀ : Numerics.Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C)
    (hK : ∀ s a args out, C s a args out → out.1.funcs = s.funcs) {F : List (FuncInst H)}
    (hS : Interp.StoreChkE Interp.tExt F) :
    SegGood Interp.tExt F C (fun s => s.funcs = F) := by
  refine ⟨fun s h => h, fun {s f N is l r labels ret out} hp hr hl hI hchk => ⟨hchk, ?_⟩⟩
  have d := Proofs.MachineLClosed.logged_closed hr hl
  have hx := xFreeL_plain hp
  obtain ⟨s₂, f₂, o⟩ := r
  cases o with
  | tail a args n => exact absurd d (Abstract.CallXP.evalOXP_not_tail hx)
  | flow fl =>
    have hoxe := (Abstract.CallXP.evalOXP_iff_evalOXE hx).1 d
    have hfun := Abstract.CallXE.evalOXE_funcs hK hoxe
    have hox := (Abstract.CallXE.evalOXE_iff_evalOX (ehFreeL_plain hp)).1 hoxe
    have hot := (Abstract.CallXT.evalOXT_iff_evalOX (irFreeL_plain hp)).2 hox
    obtain ⟨hA, -⟩ := Interp.OracleX.evalOXT_goodT (P := P₀) (host := host₀) hC hot
    obtain ⟨hfl, -, hmod, hloc⟩ := hA (hI ▸ hS) (by rw [hI]; exact hchk)
    refine ⟨by simp only at hfun ⊢; rw [hfun, hI], hmod, hloc, ?_⟩
    cases fl <;> simp_all [GoodO, Interp.FlowOkE]

open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append chkF_noTry chk_struct tryT_of_noTry
  arity_eq_blockArity entry_inv disp_inv disp_sf) in
open Silmaril.Wasm.Cfg.Proofs.MachineLProjS (plain_of_flat seg_flat) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_zero) in
open Silmaril.Wasm.Abstract.ExposePTyped (GoodO) in
/-- **The checker invariant is preserved by logged steps** on the shared fragment, under a
segment-goodness hypothesis (`SegGood`). -/
theorem cinv_stepG {ext : Interp.ExtArity H} {F : List (FuncInst H)} {I : Store H → Prop}
    (hSG : SegGood ext F C I) {mi : ModuleInst} {nl ret : Nat} {body : Expr} (hNT : NoTry body)
    (hD : DirectCalls body) (hPT : PlainTerms body) {st st' : MState H}
    {l : List (Abstract.SCall H)} (hs : MStepL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : I st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv ext F mi nl ret body st) :
    I st'.store ∧ st'.frame.locals.length = nl ∧ CInv ext F mi nl ret body st' := by
  cases hs with
  | @run b sg stk ls s f l r st' hb ht hr hd =>
    obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
    obtain ⟨c', hc', hsg⟩ := Proofs.Machine.seg_of_lookup hb
    rw [hc] at hc'; cases hc'
    simp only at hchk
    rw [restAt_cons hsg, Binaryen.liftInstrs_append, chkE_append] at hchk
    obtain ⟨oc, hoc, hrest⟩ := Option.bind_eq_some_iff.mp hchk
    obtain ⟨s', f', o⟩ := r
    simp only at hg hn hf
    have hoc' : Interp.chkE ext F f.module f.locals.length ret (labs ret ls)
        (some stk.reverse.length) (liftInstrs (codeOf sg)) = some oc := by
      rw [hf, hn, List.length_reverse]; exact hoc
    obtain ⟨-, hg', hf', hn', hgo⟩ := hSG.2 (plain_codeOf hD hPT hc hsg ht) hr hl hg hoc'
    obtain ⟨hs1, hs2⟩ := disp_sf hd
    simp only at hs1 hs2
    refine ⟨by rw [hs1]; exact hg', by rw [hs2, hn', hn], ?_⟩
    exact disp_inv hd (by simp only; rw [hf', hf]) (by simpa [MInv] using hok) hc hF hgo
      (fun ws hw hoc2 => by simp only at hw; subst hw; subst hoc2; exact hrest)
      (chkF_noTry hNT _ _ _ hF)
  | @abort b sg stk ls s f l r st' hb hr hnn hd =>
    obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
    obtain ⟨c', hc', hsg⟩ := Proofs.Machine.seg_of_lookup hb
    rw [hc] at hc'; cases hc'
    simp only at hchk
    rw [restAt_cons hsg, Segment.instrs, List.append_assoc, Binaryen.liftInstrs_append, chkE_append]
      at hchk
    obtain ⟨oc, hoc, -⟩ := Option.bind_eq_some_iff.mp hchk
    obtain ⟨s', f', o⟩ := r
    simp only at hg hn hf
    have hoc' : Interp.chkE ext F f.module f.locals.length ret (labs ret ls)
        (some stk.reverse.length) (liftInstrs sg.body) = some oc := by
      rw [hf, hn, List.length_reverse]; exact hoc
    obtain ⟨-, hg', hf', hn', hgo⟩ := hSG.2 (plain_of_flat (seg_flat hD hc hsg)) hr hl hg hoc'
    obtain ⟨hs1, hs2⟩ := disp_sf hd
    simp only at hs1 hs2
    refine ⟨by rw [hs1]; exact hg', by rw [hs2, hn', hn], ?_⟩
    exact disp_inv hd (by simp only; rw [hf', hf]) (by simpa [MInv] using hok) hc hF hgo
      (fun ws hw _ => by simp only at hw; subst hw; exact absurd trivial hnn)
      (chkF_noTry hNT _ _ _ hF)
  | @enter b sg stk V V' ls s s₁ f f₁ i a c' bt np nr loop tryT cs l st' hb ht harm hkind hr hsel
      har hg' =>
    obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
    obtain ⟨c₀, hc₀, hsg⟩ := Proofs.Machine.seg_of_lookup hb
    rw [hc] at hc₀; cases hc₀
    simp only at hchk
    rw [restAt_cons hsg, Segment.instrs, ht, Option.toList_some, List.append_assoc,
      Binaryen.liftInstrs_append, chkE_append] at hchk
    obtain ⟨oc, hoc, hrest⟩ := Option.bind_eq_some_iff.mp hchk
    simp only at hg hn hf
    have hoc' : Interp.chkE ext F f.module f.locals.length ret (labs ret ls)
        (some stk.reverse.length) (liftInstrs sg.body) = some oc := by
      rw [hf, hn, List.length_reverse]; exact hoc
    obtain ⟨-, hg', hf', hn', hgo⟩ := hSG.2 (plain_of_flat (seg_flat hD hc hsg)) hr hl hg hoc'
    simp only [GoodO] at hgo
    subst hgo
    have hf₁ : f₁.module = mi := by rw [hf', hf]
    have hnt : tryT = false := tryT_of_noTry hNT hc hsg ht hkind
    simp only [liftInstrs, List.singleton_append, Interp.chkE, Option.bind_eq_some_iff] at hrest
    obtain ⟨o₂, h₂, hrest⟩ := hrest
    obtain ⟨np', nr', hba, hle, ho₂, oa, hoa, hoaE⟩ := chk_struct hkind hnt hsel harm h₂
    rw [arity_eq_blockArity hf₁, hba] at har
    simp only [Option.some.injEq, Prod.mk.injEq] at har
    obtain ⟨rfl, rfl⟩ := har
    subst ho₂
    set L : LFrame := ⟨if loop then np' else nr', (V'.drop np').reverse, loop, tryT, cs, bt⟩
      with hLdef
    have hcA : seqAt body (b.seq ++ [(b.idx, a)]) = some c' := by
      rw [Proofs.Machine.seqAt_append]; simp [hc, hsg, ht, harm]
    have hFa : ChkF ext F mi nl ret body (b.seq ++ [(b.idx, a)]).reverse
        (L :: ls) oa := by
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
      refine ⟨c, sg, i, c', np', nr', by simpa using hc, hsg, ht, harm, hkind, hba, rfl, hoaE,
        ⟨oa, hoa, hoaE⟩, out, ?_, hF⟩
      have : (L.outer.length + nr') = V'.length - np' + nr' := by simp [hLdef]
      rw [this]; exact hrest
    have hW : ((V'.take np').reverse).length = np' := by simp; omega
    obtain ⟨hfit, hinv⟩ := entry_inv (s := s₁) (W := (V'.take np').reverse) hf₁ (j := 0) hcA
      (by rw [restAt_zero, hW]; exact hoa) hFa
    have hlen : (b.seq ++ [(b.idx, a)]).length = b.seq.length + 1 := by simp
    rw [hlen] at hfit hinv
    rw [MachineLProjC.gotoN_eq_goto hfit] at hg'
    cases hg'
    exact ⟨hg', by simp [goto]; rw [hn', hn], hinv⟩



open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append chkF_noTry) in
open Silmaril.Wasm.Cfg.Proofs.MachineLProjS (plain_runC_t plain_of_flat plain_append seg_flat) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons) in
open Silmaril.Wasm.Abstract.ExposePTyped (GoodO ArityResp evalOXP_goodO) in
/-- **A logged block step without a structured terminator projects to one `MStepC` step.** -/
theorem proj_run {P₀ : Numerics.Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C) {ext : Interp.ExtArity H} {F : List (FuncInst H)} {I : Store H → Prop} (hSG : SegGood ext F C I) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} (hNT : NoTry body) (hD : DirectCalls body)
    (hPT : PlainTerms body) (hS : Interp.StoreChkE Interp.tExt F) {b : BlockId}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H} {f : Frame}
    {l : List (Abstract.SCall H)} {r : Store H × Frame × Abstract.CallXP.POut} {st' : MState H}
    (hb : lookup body b = some sg) (ht : ∀ i, sg.term = some i → ¬ Instr.IsStruct i)
    (hr : Abstract.EvalLXPS s f stk.reverse (liftInstrs (codeOf sg)) l r)
    (hd : DispL body b ls r st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : FramesOk body b.seq.reverse ls) (hg : I s) (hn : f.locals.length = nl)
    (hI : CInv ext F mi nl ret body ⟨.block b, stk, ls, s, f⟩) :
    ∃ stC, MStepC P host C body ⟨.block b, stk, ls, s, f⟩ stC ∧ ProjRel st' stC := by
  obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
  obtain ⟨c₀, hc₀, hsg⟩ := Proofs.Machine.seg_of_lookup hb
  simp only at hc hchk hf
  rw [hc] at hc₀; cases hc₀
  rw [restAt_cons hsg, Binaryen.liftInstrs_append, chkE_append] at hchk
  obtain ⟨oc, hoc, hrest⟩ := Option.bind_eq_some_iff.mp hchk
  have hoc' : Interp.chkE ext F f.module f.locals.length ret (labs ret ls)
      (some stk.reverse.length) (liftInstrs (codeOf sg)) = some oc := by
    rw [hf, hn, List.length_reverse]; exact hoc
  have hnt := chkF_noTry hNT _ _ _ hF
  have hbodyFlat : Flat sg.body := seg_flat hD hc hsg
  have hpt : ∀ t, sg.term = some t → PlainI t := fun t htm =>
    ⟨liftInstr_of_not_struct (ht t htm), (hPT _ _ _ _ _ hc hsg htm).1,
      (hPT _ _ _ _ _ hc hsg htm).2⟩
  have hplain : Plain (codeOf sg) := plain_codeOf hD hPT hc hsg ht
  obtain ⟨hT, -, hf', -, hgo⟩ := hSG.2 hplain hr hl hg hoc'
  obtain ⟨s₂, f₂, fl, rfl, s', f', o, hrun, hres⟩ :=
    plain_runC_t (P := P) (host := host) hC hplain hr hl (hSG.1 s hg ▸ hS) (hSG.1 s hg ▸ hT)
  simp only at hf' hgo
  rw [List.reverse_reverse] at hrun
  have hop := (runC_plain_out hplain hrun).1
  obtain ⟨hs', hf'', hfr⟩ := resOut_plain hop hres
  simp only at hs' hf'' hfr
  subst hs' hf''
  have hf₂ : f₂.module = mi := by rw [hf', hf]
  rw [show expression (codeOf sg) = expression sg.body ++ expression sg.term.toList by
    simp [MachineL.codeOf, expression]] at hrun
  obtain ⟨s₁, f₁, o₁, hbody, hthen⟩ := Proofs.Region.run_split hrun rfl
  have hbo := (runC_plain_out (plain_of_flat hbodyFlat) hbody).2 hbodyFlat
  cases hterm : sg.term with
  | none =>
    simp only [hterm, Option.toList_none, expression, List.map_nil] at hthen
    obtain ⟨rfl, rfl, rfl⟩ := thenC_nil hthen
    by_cases hnorm : ∃ W, o = .normal W
    · obtain ⟨W, rfl⟩ := hnorm
      obtain ⟨ws, rfl, rfl⟩ := flowRel_normal hfr
      simp only [GoodO] at hgo
      subst hgo
      have := next_target hd hf₂ hc (by simpa [Segment.instrs, hterm] using hrest) hF
      exact ⟨_, .fall hb hterm hbody, .inl this.symm⟩
    · exact abrupt_proj hb hbody hbo (fun W h => hnorm ⟨W, h⟩) hfr hd hnt
  | some t =>
    have hpt' := hpt t hterm
    have hrest' : ∀ h, oc = some h → Interp.chkE ext F mi nl ret
        (labs ret ls) (some h) (liftInstrs (restAt c (b.idx + 1))) = some out := by
      intro h hh; subst hh; exact hrest
    simp only [hterm, Option.toList_some, expression, List.map_cons, List.map_nil] at hthen
    cases o₁ with
    | normal stk₁ =>
      change RunC P host C s₁ f₁ stk₁ [.plain t] s₂ f₂ o at hthen
      rcases term_run hsg hterm hpt' hthen with
        rfl | ⟨rfl, rfl, rfl, rfl⟩ | ⟨l', rfl, rfl, rfl, rfl⟩ |
        ⟨l', k, W, rfl, rfl, hk, rfl, rfl⟩ | ⟨ws, us, us', X, rfl, hbs, hX, rfl, rfl⟩
      · obtain rfl := flowRel_trap hfr
        cases hd
        exact ⟨_, .termTrap hb hterm hbody hthen, .inl rfl⟩
      · obtain ⟨ws, junk, rfl, rfl⟩ := flowRel_ret hfr
        cases hd
        refine ⟨_, .ret hb hterm hbody, .inr ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩⟩
        obtain ⟨j, hj⟩ := MachineLProjC.brVals_junk ls.length ls (junk ++ ws.reverse)
        exact ⟨j ++ junk, by rw [hj, List.append_assoc]⟩
      · obtain ⟨ws, junk, rfl, rfl⟩ := flowRel_br hfr
        exact br_proj hd hf₂ hok hF hgo rfl rfl
          (fun L hL ha hlbt => .br hb hterm hbody hL ha hlbt)
          (fun h => .brOut hb hterm hbody h)
      · rcases hk with ⟨rfl, rfl⟩ | ⟨hk, rfl⟩
        · obtain ⟨ws, rfl, rfl⟩ := flowRel_normal hfr
          simp only [GoodO] at hgo
          have := next_target hd hf₂ hc (hrest' _ hgo) hF
          exact ⟨_, .brIfNot hb hterm hbody, .inl this.symm⟩
        · obtain ⟨ws, junk, rfl, rfl⟩ := flowRel_br hfr
          exact br_proj hd hf₂ hok hF hgo rfl rfl
            (fun L hL ha hlbt => .brIfTaken hb hterm hbody hk hL ha hlbt)
            (fun h => .brIfOut hb hterm hbody hk h)
      · rcases hX with ⟨rfl, rfl⟩ | ⟨l', rfl, rfl⟩
        · obtain ⟨ws', hws, hW⟩ := flowRel_normal hfr
          subst hws
          simp only [GoodO] at hgo
          have := next_target hd hf₂ hc (hrest' _ hgo) hF
          refine ⟨_, .brDataNot hb hterm hbody hbs, .inl ?_⟩
          rw [this, hW]
        · obtain ⟨ws', junk, rfl, hW⟩ := flowRel_br hfr
          exact br_proj hd hf₂ hok hF hgo hW rfl
            (fun L hL ha hlbt => .brDataTaken hb hterm hbody hbs hL ha hlbt)
            (fun h => .brDataOut hb hterm hbody hbs h)
    | trap =>
      obtain ⟨rfl, rfl, rfl⟩ := hthen
      exact abrupt_proj hb hbody hbo (fun W h => by cases h) hfr hd hnt
    | throw a =>
      obtain ⟨rfl, rfl, rfl⟩ := hthen
      exact abrupt_proj hb hbody hbo (fun W h => by cases h) hfr hd hnt
    | _ => exact hbo.elim

open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append chkF_noTry) in
open Silmaril.Wasm.Cfg.Proofs.MachineLProjS (plain_runC_t plain_of_flat seg_flat) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons) in
open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- **A logged block step whose segment ends abruptly before a structured terminator** projects
to `MStepC`'s `bodyTrap`/`bodyRaise`. -/
theorem proj_abort {P₀ : Numerics.Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C) {ext : Interp.ExtArity H} {F : List (FuncInst H)} {I : Store H → Prop} (hSG : SegGood ext F C I) {mi : ModuleInst}
    {nl ret : Nat} {body : Expr} (hNT : NoTry body) (hD : DirectCalls body)
    (hS : Interp.StoreChkE Interp.tExt F) {b : BlockId}
    {sg : Segment} {stk : List Val} {ls : List LFrame} {s : Store H} {f : Frame}
    {l : List (Abstract.SCall H)} {r : Store H × Frame × Abstract.CallXP.POut} {st' : MState H}
    (hb : lookup body b = some sg)
    (hr : Abstract.EvalLXPS s f stk.reverse (liftInstrs sg.body) l r) (hnn : ¬ r.2.2.IsNormal)
    (hd : DispL body b ls r st') (hl : ∀ e ∈ l, CloseOk C e) (hg : I s)
    (hn : f.locals.length = nl)
    (hI : CInv ext F mi nl ret body ⟨.block b, stk, ls, s, f⟩) :
    ∃ stC, MStepC P host C body ⟨.block b, stk, ls, s, f⟩ stC ∧ ProjRel st' stC := by
  obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
  obtain ⟨c₀, hc₀, hsg⟩ := Proofs.Machine.seg_of_lookup hb
  simp only at hc hchk hf
  rw [hc] at hc₀; cases hc₀
  rw [restAt_cons hsg, Segment.instrs, List.append_assoc, Binaryen.liftInstrs_append, chkE_append]
    at hchk
  obtain ⟨oc, hoc, -⟩ := Option.bind_eq_some_iff.mp hchk
  have hoc' : Interp.chkE ext F f.module f.locals.length ret (labs ret ls)
      (some stk.reverse.length) (liftInstrs sg.body) = some oc := by
    rw [hf, hn, List.length_reverse]; exact hoc
  have hbodyFlat : Flat sg.body := seg_flat hD hc hsg
  obtain ⟨hT, -⟩ := hSG.2 (plain_of_flat hbodyFlat) hr hl hg hoc'
  obtain ⟨s₂, f₂, fl, rfl, s', f', o, hrun, hres⟩ :=
    plain_runC_t (P := P) (host := host) hC (plain_of_flat hbodyFlat) hr hl (hSG.1 s hg ▸ hS)
      (hSG.1 s hg ▸ hT)
  rw [List.reverse_reverse] at hrun
  have hbo := (runC_plain_out (plain_of_flat hbodyFlat) hrun).2 hbodyFlat
  obtain ⟨hs', hf'', hfr⟩ := resOut_plain (outPlain_of_flat hbo) hres
  simp only at hs' hf'' hfr
  subst hs' hf''
  refine abrupt_proj hb hrun hbo (fun W h => ?_) hfr hd (chkF_noTry hNT _ _ _ hF)
  subst h
  obtain ⟨ws, rfl, -⟩ := flowRel_normal hfr
  exact hnn trivial

open Silmaril.Wasm.Cfg.Proofs.MachineLProjI (chkE_append chkF_noTry chk_struct tryT_of_noTry
  arity_eq_blockArity entry_inv) in
open Silmaril.Wasm.Cfg.Proofs.MachineLProjS (plain_runC_t plain_of_flat seg_flat) in
open Silmaril.Wasm.Cfg.Proofs.Machine (restAt_cons restAt_zero) in
open Silmaril.Wasm.Abstract.ExposePTyped (GoodO ArityResp evalOXP_goodO) in
/-- **Entering an arm** projects to `MStepC`'s `enter`, to the same state. -/
theorem proj_enter {P₀ : Numerics.Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C) {ext : Interp.ExtArity H} {F : List (FuncInst H)} {I : Store H → Prop} (hSG : SegGood ext F C I)
    {mi : ModuleInst} {nl ret : Nat} {body : Expr} (hNT : NoTry body) (hD : DirectCalls body)
    (hS : Interp.StoreChkE Interp.tExt F) {b : BlockId} {sg : Segment}
    {stk V V' : List Val} {ls : List LFrame} {s s₁ : Store H} {f f₁ : Frame} {i : Instr}
    {a : Nat} {c' : List Instr} {bt : BlockType} {np nr : Nat} {loop tryT : Bool}
    {cs : List Catch} {l : List (Abstract.SCall H)} {st' : MState H}
    (hb : lookup body b = some sg) (ht : sg.term = some i) (harm : armOf i a = some c')
    (hkind : StructKind i bt loop tryT cs)
    (hr : Abstract.EvalLXPS s f stk.reverse (liftInstrs sg.body) l (s₁, f₁, .flow (.normal V)))
    (hsel : ArmSel i V a V') (har : Binaryen.arity f₁ bt = some (np, nr))
    (hg' : gotoN (entry body (b.seq ++ [(b.idx, a)]) 0) (b.seq.length + 1)
      (⟨if loop then np else nr, (V'.drop np).reverse, loop, tryT, cs, bt⟩ :: ls)
      (V'.take np).reverse s₁ f₁ = some st')
    (hl : ∀ e ∈ l, CloseOk C e) (hg : I s) (hn : f.locals.length = nl)
    (hI : CInv ext F mi nl ret body ⟨.block b, stk, ls, s, f⟩) :
    ∃ stC, MStepC P host C body ⟨.block b, stk, ls, s, f⟩ stC ∧ ProjRel st' stC := by
  obtain ⟨hf, c, out, hc, hchk, hF⟩ := hI
  obtain ⟨c₀, hc₀, hsg⟩ := Proofs.Machine.seg_of_lookup hb
  simp only at hc hchk hf
  rw [hc] at hc₀; cases hc₀
  rw [restAt_cons hsg, Segment.instrs, ht, Option.toList_some, List.append_assoc,
    Binaryen.liftInstrs_append, chkE_append] at hchk
  obtain ⟨oc, hoc, hrest⟩ := Option.bind_eq_some_iff.mp hchk
  have hoc' : Interp.chkE ext F f.module f.locals.length ret (labs ret ls)
      (some stk.reverse.length) (liftInstrs sg.body) = some oc := by
    rw [hf, hn, List.length_reverse]; exact hoc
  have hbodyFlat : Flat sg.body := seg_flat hD hc hsg
  obtain ⟨hT, -, hf', -, hgo⟩ := hSG.2 (plain_of_flat hbodyFlat) hr hl hg hoc'
  simp only [GoodO] at hgo hf'
  subst hgo
  obtain ⟨s₂, f₂, fl, hr2, s', f', o, hrun, hres⟩ :=
    plain_runC_t (P := P) (host := host) hC (plain_of_flat hbodyFlat) hr hl (hSG.1 s hg ▸ hS)
      (hSG.1 s hg ▸ hT)
  simp only [Prod.mk.injEq, Abstract.CallXP.POut.flow.injEq] at hr2
  obtain ⟨rfl, rfl, rfl⟩ := hr2
  rw [List.reverse_reverse] at hrun
  have hbo := (runC_plain_out (plain_of_flat hbodyFlat) hrun).2 hbodyFlat
  obtain ⟨hs', hf'', hfr⟩ := resOut_plain (outPlain_of_flat hbo) hres
  simp only at hs' hf'' hfr
  subst hs' hf''
  have hoN : o = .normal V.reverse := by
    cases o <;> simp_all [Bridge.FlowRel]
  subst hoN
  have hf₁ : f₁.module = mi := by rw [hf', hf]
  have hnt : tryT = false := tryT_of_noTry hNT hc hsg ht hkind
  simp only [liftInstrs, List.singleton_append, Interp.chkE, Option.bind_eq_some_iff] at hrest
  obtain ⟨o₂, h₂, hrest⟩ := hrest
  obtain ⟨np', nr', hba, hle, ho₂, oa, hoa, hoaE⟩ := chk_struct hkind hnt hsel harm h₂
  rw [arity_eq_blockArity hf₁, hba] at har
  simp only [Option.some.injEq, Prod.mk.injEq] at har
  obtain ⟨rfl, rfl⟩ := har
  subst ho₂
  obtain ⟨t₁, t₂, hbt, h1, h2⟩ := blockType_of_blockArity hba
  obtain ⟨hcond, hus⟩ := MachineLProjC.armSel_condArm hsel hle
  set L : LFrame := ⟨if loop then np' else nr', (V'.drop np').reverse, loop, tryT, cs, bt⟩
    with hLdef
  have hcA : seqAt body (b.seq ++ [(b.idx, a)]) = some c' := by
    rw [Proofs.Machine.seqAt_append]; simp [hc, hsg, ht, harm]
  have hFa : ChkF ext F mi nl ret body (b.seq ++ [(b.idx, a)]).reverse
      (L :: ls) oa := by
    simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
    refine ⟨c, sg, i, c', np', nr', by simpa using hc, hsg, ht, harm, hkind, hba, rfl, hoaE,
      ⟨oa, hoa, hoaE⟩, out, ?_, hF⟩
    have : (L.outer.length + nr') = V'.length - np' + nr' := by simp [hLdef]
    rw [this]; exact hrest
  have hW : ((V'.take np').reverse).length = np' := by simp; omega
  obtain ⟨hfit, -⟩ := entry_inv (s := s₁) (W := (V'.take np').reverse) hf₁ (j := 0) hcA
    (by rw [restAt_zero, hW]; exact hoa) hFa
  rw [show (b.seq ++ [(b.idx, a)]).length = b.seq.length + 1 by simp] at hfit
  rw [MachineLProjC.gotoN_eq_goto hfit] at hg'
  cases hg'
  have hlab := MachineLProjC.labelArity_eq loop (hf₁ ▸ hbt : f₁.module.blockType? bt = some _)
    (by rw [arity_eq_blockArity hf₁]; exact hba)
  refine ⟨_, .enter hb ht harm hkind hrun hcond (by rw [hf₁]; exact hbt) (by rw [hus, h1]), .inl ?_⟩
  rw [hlab]

/-- **A logged step projects to one `MStepC` step** (checked states, the shared fragment, under
segment goodness). -/
theorem proj_stepG {P₀ : Numerics.Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C) {ext : Interp.ExtArity H} {F : List (FuncInst H)}
    {I : Store H → Prop} (hSG : SegGood ext F C I) {mi : ModuleInst} {nl ret : Nat} {body : Expr}
    (hNT : NoTry body) (hD : DirectCalls body) (hPT : PlainTerms body)
    (hS : Interp.StoreChkE Interp.tExt F) {st st' : MState H} {l : List (Abstract.SCall H)}
    (hs : MStepL body st l st') (hl : ∀ e ∈ l, CloseOk C e) (hok : MInv body st)
    (hg : I st.store) (hn : st.frame.locals.length = nl) (hI : CInv ext F mi nl ret body st) :
    ∃ stC, MStepC P host C body st stC ∧ ProjRel st' stC := by
  cases hs with
  | run hb ht hr hd =>
    exact proj_run hC hSG hNT hD hPT hS hb ht hr hd hl (by simpa [MInv] using hok) hg hn hI
  | abort hb hr hnn hd => exact proj_abort hC hSG hNT hD hS hb hr hnn hd hl hg hn hI
  | enter hb ht harm hkind hr hsel har hg' =>
    exact proj_enter hC hSG hNT hD hS hb ht harm hkind hr hsel har hg' hl hg hn hI

theorem mstepL_block {body : Expr} {st st' : MState H} {l : List (Abstract.SCall H)}
    (h : MStepL body st l st') : ∃ b, st.node = .block b := by
  cases h <;> exact ⟨_, rfl⟩

/-- A logged run from a state that is not a block is empty. -/
theorem mrunL_sink {body : Expr} {st st' : MState H} {l : List (Abstract.SCall H)}
    (h : MRunL body st l st') (hs : ∀ b, st.node ≠ .block b) : st' = st ∧ l = [] := by
  cases h with
  | refl => exact ⟨rfl, rfl⟩
  | step h₁ _ => obtain ⟨b, hb⟩ := mstepL_block h₁; exact absurd hb (hs b)

/-- **A logged run projects to an `MStepC` run**, step by step (checked states, the shared
fragment, under segment goodness). -/
theorem proj_runLG {P₀ : Numerics.Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C) {ext : Interp.ExtArity H} {F : List (FuncInst H)}
    {I : Store H → Prop} (hSG : SegGood ext F C I) {mi : ModuleInst} {nl ret : Nat} {body : Expr}
    (hNT : NoTry body) (hD : DirectCalls body) (hPT : PlainTerms body)
    (hS : Interp.StoreChkE Interp.tExt F) {st st' : MState H} {l : List (Abstract.SCall H)}
    (h : MRunL body st l st') (hl : ∀ e ∈ l, CloseOk C e) (hok : MInv body st)
    (hg : I st.store) (hn : st.frame.locals.length = nl) (hI : CInv ext F mi nl ret body st) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) st stC ∧ ProjRel st' stC := by
  induction h with
  | refl => exact ⟨_, .refl, .inl rfl⟩
  | @step st st₁ st₂ l₁ l₂ hs hr ih =>
    have hl₁ : ∀ e ∈ l₁, CloseOk C e := fun e he => hl e (List.mem_append_left _ he)
    have hl₂ : ∀ e ∈ l₂, CloseOk C e := fun e he => hl e (List.mem_append_right _ he)
    obtain ⟨stC₁, hC₁, hR₁⟩ := proj_stepG (P := P) (host := host) hC hSG hNT hD hPT hS hs hl₁ hok
      hg hn hI
    obtain ⟨hg₁, hn₁, hI₁⟩ := cinv_stepG hSG hNT hD hPT hs hl₁ hok hg hn hI
    rcases hR₁ with rfl | hR₁
    · obtain ⟨stC₂, hC₂, hR₂⟩ := ih hl₂ (MachineLFwd.mstep_ok hs hok) hg₁ hn₁ hI₁
      exact ⟨stC₂, .head hC₁ hC₂, hR₂⟩
    · obtain ⟨rfl, -⟩ := mrunL_sink hr (fun b h => by rw [hR₁.1] at h; cases h)
      exact ⟨stC₁, .single hC₁, .inr hR₁⟩

/-- **A logged run from the CFG entry projects to an `MStepC` run from the CFG entry** (under
segment goodness), for a body passing the function's own check. -/
theorem proj_initialG {P₀ : Numerics.Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C) {ext : Interp.ExtArity H} {F : List (FuncInst H)}
    {I : Store H → Prop} (hSG : SegGood ext F C I) {ret : Nat} {body : Expr} (hNT : NoTry body)
    (hD : DirectCalls body) (hPT : PlainTerms body) (hS : Interp.StoreChkE Interp.tExt F)
    {s : Store H} {f : Frame} (hg : I s)
    (hchk : Interp.endsAt (Interp.chkE ext F f.module f.locals.length ret [ret] (some 0)
      (liftInstrs body)) ret = true)
    {l : List (Abstract.SCall H)} {st' : MState H} (h : MRunL body (initial body s f) l st')
    (hl : ∀ e ∈ l, CloseOk C e) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) (initial body s f) stC ∧ ProjRel st' stC :=
  proj_runLG hC hSG hNT hD hPT hS h hl (MachineLFwd.initial_ok body s f) hg rfl
    (MachineLProjI.cinv_initial (s := s) (f := f) rfl hchk)

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- `proj_stepG` with exceptions on, for an arity-respecting oracle. -/
theorem proj_step {P₀ : Numerics.Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C) {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C)
    {mi : ModuleInst} {nl ret : Nat} {body : Expr} (hNT : NoTry body) (hD : DirectCalls body)
    (hPT : PlainTerms body) (hS : Interp.StoreChkE Interp.tExt Γ.funcs) {st st' : MState H}
    {l : List (Abstract.SCall H)} (hs : MStepL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (Interp.ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, MStepC P host C body st stC ∧ ProjRel st' stC :=
  proj_stepG hC (segGood_eh hA) hNT hD hPT hS hs hl hok hg hn hI

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- `proj_runLG` with exceptions on, for an arity-respecting oracle. -/
theorem proj_runL {P₀ : Numerics.Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C) {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C)
    {mi : ModuleInst} {nl ret : Nat} {body : Expr} (hNT : NoTry body) (hD : DirectCalls body)
    (hPT : PlainTerms body) (hS : Interp.StoreChkE Interp.tExt Γ.funcs) {st st' : MState H}
    {l : List (Abstract.SCall H)} (h : MRunL body st l st') (hl : ∀ e ∈ l, CloseOk C e)
    (hok : MInv body st) (hg : Γ.Good st.store) (hn : st.frame.locals.length = nl)
    (hI : CInv (Interp.ehExt Γ.tags) Γ.funcs mi nl ret body st) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) st stC ∧ ProjRel st' stC :=
  proj_runLG hC (segGood_eh hA) hNT hD hPT hS h hl hok hg hn hI

open Silmaril.Wasm.Abstract.ExposePTyped (ArityResp) in
/-- `proj_initialG` with exceptions on, for an arity-respecting oracle. -/
theorem proj_initial {P₀ : Numerics.Profile} {host₀ : HostSemantics H}
    (hC : Interp.OracleSoundT P₀ host₀ C) {Γ : Abstract.ExposePStruct.Ctx H} (hA : ArityResp Γ C)
    {ret : Nat} {body : Expr} (hNT : NoTry body) (hD : DirectCalls body) (hPT : PlainTerms body)
    (hS : Interp.StoreChkE Interp.tExt Γ.funcs) {s : Store H} {f : Frame} (hg : Γ.Good s)
    (hchk : Interp.endsAt (Interp.chkE (Interp.ehExt Γ.tags) Γ.funcs f.module f.locals.length ret
      [ret] (some 0) (liftInstrs body)) ret = true)
    {l : List (Abstract.SCall H)} {st' : MState H} (h : MRunL body (initial body s f) l st')
    (hl : ∀ e ∈ l, CloseOk C e) :
    ∃ stC, Relation.ReflTransGen (MStepC P host C body) (initial body s f) stC ∧ ProjRel st' stC :=
  proj_initialG hC (segGood_eh hA) hNT hD hPT hS hg hchk h hl

/-- **The closed instance, no oracle hypothesis**: a logged run from the CFG entry whose calls
are answers of the typed closed extended oracle `closedXOk` is an `MStepC` run with `closedXOk`
from the CFG entry, its end related by `ProjRel`, on the shared fragment, for a body passing the
function's own `tExt` check in a store whose functions pass it. -/
theorem proj_initial_closedX {F : List (FuncInst H)} (hS : Interp.StoreChkE Interp.tExt F)
    {ret : Nat} {body : Expr} (hNT : NoTry body) (hD : DirectCalls body) (hPT : PlainTerms body)
    {s : Store H} {f : Frame} (hs : s.funcs = F)
    (hchk : Interp.endsAt (Interp.chkE Interp.tExt F f.module f.locals.length ret [ret] (some 0)
      (liftInstrs body)) ret = true)
    {l : List (Abstract.SCall H)} {st' : MState H} (h : MRunL body (initial body s f) l st')
    (hl : ∀ e ∈ l, CloseOk closedXOk e) :
    ∃ stC, Relation.ReflTransGen (MStepC P host closedXOk body) (initial body s f) stC ∧
      ProjRel st' stC :=
  proj_initialG (Proofs.Bridge.oracleSoundT_closedXOk P)
    (segGood_t (Proofs.Bridge.oracleSoundT_closedXOk P)
      (fun _ _ _ _ h => Abstract.XRecursion.closedCallX_funcs h.2.2) hS)
    hNT hD hPT hS hs hchk h hl

end Silmaril.Wasm.Cfg.Proofs.MachineLProjT
