module

public import Silmaril.Proofs.Wasm.Jco.Real.StepX

/-!
# Traps of well-typed adaptor code against the reference engine

`trap_stepT`, `trap_execT`: a trapping run of well-typed adaptor code over `realInst`, from an
operand stack `a ++ st` with `a` of the checked types, is matched by a Core 3.0 run of its image
from `a` that reaches `trap`. Well-typed code traps only where Wasm traps: out-of-bounds
`memory.copy`, loads and stores (`copy-oob`, `load-*-oob`, `store-*-oob`), and calls that trap
(`CallsTrapCore`); an `if` branch's trap leaves the label (`trap-label`) and the rest of the code
is dropped (`trap-instrs`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Real
open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm (NumType)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Binaryen (exportFunc?)

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (ma : Nat) (fi : String → Nat)

/-! ## Inversion of trapping runs -/

theorem trap_pure {σ α : Type} {a : α} {s : σ} (h : (pure a : RM σ α) s .trap) : False := by
  cases h

theorem trap_bind {σ α β : Type} {m : RM σ α} {k : α → RM σ β} {s : σ}
    (h : (m >>= k) s .trap) : m s .trap ∨ ∃ a s', m s (.ok a s') ∧ k a s' .trap := by
  rcases (RM.bind_apply m k s _).mp h with ⟨a, s', h1, h2⟩ | ⟨h1, -⟩
  · exact .inr ⟨a, s', h1, h2⟩
  · exact .inl h1

theorem trap_ofOption {σ α : Type} {x : Option α} {s : σ} (h : (RM.ofOption x : RM σ α) s .trap) :
    x = none := by
  cases x with
  | none => rfl
  | some a => exact (trap_pure h).elim

theorem trap_load {M : CoreInst} {a n : Nat} {s : M.St} (h : M.load a n s .trap) :
    (M.mem s).read a n = none := by
  rcases trap_bind h with h1 | ⟨s₀, s₁, hg, hr⟩
  · cases h1
  · have hg' : Out.ok s₀ s₁ = Out.ok s s := hg
    cases hg'
    exact trap_ofOption hr

theorem trap_store {M : CoreInst} {a : Nat} {bs : List UInt8} {s : M.St} (h : M.store a bs s .trap) :
    (M.mem s).write a bs = none := by
  rcases trap_bind h with h1 | ⟨s₀, s₁, hg, hr⟩
  · cases h1
  · have hg' : Out.ok s₀ s₁ = Out.ok s s := hg
    cases hg'
    rcases trap_bind hr with h2 | ⟨m, s₂, hw, hs⟩
    · exact trap_ofOption h2
    · cases hs

theorem asI32_some {v : Flat} (h : v.type = tI32) {σ β : Type} {k : BitVec 32 → RM σ β} {s : σ}
    (hk : ∀ x s', ¬ k x s' .trap) : ¬ (RM.ofOption (asI32? v) >>= k) s .trap := by
  intro ht
  obtain ⟨x, hx⟩ := exists_asI32 h
  rcases trap_bind ht with h1 | ⟨y, s', h1, h2⟩
  · rw [hx] at h1; exact trap_pure h1
  · exact hk y s' h2

/-! ## Core traps in context -/

/-- A run to `trap` under an operand stack and before more code reaches `trap`. -/
theorem to_trap (st : List Flat) {s s' : Store H} {cf cf' : Silmaril.Wasm.Execution.Core.Frame}
    {X : List Admin} (h : Steps P host ⟨s, cf, X⟩ ⟨s', cf', [.trap]⟩) (rest : List Admin) :
    Steps P host ⟨s, cf, stackCode st ++ X ++ rest⟩ ⟨s', cf', [.trap]⟩ := by
  have h1 := Steps.ctxtInstrs (vs := st.reverse.map toVal) (rest := rest) h
  by_cases hne : st.reverse.map toVal ≠ [] ∨ rest ≠ []
  · exact h1.tail (Step.trapInstrs hne)
  · simp only [ne_eq, not_or, not_not] at hne
    obtain ⟨h2, rfl⟩ := hne
    simpa [stackCode, h2, vals] using h1

theorem mem?_of_ok {s : Store H} {cf : Silmaril.Wasm.Execution.Core.Frame}
    (hmem : cf.module.mems[0]? = some ma) (hok : MemOk ma s) :
    ∃ m, s.mem? cf ⟨0⟩ = some (ma, m) ∧ (memBytes ma s).length = m.bytes.size := by
  obtain ⟨m, hm, -⟩ := hok
  refine ⟨m, by simp [Store.mem?, Silmaril.Wasm.Idx.toNat, hmem, hm], ?_⟩
  rw [memBytes_some ma hm, size_toList]

theorem read_none {L : List UInt8} {a n : Nat} (h : Mem.read L a n = none) : L.length < a + n := by
  unfold Mem.read at h; split at h
  · cases h
  · omega

theorem write_none {L bs : List UInt8} {a : Nat} (h : Mem.write L a bs = none) :
    L.length < a + bs.length := by
  unfold Mem.write at h; split at h
  · cases h
  · omega

/-- `memory.copy` out of bounds traps. -/
theorem core_copyOob {s : Store H} {cf : Silmaril.Wasm.Execution.Core.Frame}
    (hmem : cf.module.mems[0]? = some ma) (hok : MemOk ma s) {d src n : BitVec 32}
    (h : (memBytes ma s).length < d.toNat + n.toNat ∨ (memBytes ma s).length < src.toNat + n.toNat) :
    Step P host ⟨s, cf, [i32a d, i32a src, i32a n, .plain (.memoryCopy ⟨0⟩ ⟨0⟩)]⟩
      ⟨s, cf, [.trap]⟩ := by
  obtain ⟨m, hsm, hlen⟩ := mem?_of_ok ma hmem hok
  exact Step.memory (MemoryStep.copyOob (a₁ := .i32) (a₂ := .i32) (a' := .i32) hsm hsm
    (by rw [← hlen]; exact h))

/-- An integer load out of bounds traps. -/
theorem core_loadOob {it : Silmaril.Wasm.IntType} {n : Nat} {sx : Bool} {off : Nat}
    (hn : intWidthOk it n = true) (hoff : off < 2 ^ 32) {s : Store H}
    {cf : Silmaril.Wasm.Execution.Core.Frame} (hmem : cf.module.mems[0]? = some ma)
    (hok : MemOk ma s) {a : BitVec 32} (h : (memBytes ma s).length < a.toNat + off + n) :
    Step P host ⟨s, cf, [i32a a, .plain (coreOf fi (.load (.int it) n sx off))]⟩
      ⟨s, cf, [.trap]⟩ := by
  obtain ⟨m, hsm, hlen⟩ := mem?_of_ok ma hmem hok
  have h' : m.bytes.size < effAddr a.toNat (memArg (alignExp n) off).toCore + n := by
    rw [effAddr_memArg a _ off hoff, ← hlen]; exact h
  rcases intWidthOk_cases hn with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ <;>
    cases sx <;>
    first
    | exact Step.memory (MemoryStep.loadIntOob (a := .i32) (i := a) hsm h')
    | exact Step.memory (MemoryStep.loadPackOob (a := .i32) (i := a) hsm h')

/-- An integer store out of bounds traps. -/
theorem core_storeOob {it : Silmaril.Wasm.IntType} {n off : Nat} (hn : intWidthOk it n = true)
    (hoff : off < 2 ^ 32) {s : Store H} {cf : Silmaril.Wasm.Execution.Core.Frame}
    (hmem : cf.module.mems[0]? = some ma) (hok : MemOk ma s) {a : BitVec 32} {c : BitVec it.width}
    (h : (memBytes ma s).length < a.toNat + off + n) :
    Step P host ⟨s, cf, [i32a a, .plain (.intConst it c), .plain (coreOf fi (.store (.int it) n off))]⟩
      ⟨s, cf, [.trap]⟩ := by
  obtain ⟨m, hsm, hlen⟩ := mem?_of_ok ma hmem hok
  have h' : m.bytes.size < effAddr a.toNat (memArg (alignExp n) off).toCore + n := by
    rw [effAddr_memArg a _ off hoff, ← hlen]; exact h
  rcases intWidthOk_cases hn with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ <;>
    first
    | exact Step.memory (MemoryStep.storeIntOob (a := .i32) (i := a) hsm h')
    | exact Step.memory (MemoryStep.storePackOob (a := .i32) (i := a) hsm h')

/-- A call that traps (as a Core trap) from the adaptor's frame. -/
theorem core_callTrap (hT : CallsTrapCore P host mi ma) {g : String} (n : Nat) {args : List Flat}
    {s : Store H} (hc : (realInst H P host mi ma).call g args s .trap)
    {cf : Silmaril.Wasm.Execution.Core.Frame} (he : FrameEnv mi ma fi cf) :
    ∃ s', Steps P host ⟨s, cf, vals (args.map toVal) ++ [.plain (coreOf fi (.base (.call g n)))]⟩
      ⟨s', cf, [.trap]⟩ := by
  obtain ⟨a, c, ha, hok, hrun, hcode⟩ := hT g args s hc
  obtain ⟨fn, ps, rts, hfn, -, -⟩ := hok
  have hx : cf.module.funcs[(mkIdx (fi g) : Silmaril.Wasm.FuncIdx).toNat]? = some a := by
    simpa [mkIdx, Silmaril.Wasm.Idx.toNat] using he.call g a ha
  have hcall : Step P host ⟨s, cf, [.plain (.call (mkIdx (fi g)))]⟩
      ⟨s, cf, [.ref (.func a), .callRefType fn.type]⟩ := Step.call hx hfn
  have hinv : (invoke s a (args.map toVal)).code =
      vals (args.map toVal) ++ [.ref (.func a), .callRefType fn.type] := by
    simp [invoke, hfn]
  obtain ⟨-, -, hre⟩ := Steps.reframe hrun (invoke_topOK s a _)
  have hre' : Steps P host ⟨s, cf, vals (args.map toVal) ++ [.ref (.func a), .callRefType fn.type]⟩
      ⟨c.store, cf, [.trap]⟩ := by
    rw [← hinv, ← hcode]
    exact hre cf
  have hpre := Steps.ctxtInstrs (vs := args.map toVal) (rest := []) hcall.steps
  simp only [List.append_nil] at hpre
  exact ⟨c.store, hpre.trans hre'⟩

/-! ## The trap simulation -/

variable {rt : String → List NumType} {lt : List NumType}

mutual

/-- **A trapping well-typed instruction.** -/
theorem trap_stepT (hC : CallsTyped (realInst H P host mi ma) rt) (hK : CallsKeepMem P host mi ma)
    (hT : CallsTrapCore P host mi ma) :
    ∀ (i : XInstr) {ts ts' : List NumType}, tyStep rt lt i ts = some ts' →
    ∀ {ls a st : List Flat} {s : Store H}, ls.map (·.type) = lt → a.map (·.type) = ts →
    MemOk ma s → XInstr.step (realInst H P host mi ma) i ⟨ls, a ++ st⟩ s .trap →
    ∀ {cf : Silmaril.Wasm.Execution.Core.Frame}, FrameEnv mi ma fi cf →
    cf.locals = localsOf ls →
    ∃ s' cf', Steps P host ⟨s, cf, stackCode a ++ [.plain (coreOf fi i)]⟩ ⟨s', cf', [.trap]⟩
  | .base (.localGet j), ts, ts', hty, ls, a, st, s, hls, ha, hok, h, cf, he, hl => by
    exfalso
    simp only [XInstr.step, AInstr.step] at h
    simp only [tyStep] at hty
    split at hty
    · rcases hv : ls[j]? with _ | v <;> simp only [hv] at h
      · have : lt[j]? = none := by rw [← hls]; simp [hv]
        simp [this] at hty
      · exact trap_pure h
    · cases hty
  | .base (.localSet j), ts, ts', hty, ls, a, st, s, hls, ha, hok, h, cf, he, hl => by
    exfalso
    rcases a with _ | ⟨v, a⟩
    · subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, ts⟩
      · simp at ha
      · simp only [tyStep] at hty
        split at hty
        · rename_i hc
          have hj : j < ls.length := by
            have h2 := hc.2
            rw [← hls] at h2
            simpa using (List.getElem?_eq_some_iff.mp h2).1
          simp only [List.cons_append, XInstr.step, AInstr.step, hj, ↓reduceIte] at h
          exact trap_pure h
        · cases hty
  | .base (.i32Const c), _, _, _, _, _, _, _, _, _, _, h, _, _, _ => by
    exfalso; simp only [XInstr.step, AInstr.step] at h; exact trap_pure h
  | .base (.call g n), ts, ts', hty, ls, a, st, s, hls, ha, hok, h, cf, he, hl => by
    simp only [tyStep] at hty
    split at hty
    · rename_i hn
      obtain ⟨ht, hd, hle, hle'⟩ := typesOK_take ha hn st
      simp only [XInstr.step, AInstr.step, hle, ↓reduceIte, ht] at h
      rcases trap_bind h with hc | ⟨rs, s₁, -, hp⟩
      · obtain ⟨s', hrun⟩ := core_callTrap P host mi ma fi hT n hc he
        refine ⟨s', cf, ?_⟩
        have := to_trap P host (a.drop n) hrun []
        rw [stackCode_split n a, List.append_assoc]
        simpa [List.reverse_reverse] using this
      · exact (trap_pure hp).elim
    · cases hty
  | .i32Eqz, ts, ts', hty, ls, a, st, s, hls, ha, hok, h, cf, he, hl => by
    exfalso
    rcases a with _ | ⟨v, a⟩
    · subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, ts⟩
      · simp at ha
      · simp only [List.map_cons, List.cons.injEq] at ha
        obtain ⟨rfl, ha⟩ := ha
        simp only [tyStep] at hty
        split at hty
        · rename_i hc
          simp only [List.cons_append, XInstr.step] at h
          exact asI32_some hc (fun _ _ hp => trap_pure hp) h
        · cases hty
  | .i32LtU, ts, ts', hty, ls, a, st, s, hls, ha, hok, h, cf, he, hl => by
    exfalso
    rcases a with _ | ⟨vb, _ | ⟨va, a⟩⟩
    · subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩ <;> simp at ha
      subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩ <;> simp only [List.map_cons, List.cons.injEq,
        reduceCtorEq, and_false] at ha
      obtain ⟨rfl, rfl, ha⟩ := ha
      simp only [tyStep] at hty
      split at hty
      · rename_i hc
        simp only [List.cons_append, XInstr.step] at h
        exact asI32_some hc.1 (fun _ _ h₁ => asI32_some hc.2 (fun _ _ hp => trap_pure hp) h₁) h
      · cases hty
  | .select, ts, ts', hty, ls, a, st, s, hls, ha, hok, h, cf, he, hl => by
    exfalso
    rcases a with _ | ⟨vc, _ | ⟨vb, _ | ⟨va, a⟩⟩⟩
    · subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩ <;> simp at ha
      subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', _ | ⟨t'', ts⟩⟩⟩ <;> simp at ha
      obtain ⟨rfl, rfl⟩ := ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', _ | ⟨t'', ts⟩⟩⟩ <;> simp only [List.map_cons, List.cons.injEq,
        reduceCtorEq, and_false] at ha
      obtain ⟨rfl, rfl, rfl, ha⟩ := ha
      simp only [tyStep] at hty
      split at hty
      · rename_i hc
        simp only [List.cons_append, XInstr.step] at h
        exact asI32_some hc.1 (fun _ _ hp => trap_pure hp) h
      · cases hty
  | .memCopy, ts, ts', hty, ls, a, st, s, hls, ha, hok, h, cf, he, hl => by
    rcases a with _ | ⟨vn, _ | ⟨vs, _ | ⟨vd, a⟩⟩⟩
    · subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', ts⟩⟩ <;> simp at ha
      subst ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', _ | ⟨t'', ts⟩⟩⟩ <;> simp at ha
      obtain ⟨rfl, rfl⟩ := ha; simp [tyStep] at hty
    · rcases ts with _ | ⟨t, _ | ⟨t', _ | ⟨t'', ts⟩⟩⟩ <;> simp only [List.map_cons, List.cons.injEq,
        reduceCtorEq, and_false] at ha
      obtain ⟨rfl, rfl, rfl, ha⟩ := ha
      simp only [tyStep] at hty
      split at hty
      · rename_i hc
        obtain ⟨n, hn⟩ := exists_asI32 hc.1
        obtain ⟨src, hsr⟩ := exists_asI32 hc.2.1
        obtain ⟨d, hd⟩ := exists_asI32 hc.2.2
        simp only [List.cons_append, XInstr.step, hn, hsr, hd] at h
        simp only [RM.ofOption_some, RM.pure_bind] at h
        have hOob : (memBytes ma s).length < d.toNat + n.toNat ∨
            (memBytes ma s).length < src.toNat + n.toNat := by
          rcases trap_bind h with hl₁ | ⟨bs, s₁, hl₁, h₂⟩
          · exact .inr (read_none (trap_load hl₁))
          · obtain ⟨hr, rfl⟩ := ok_load hl₁
            rcases trap_bind h₂ with hs₁ | ⟨u, s₂, -, hp⟩
            · have := write_none (trap_store hs₁)
              rw [read_length hr] at this
              exact .inl this
            · exact (trap_pure hp).elim
        refine ⟨s, cf, ?_⟩
        have := to_trap P host a (core_copyOob P host ma he.mem hok hOob).steps []
        rw [List.append_nil] at this
        rw [stackCode_cons, stackCode_cons, stackCode_cons, asI32?_eq hn, asI32?_eq hsr,
          asI32?_eq hd]
        simp only [List.append_assoc, List.cons_append, List.nil_append, toAdmin_i32]
        exact this
      · cases hty
  | .ifElse res thn els, ts, ts', hty, ls, a, st, s, hls, ha, hok, h, cf, he, hl => by
    rcases a with _ | ⟨vc, a⟩
    · subst ha; simp [tyStep] at hty
    rcases ts with _ | ⟨t, ts⟩
    · simp at ha
    simp only [List.map_cons, List.cons.injEq] at ha
    obtain ⟨rfl, ha⟩ := ha
    simp only [tyStep] at hty
    split at hty
    swap
    · cases hty
    rename_i hc
    obtain ⟨hct, hthn, hels⟩ := hc
    obtain ⟨c, hc'⟩ := exists_asI32 hct
    simp only [List.cons_append, XInstr.step, hc', RM.ofOption_some, RM.pure_bind] at h
    obtain ⟨t₂, hbt, -⟩ := blockType_res cf.module res
    have branch : ∀ (body : List XInstr),
        (∃ s' cf', Steps P host ⟨s, cf, stackCode [] ++ codeOf fi body⟩ ⟨s', cf', [.trap]⟩) →
        ∃ s' cf', Steps P host ⟨s, cf, [.plain (.block (btOf res)
          (Silmaril.Wasm.Lime1.Expr.toCore (XInstr.toLimeL fi body)))]⟩ ⟨s', cf', [.trap]⟩ := by
      intro body ⟨s', cf', hrun⟩
      refine ⟨s', cf', ?_⟩
      have hblk := Step.block (P := P) (host := host) (s := s) (f := cf)
        (body := Silmaril.Wasm.Lime1.Expr.toCore (XInstr.toLimeL fi body)) (vs := []) hbt rfl
      simp only [vals, List.map_nil, List.nil_append, codeOf_toLimeL] at hblk
      have hL := Steps.label (n := t₂.length) (cont := []) hrun
      simp only [stackCode, List.reverse_nil, List.map_nil, vals, List.nil_append] at hL
      exact (hblk.steps.trans hL).tail Step.trapLabel
    by_cases h0 : c == 0
    · simp only [h0, ↓reduceIte] at h
      obtain ⟨s', cf', hrun⟩ := branch els
        (trap_execT hC hK hT els hels (a := []) (st := a ++ st) hls rfl hok (by simpa using h) he hl)
      have hc0 : c = 0 := by simpa using h0
      refine ⟨s', cf', ?_⟩
      have hrun₀ : Steps P host ⟨s, cf, [i32a c, .plain (coreOf fi (.ifElse res thn els))]⟩
          ⟨s', cf', [.trap]⟩ := by
        rw [coreOf_ifElse, hc0]
        exact (Relation.ReflTransGen.single Step.ifFalse).trans hrun
      have := to_trap P host a hrun₀ []
      rw [List.append_nil] at this
      rw [stackCode_cons, asI32?_eq hc', List.append_assoc]
      exact this
    · simp only [h0, ↓reduceIte, Bool.false_eq_true] at h
      obtain ⟨s', cf', hrun⟩ := branch thn
        (trap_execT hC hK hT thn hthn (a := []) (st := a ++ st) hls rfl hok (by simpa using h) he hl)
      have hc0 : c ≠ 0 := by simpa using h0
      refine ⟨s', cf', ?_⟩
      have hrun₀ : Steps P host ⟨s, cf, [i32a c, .plain (coreOf fi (.ifElse res thn els))]⟩
          ⟨s', cf', [.trap]⟩ := by
        rw [coreOf_ifElse]
        exact (Relation.ReflTransGen.single (Step.ifTrue hc0)).trans hrun
      have := to_trap P host a hrun₀ []
      rw [List.append_nil] at this
      rw [stackCode_cons, asI32?_eq hc', List.append_assoc]
      exact this
  | .load t n sx off, ts, ts', hty, ls, a, st, s, hls, ha, hok, h, cf, he, hl => by
    rcases a with _ | ⟨va, a⟩
    · subst ha; cases t <;> simp [tyStep] at hty
    rcases ts with _ | ⟨t₀, ts⟩
    · simp at ha
    simp only [List.map_cons, List.cons.injEq] at ha
    obtain ⟨rfl, ha⟩ := ha
    rcases t with it | ft
    swap
    · simp [tyStep] at hty
    simp only [tyStep] at hty
    split at hty
    swap
    · cases hty
    rename_i hc
    obtain ⟨x, hx⟩ := exists_asI32 hc.1
    simp only [List.cons_append, XInstr.step, hx, RM.ofOption_some, RM.pure_bind] at h
    rcases trap_bind h with hl₁ | ⟨bs, s₁, -, hp⟩
    · have hOob := read_none (trap_load hl₁)
      refine ⟨s, cf, ?_⟩
      have := to_trap P host a
        (core_loadOob P host ma fi (sx := sx) hc.2.1 hc.2.2 he.mem hok (a := x) hOob).steps []
      rw [List.append_nil] at this
      rw [stackCode_cons, asI32?_eq hx, List.append_assoc]
      exact this
    · exact (trap_pure hp).elim
  | .store t n off, ts, ts', hty, ls, a, st, s, hls, ha, hok, h, cf, he, hl => by
    rcases a with _ | ⟨v, _ | ⟨va, a⟩⟩
    · subst ha; cases t <;> simp [tyStep] at hty
    · rcases ts with _ | ⟨t₁, _ | ⟨t₂, ts⟩⟩ <;> simp at ha
      subst ha; cases t <;> simp [tyStep] at hty
    rcases ts with _ | ⟨t₁, _ | ⟨t₂, ts⟩⟩ <;> simp only [List.map_cons, List.cons.injEq,
      reduceCtorEq, and_false] at ha
    obtain ⟨rfl, rfl, ha⟩ := ha
    rcases t with it | ft
    swap
    · simp [tyStep] at hty
    simp only [tyStep] at hty
    split at hty
    swap
    · cases hty
    rename_i hc
    obtain ⟨x, hx⟩ := exists_asI32 hc.2.1
    simp only [List.cons_append, XInstr.step, hx, RM.ofOption_some, RM.pure_bind] at h
    rcases trap_bind h with hs₁ | ⟨u, s₁, -, hp⟩
    · have hOob := write_none (trap_store hs₁)
      rw [length_leBytes] at hOob
      rcases v with ⟨tv, c⟩
      obtain ⟨htv, -, hwd, hof⟩ := hc
      simp only at htv
      subst htv
      refine ⟨s, cf, ?_⟩
      have := to_trap P host a
        (core_storeOob P host ma fi hwd hof he.mem hok (a := x) (c := c) hOob).steps []
      rw [List.append_nil] at this
      rw [stackCode_cons, stackCode_cons, asI32?_eq hx]
      simp only [List.append_assoc, List.cons_append, List.nil_append, toAdmin_i32]
      exact this
    · exact (trap_pure hp).elim

/-- **A trapping well-typed sequence.** -/
theorem trap_execT (hC : CallsTyped (realInst H P host mi ma) rt) (hK : CallsKeepMem P host mi ma)
    (hT : CallsTrapCore P host mi ma) :
    ∀ (is : List XInstr) {ts ts' : List NumType}, tyExec rt lt is ts = some ts' →
    ∀ {ls a st : List Flat} {s : Store H}, ls.map (·.type) = lt → a.map (·.type) = ts →
    MemOk ma s → execX (realInst H P host mi ma) is ⟨ls, a ++ st⟩ s .trap →
    ∀ {cf : Silmaril.Wasm.Execution.Core.Frame}, FrameEnv mi ma fi cf →
    cf.locals = localsOf ls →
    ∃ s' cf', Steps P host ⟨s, cf, stackCode a ++ codeOf fi is⟩ ⟨s', cf', [.trap]⟩
  | [], _, _, _, _, _, _, _, _, _, _, h, _, _, _ => by
    exfalso
    have h' : (pure _ : RM (Store H) Silmaril.Wasm.Jco.Frame) _ .trap := h
    exact trap_pure h'
  | i :: is, ts, ts', hty, ls, a, st, s, hls, ha, hok, h, cf, he, hl => by
    simp only [tyExec] at hty
    split at hty
    swap
    · cases hty
    rename_i ts₁ h₁
    rw [execX_cons] at h
    rcases trap_bind h with hs | ⟨f₁, s₁, hs₁, hr⟩
    · obtain ⟨s', cf', hrun⟩ := trap_stepT hC hK hT i h₁ hls ha hok hs he hl
      refine ⟨s', cf', ?_⟩
      have := to_trap P host [] hrun (codeOf fi is)
      simpa [stackCode, vals, codeOf, List.append_assoc] using this
    · have hok₁ := step_memOk P host mi ma hK i hs₁ hok
      obtain ⟨ls₁, a₁, rfl, hls₁, ha₁, hall⟩ := step_frame hC i h₁ hls ha hs₁
      have hbase := hall []
      simp only [List.append_nil] at hbase
      obtain ⟨cf₁, hm₁, hl₁, hrun₁⟩ :=
        sim_stepT P host mi ma fi hC hK i h₁ (f := ⟨ls, a⟩) ⟨hls, ha⟩ hok hbase he hl
      obtain ⟨s', cf', hrun₂⟩ := trap_execT hC hK hT is hty hls₁ ha₁ hok₁ hr
        (FrameEnv.of_module mi ma fi he hm₁) hl₁
      refine ⟨s', cf', ?_⟩
      have hA := Silmaril.Wasm.Execution.Core.Sim.Steps.append_right hrun₁ (codeOf fi is)
      simp only [List.append_assoc] at hA
      exact hA.trans hrun₂

end

/-! ## Functions -/

/-- **A trapping well-typed adaptor function, invoked**, reaches `trap`. -/
theorem invoke_xfnT_trap (hC : CallsTyped (realInst H P host mi ma) rt)
    (hK : CallsKeepMem P host mi ma) (hT : CallsTrapCore P host mi ma) (fn : XFn) (ty : Nat)
    {rts : List NumType} (hty : tyExec rt (lt ++ List.replicate fn.locals tI32) fn.body [] = some rts)
    {args : List Flat} (ha : args.map (·.type) = lt) (hn : args.length = fn.params) {s : Store H}
    (hok : MemOk ma s) (h : fn.run (realInst H P host mi ma) args s .trap) {b : Nat}
    {fA : FuncInst H} (hb : s.funcs[b]? = some fA)
    (hcode : fA.code = .wasm (fn.toLime fi ty).toCore)
    (he : FrameEnv mi ma fi { module := fA.module })
    {ps rts' : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hexp : Silmaril.Wasm.Validation.Expand fA.type (.func ps rts'))
    (hps : args.length = ps.length) :
    ∃ s', Steps P host (invoke s b (args.map toVal)) ⟨s', {}, [.trap]⟩ := by
  simp only [XFn.run] at h
  have hchk : ∀ o, (RM.check (args.length == fn.params) : RM (Store H) Unit) s o ↔ o = .ok () s := by
    intro o; simp only [RM.check, hn, beq_self_eq_true, ↓reduceIte]; rfl
  rcases trap_bind h with hx | ⟨u, s₁, hc, h₂⟩
  · cases (hchk _).mp hx
  have hc' := (hchk _).mp hc
  cases hc'
  rcases trap_bind h₂ with hx | ⟨fr, s₂, -, hp⟩
  swap
  · exact (trap_pure hp).elim
  set cf := Frame.forCall fA.module (args.map toVal) (fn.toLime fi ty).toCore.locals with hcf
  have hloc : cf.locals = localsOf (args ++ List.replicate fn.locals (i32n 0)) :=
    forCall_i32 fi fA.module args fn ty
  have he' : FrameEnv mi ma fi cf := FrameEnv.of_module mi ma fi he rfl
  obtain ⟨s', cf', hrun⟩ := trap_execT P host mi ma fi hC hK hT fn.body hty
    (ls := args ++ List.replicate fn.locals (i32n 0)) (a := []) (st := [])
    (by rw [types_init, ha]) rfl hok (by simpa using hx) he' hloc
  have hbody : expression (fn.toLime fi ty).toCore.body = codeOf fi fn.body :=
    codeOf_toLimeL fi fn.body
  have hinv : invoke s b (args.map toVal) =
      ⟨s, {}, vals (args.map toVal) ++ [.ref (.func b), .callRefType fA.type]⟩ := by
    simp [invoke, hb]
  rw [hinv]
  have hstep := Step.callRefFunc (P := P) (host := host) (f := {})
    (c := .callRefType fA.type) (vs := args.map toVal) trivial hb hexp (by simpa using hps) hcode
  rw [hbody] at hstep
  simp only [stackCode, List.reverse_nil, List.map_nil, vals, List.nil_append] at hrun
  have hL := Steps.frame (f := {}) (n := rts'.length)
    (Steps.label (n := rts'.length) (cont := []) hrun)
  exact ⟨s', ((hstep.steps.trans hL).tail (Step.ctxtFrame Step.trapLabel)).tail Step.trapFrame⟩

theorem realloc_core_trap (hC : CallsTyped (realInst H P host mi ma) rt)
    (hK : CallsKeepMem P host mi ma) (hT : CallsTrapCore P host mi ma) (alloc : String)
    (hA : rt alloc = [tI32])
    (hty : tyExec rt ([tI32, tI32, tI32, tI32] ++ List.replicate (reallocShimX alloc).locals tI32)
      (reallocShimX alloc).body [] = some [tI32]) (ty : Nat)
    {old os al ns : BitVec 32} {s : Store H} (hok : MemOk ma s)
    (h : reallocEmu (realInst H P host mi ma) alloc old os al ns s .trap) {b : Nat}
    {fA : FuncInst H} (hb : s.funcs[b]? = some fA)
    (hcode : fA.code = .wasm ((reallocShimX alloc).toLime fi ty).toCore)
    (he : FrameEnv mi ma fi { module := fA.module })
    {ps rts' : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hexp : Silmaril.Wasm.Validation.Expand fA.type (.func ps rts')) (hps : 4 = ps.length) :
    ∃ s', Steps P host (invoke s b ([Flat.i32 old, Flat.i32 os, Flat.i32 al, Flat.i32 ns].map toVal))
      ⟨s', {}, [.trap]⟩ := by
  have hrun : (reallocShimX alloc).run (realInst H P host mi ma)
      [Flat.i32 old, Flat.i32 os, Flat.i32 al, Flat.i32 ns] s .trap := by
    rw [reallocShimX_run _ alloc old os al ns (returns_one_i32 hC hA _)]
    exact h
  exact invoke_xfnT_trap P host mi ma fi hC hK hT (reallocShimX alloc) ty hty rfl rfl hok hrun hb
    hcode he hexp hps

end Silmaril.Proofs.Wasm.Jco.Real
