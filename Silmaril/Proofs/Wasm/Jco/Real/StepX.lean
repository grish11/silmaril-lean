module

public import Silmaril.Proofs.Wasm.Jco.Real.Copy
public import Silmaril.Proofs.Wasm.Jco.Real.Framing

/-!
# Well-typed adaptor code against the reference engine

`sim_stepT`, `sim_execT`: a returned run of well-typed adaptor code (`tyStep`, `tyExec`) over
`realInst` is a run of its Core 3.0 image, from a store whose memory has at most `2^32` bytes
(`MemOk`), when the wrapped instance's calls return values of the declared types (`CallsTyped`)
and keep `MemOk` (`CallsKeepMem`). Beyond `Frag` this covers:

* `memory.copy` (`sim_memCopy`, through `core_copy`);
* integer stores (`core_storeInt`, `sim_storeInt`);
* `if … else … end` (in `sim_stepT`): the branch runs on an empty operand stack (`exec_frame`),
  inside the label of the Wasm block, and leaves the values of the block type.

`invoke_xfnT`: the same for an adaptor function invoked by `$invoke`.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco.Real

open Silmaril.Wasm.Jco Silmaril.Wasm.Jco.Real
open Silmaril.Wasm.Component (Flat)
open Silmaril.Wasm (NumType)
open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

variable {H : Type} (P : Profile) (host : HostSemantics H)
  (mi : Silmaril.Wasm.Execution.Core.ModuleInst) (ma : Nat) (fi : String → Nat)

/-! ## `MemOk` along returned runs -/

theorem write_length {m m' : Mem} {a : Nat} {bs : List UInt8} (h : m.write a bs = some m') :
    m'.length = m.length := by
  unfold Mem.write at h
  split at h
  · cases h; simp; omega
  · cases h

theorem memOk_store {s s' : Store H} {a : Nat} {bs : List UInt8} {u : Unit}
    (h : (realInst H P host mi ma).store a bs s (.ok u s')) (hm : MemOk ma s) : MemOk ma s' := by
  obtain ⟨m', hw, rfl⟩ := ok_store h
  exact MemOk.putBytes ma hm (write_length hw)

mutual

theorem step_memOk (hK : CallsKeepMem P host mi ma) : ∀ (i : XInstr) {f f' : Silmaril.Wasm.Jco.Frame}
    {s s' : Store H}, XInstr.step (realInst H P host mi ma) i f s (.ok f' s') → MemOk ma s →
    MemOk ma s'
  | .base (.localGet j), ⟨ls, _⟩, _, _, _, h, hm => by
    simp only [XInstr.step, AInstr.step] at h
    rcases hv : ls[j]? with _ | v <;> simp only [hv] at h
    · cases h
    · obtain ⟨-, rfl⟩ := ok_pure h; exact hm
  | .base (.localSet _), ⟨_, st⟩, _, _, _, h, hm => by
    simp only [XInstr.step, AInstr.step] at h
    split at h
    · split at h
      · obtain ⟨-, rfl⟩ := ok_pure h; exact hm
      · cases h
    · cases h
  | .base (.i32Const _), _, _, _, _, h, hm => by
    simp only [XInstr.step, AInstr.step] at h
    obtain ⟨-, rfl⟩ := ok_pure h; exact hm
  | .base (.call _ _), _, _, _, _, h, hm => by
    simp only [XInstr.step, AInstr.step] at h
    split at h
    · obtain ⟨rs, s₁, hc, hp⟩ := ok_bind h
      obtain ⟨-, rfl⟩ := ok_pure hp
      exact hK _ _ _ _ _ hc hm
    · cases h
  | .i32Eqz, ⟨_, st⟩, _, _, _, h, hm => by
    simp only [XInstr.step] at h
    split at h
    · obtain ⟨_, _, hx, hp⟩ := ok_bind h
      obtain ⟨-, rfl⟩ := ok_ofOption hx
      obtain ⟨-, rfl⟩ := ok_pure hp; exact hm
    · cases h
  | .i32LtU, ⟨_, st⟩, _, _, _, h, hm => by
    simp only [XInstr.step] at h
    split at h
    · obtain ⟨_, _, hx, h₁⟩ := ok_bind h
      obtain ⟨-, rfl⟩ := ok_ofOption hx
      obtain ⟨_, _, hy, hp⟩ := ok_bind h₁
      obtain ⟨-, rfl⟩ := ok_ofOption hy
      obtain ⟨-, rfl⟩ := ok_pure hp; exact hm
    · cases h
  | .select, ⟨_, st⟩, _, _, _, h, hm => by
    simp only [XInstr.step] at h
    split at h
    · obtain ⟨_, _, hx, hp⟩ := ok_bind h
      obtain ⟨-, rfl⟩ := ok_ofOption hx
      obtain ⟨-, rfl⟩ := ok_pure hp; exact hm
    · cases h
  | .memCopy, ⟨_, st⟩, _, _, _, h, hm => by
    simp only [XInstr.step] at h
    split at h
    · obtain ⟨_, _, hx, h₁⟩ := ok_bind h
      obtain ⟨-, rfl⟩ := ok_ofOption hx
      obtain ⟨_, _, hy, h₂⟩ := ok_bind h₁
      obtain ⟨-, rfl⟩ := ok_ofOption hy
      obtain ⟨_, _, hz, h₃⟩ := ok_bind h₂
      obtain ⟨-, rfl⟩ := ok_ofOption hz
      obtain ⟨_, _, hl, h₄⟩ := ok_bind h₃
      obtain ⟨-, rfl⟩ := ok_load hl
      obtain ⟨_, _, hs, hp⟩ := ok_bind h₄
      obtain ⟨-, rfl⟩ := ok_pure hp
      exact memOk_store P host mi ma hs hm
    · cases h
  | .ifElse _ thn els, ⟨_, st⟩, _, _, _, h, hm => by
    simp only [XInstr.step] at h
    split at h
    · obtain ⟨c, _, hx, h₁⟩ := ok_bind h
      obtain ⟨-, rfl⟩ := ok_ofOption hx
      split at h₁
      · exact exec_memOk hK els h₁ hm
      · exact exec_memOk hK thn h₁ hm
    · cases h
  | .load _ _ _ _, ⟨_, st⟩, _, _, _, h, hm => by
    simp only [XInstr.step] at h
    split at h
    · obtain ⟨_, _, hx, h₁⟩ := ok_bind h
      obtain ⟨-, rfl⟩ := ok_ofOption hx
      obtain ⟨_, _, hl, hp⟩ := ok_bind h₁
      obtain ⟨-, rfl⟩ := ok_load hl
      obtain ⟨-, rfl⟩ := ok_pure hp; exact hm
    · cases h
  | .store _ _ _, ⟨_, st⟩, _, _, _, h, hm => by
    simp only [XInstr.step] at h
    split at h
    · obtain ⟨_, _, hx, h₁⟩ := ok_bind h
      obtain ⟨-, rfl⟩ := ok_ofOption hx
      obtain ⟨_, _, hs, hp⟩ := ok_bind h₁
      obtain ⟨-, rfl⟩ := ok_pure hp
      exact memOk_store P host mi ma hs hm
    · cases h

theorem exec_memOk (hK : CallsKeepMem P host mi ma) : ∀ (is : List XInstr)
    {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H},
    execX (realInst H P host mi ma) is f s (.ok f' s') → MemOk ma s → MemOk ma s'
  | [], f, f', s, s', h, hm => by
    have h' : (pure f : RM (Store H) Silmaril.Wasm.Jco.Frame) s (.ok f' s') := h
    obtain ⟨-, rfl⟩ := ok_pure h'; exact hm
  | i :: is, _, _, _, _, h, hm => by
    rw [execX_cons] at h
    obtain ⟨_, _, h₁, h₂⟩ := ok_bind h
    exact exec_memOk hK is h₂ (step_memOk hK i h₁ hm)

end

/-! ## `memory.copy` -/

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem sim_memCopy {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (h : XInstr.step (realInst H P host mi ma) .memCopy f s (.ok f' s')) (hok : MemOk ma s)
    {cf : Silmaril.Wasm.Execution.Core.Frame} (he : FrameEnv mi ma fi cf)
    (hl : cf.locals = localsOf f.locals) :
    Sim P host f f' s s' cf [.plain (coreOf fi .memCopy)] := by
  rcases f with ⟨ls, _ | ⟨vn, _ | ⟨vs, _ | ⟨vd, st⟩⟩⟩⟩ <;> simp only [XInstr.step] at h
  · cases h
  · cases h
  · cases h
  · obtain ⟨n, _, hn, h₁⟩ := ok_bind h
    obtain ⟨hn', rfl⟩ := ok_ofOption hn
    obtain ⟨src, _, hsr, h₂⟩ := ok_bind h₁
    obtain ⟨hsr', rfl⟩ := ok_ofOption hsr
    obtain ⟨d, _, hd, h₃⟩ := ok_bind h₂
    obtain ⟨hd', rfl⟩ := ok_ofOption hd
    obtain ⟨bs, _, hld, h₄⟩ := ok_bind h₃
    obtain ⟨hr, rfl⟩ := ok_load hld
    obtain ⟨u, _, hst, hp⟩ := ok_bind h₄
    obtain ⟨m', hw, rfl⟩ := ok_store hst
    obtain ⟨rfl, rfl⟩ := ok_pure hp
    obtain ⟨rfl, hb₁, hb₂⟩ := write_read_mmove hr hw
    refine ⟨cf, rfl, hl, ?_⟩
    have hc := core_copy P host ma he.mem n.toNat d src _ hok hb₁ hb₂ n.isLt
    rw [ofNat_toNat32] at hc
    have hrun := lift P host st hc
    rw [List.append_nil] at hrun
    rw [stackCode_cons, stackCode_cons, stackCode_cons, asI32?_eq hn', asI32?_eq hsr',
      asI32?_eq hd']
    simp only [List.append_assoc, List.cons_append, List.nil_append, toAdmin_i32]
    exact hrun

/-! ## Integer stores -/

/-- **The Core 3.0 store** of the image of an integer store, writing the bytes `realInst`
writes. -/
theorem core_storeInt {it : Silmaril.Wasm.IntType} {n off : Nat} (hn : intWidthOk it n = true)
    (hoff : off < 2 ^ 32) {s : Store H} {cf : Silmaril.Wasm.Execution.Core.Frame}
    (hmem : cf.module.mems[0]? = some ma) {a : BitVec 32} {c : BitVec it.width} {m' : Mem}
    (hw : (memBytes ma s).write (a.toNat + off) (leBytes n c.toNat) = some m') :
    Step P host ⟨s, cf, [i32a a, .plain (.intConst it c), .plain (coreOf fi (.store (.int it) n off))]⟩
      ⟨putBytes ma s m', cf, []⟩ := by
  have hn0 : 0 < n := by
    rcases intWidthOk_cases hn with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  obtain ⟨m, b, hm, hst, hput⟩ := memBytes_store hn0 hw
  have hsm : s.mem? cf ⟨0⟩ = some (ma, m) := by
    simp [Store.mem?, Silmaril.Wasm.Idx.toNat, hmem, hm]
  rw [hput]
  rw [← effAddr_memArg a (alignExp n) off hoff, BitVec.ofNat_toNat] at hst
  rcases intWidthOk_cases hn with ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl | rfl⟩ <;>
    first
    | exact Step.memory (MemoryStep.storeIntVal (a := .i32) (i := a) hsm hst)
    | exact Step.memory (MemoryStep.storePackVal (a := .i32) (i := a) hsm hst)

theorem sim_storeInt {it : Silmaril.Wasm.IntType} {n off : Nat} (hn : intWidthOk it n = true)
    (hoff : off < 2 ^ 32) {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}
    (ht : (f.stack.head?.map (·.type)) = some (.int it))
    (h : XInstr.step (realInst H P host mi ma) (.store (.int it) n off) f s (.ok f' s'))
    {cf : Silmaril.Wasm.Execution.Core.Frame} (he : FrameEnv mi ma fi cf)
    (hl : cf.locals = localsOf f.locals) :
    Sim P host f f' s s' cf [.plain (coreOf fi (.store (.int it) n off))] := by
  rcases f with ⟨ls, _ | ⟨v, _ | ⟨va, st⟩⟩⟩ <;> simp only [XInstr.step] at h
  · cases h
  · cases h
  · obtain ⟨a, _, ha, h₁⟩ := ok_bind h
    obtain ⟨ha', rfl⟩ := ok_ofOption ha
    obtain ⟨u, _, hst, hp⟩ := ok_bind h₁
    obtain ⟨m', hw, rfl⟩ := ok_store hst
    obtain ⟨rfl, rfl⟩ := ok_pure hp
    refine ⟨cf, rfl, hl, ?_⟩
    rcases v with ⟨t, c⟩
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at ht
    subst ht
    have hrun := lift P host st
      (core_storeInt P host ma fi hn hoff he.mem (a := a) (c := c) hw).steps
    rw [List.append_nil] at hrun
    rw [stackCode_cons, stackCode_cons, asI32?_eq ha']
    simp only [List.append_assoc, List.cons_append, List.nil_append, toAdmin_i32]
    exact hrun

/-! ## The simulation -/

theorem typed_step {M : CoreInst} {rt : String → List NumType} {lt : List NumType}
    (hC : CallsTyped M rt) {i : XInstr} {ts ts' : List NumType} (hty : tyStep rt lt i ts = some ts')
    {f f' : Silmaril.Wasm.Jco.Frame} {s s' : M.St} (hf : Typed lt ts f)
    (h : i.step M f s (.ok f' s')) : Typed lt ts' f' := by
  rcases f with ⟨ls, a⟩
  have h' : i.step M ⟨ls, a ++ []⟩ s (.ok f' s') := by simpa using h
  obtain ⟨ls', a', rfl, hls', ha', -⟩ := step_frame hC i hty hf.1 hf.2 h'
  exact ⟨hls', by simpa using ha'⟩

/-- The Core block type of an adaptor `if`. -/
def btOf (res : Option NumType) : Silmaril.Wasm.BlockType :=
  Silmaril.Wasm.Lime1.BlockType.toCore (match res with | some t => .value t | none => .empty)

theorem coreOf_ifElse (res : Option NumType) (thn els : List XInstr) :
    coreOf fi (.ifElse res thn els) = .if_ (btOf res)
      (Silmaril.Wasm.Lime1.Expr.toCore (XInstr.toLimeL fi thn))
      (Silmaril.Wasm.Lime1.Expr.toCore (XInstr.toLimeL fi els)) := by
  cases res <;> rfl

theorem blockType_res (m : Silmaril.Wasm.Execution.Core.ModuleInst) (res : Option NumType) :
    ∃ t₂, m.blockType? (btOf res) = some ([], t₂) ∧ t₂.length = res.toList.length := by
  cases res <;> exact ⟨_, rfl, rfl⟩

variable {rt : String → List NumType} {lt : List NumType}

mutual

/-- **One well-typed instruction.** -/
theorem sim_stepT (hC : CallsTyped (realInst H P host mi ma) rt)
    (hK : CallsKeepMem P host mi ma) :
    ∀ (i : XInstr) {ts ts' : List NumType}, tyStep rt lt i ts = some ts' →
    ∀ {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}, Typed lt ts f → MemOk ma s →
    XInstr.step (realInst H P host mi ma) i f s (.ok f' s') →
    ∀ {cf : Silmaril.Wasm.Execution.Core.Frame}, FrameEnv mi ma fi cf →
    cf.locals = localsOf f.locals → Sim P host f f' s s' cf [.plain (coreOf fi i)]
  | .base (.localGet j), ts, ts', hty, f, f', s, s', _, _, h, cf, _, hl => by
    simp only [tyStep] at hty
    split at hty
    · rename_i hj; exact sim_localGet P host mi ma fi hj h hl
    · cases hty
  | .base (.localSet j), ts, ts', hty, f, f', s, s', _, _, h, cf, _, hl => by
    rcases ts with _ | ⟨t, ts⟩
    · simp [tyStep] at hty
    · simp only [tyStep] at hty
      split at hty
      · rename_i hj; exact sim_localSet P host mi ma fi hj.1 h hl
      · cases hty
  | .base (.i32Const c), _, _, _, _, _, _, _, _, _, h, _, _, hl =>
    sim_i32Const P host mi ma fi c h hl
  | .base (.call g n), _, _, _, _, _, _, _, _, _, h, _, he, hl =>
    sim_call P host mi ma fi g n h he hl
  | .i32Eqz, _, _, _, _, _, _, _, _, _, h, _, _, hl => sim_i32Eqz P host mi ma fi h hl
  | .i32LtU, _, _, _, _, _, _, _, _, _, h, _, _, hl => sim_i32LtU P host mi ma fi h hl
  | .select, _, _, _, _, _, _, _, _, _, h, _, _, hl => sim_select P host mi ma fi h hl
  | .memCopy, _, _, _, _, _, _, _, _, hok, h, _, he, hl => sim_memCopy P host mi ma fi h hok he hl
  | .load t n sx off, ts, ts', hty, f, f', s, s', _, _, h, cf, he, hl => by
    rcases ts with _ | ⟨t₀, ts⟩
    · cases t <;> simp [tyStep] at hty
    · rcases t with it | ft
      · simp only [tyStep] at hty
        split at hty
        · rename_i hc; exact sim_loadInt P host mi ma fi hc.2.1 hc.2.2 h he hl
        · cases hty
      · simp [tyStep] at hty
  | .store t n off, ts, ts', hty, f, f', s, s', hf, _, h, cf, he, hl => by
    rcases ts with _ | ⟨t₁, _ | ⟨t₂, ts⟩⟩
    · cases t <;> simp [tyStep] at hty
    · cases t <;> simp [tyStep] at hty
    · rcases t with it | ft
      · simp only [tyStep] at hty
        split at hty
        · rename_i hc
          have ht : f.stack.head?.map (·.type) = some (.int it) := by
            rcases f with ⟨ls, _ | ⟨v, a⟩⟩
            · have := hf.2; simp at this
            · have := hf.2; simp only [List.map_cons, List.cons.injEq] at this
              simp [this.1, hc.1]
          exact sim_storeInt P host mi ma fi hc.2.2.1 hc.2.2.2 ht h he hl
        · cases hty
      · simp [tyStep] at hty
  | .ifElse res thn els, ts, ts', hty, ⟨ls, a⟩, f', s, s', hf, hok, h, cf, he, hl => by
    rcases a with _ | ⟨vc, st⟩
    · have := hf.2; rcases ts with _ | ⟨t, ts⟩
      · simp [tyStep] at hty
      · simp at this
    rcases ts with _ | ⟨t, ts⟩
    · have := hf.2; simp at this
    simp only [tyStep] at hty
    split at hty
    swap
    · cases hty
    rename_i hc
    cases hty
    obtain ⟨-, hthn, hels⟩ := hc
    have hls : ls.map (·.type) = lt := hf.1
    simp only [XInstr.step] at h
    obtain ⟨c, s₁, hcv, h₁⟩ := ok_bind h
    obtain ⟨hc', hs₁⟩ := ok_ofOption hcv
    rw [hs₁] at h₁
    obtain ⟨t₂, hbt, ht₂⟩ := blockType_res cf.module res
    -- the branch, run on an empty operand stack inside the block's label
    have branch : ∀ (body : List XInstr), tyExec rt lt body [] = some res.toList →
        (∀ {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}, Typed lt [] f → MemOk ma s →
          execX (realInst H P host mi ma) body f s (.ok f' s') →
          ∀ {cf : Silmaril.Wasm.Execution.Core.Frame}, FrameEnv mi ma fi cf →
          cf.locals = localsOf f.locals → Sim P host f f' s s' cf (codeOf fi body)) →
        execX (realInst H P host mi ma) body ⟨ls, st⟩ s (.ok f' s') →
        ∃ cf' : Silmaril.Wasm.Execution.Core.Frame, cf'.module = cf.module ∧
          cf'.locals = localsOf f'.locals ∧ ∃ a' : List Flat, f'.stack = a' ++ st ∧
          Steps P host ⟨s, cf, [.plain (.block (btOf res)
            (Silmaril.Wasm.Lime1.Expr.toCore (XInstr.toLimeL fi body)))]⟩
            ⟨s', cf', stackCode a'⟩ := by
      intro body hb ih hrun
      obtain ⟨ls', a', rfl, hls', ha', hall⟩ :=
        exec_frame hC body hb (a := []) (st := st) hls rfl (by simpa using hrun)
      have hbase := hall []
      simp only [List.append_nil] at hbase
      obtain ⟨cf', hm', hl', hrun'⟩ := ih (f := ⟨ls, []⟩) ⟨hls, rfl⟩ hok hbase he hl
      refine ⟨cf', hm', hl', a', rfl, ?_⟩
      have hlen : a'.length = t₂.length := by rw [ht₂, ← ha', List.length_map]
      have hblk := Step.block (P := P) (host := host) (s := s) (f := cf)
        (body := Silmaril.Wasm.Lime1.Expr.toCore (XInstr.toLimeL fi body)) (vs := []) hbt rfl
      rw [← hlen] at hblk
      simp only [vals, List.map_nil, List.nil_append, codeOf_toLimeL] at hblk
      have hL := Steps.label (n := a'.length) (cont := []) hrun'
      simp only [stackCode, List.reverse_nil, List.map_nil, vals, List.nil_append] at hL
      exact (hblk.steps.trans hL).tail Step.labelVals
    by_cases h0 : c == 0
    · simp only [h0, ↓reduceIte] at h₁
      obtain ⟨cf', hm', hl', a', hst, hrun⟩ := branch els hels (sim_execT hC hK els hels) h₁
      have hc0 : c = 0 := by simpa using h0
      refine ⟨cf', hm', hl', ?_⟩
      have hrun₀ : Steps P host ⟨s, cf, [i32a c, .plain (coreOf fi (.ifElse res thn els))]⟩
          ⟨s', cf', stackCode a'⟩ := by
        rw [coreOf_ifElse, hc0]
        exact (Relation.ReflTransGen.single Step.ifFalse).trans hrun
      have hall := lift P host st hrun₀
      rw [stackCode_cons, asI32?_eq hc', hst, stackCode_append, List.append_assoc]
      exact hall
    · simp only [h0, ↓reduceIte, Bool.false_eq_true] at h₁
      obtain ⟨cf', hm', hl', a', hst, hrun⟩ := branch thn hthn (sim_execT hC hK thn hthn) h₁
      have hc0 : c ≠ 0 := by simpa using h0
      refine ⟨cf', hm', hl', ?_⟩
      have hrun₀ : Steps P host ⟨s, cf, [i32a c, .plain (coreOf fi (.ifElse res thn els))]⟩
          ⟨s', cf', stackCode a'⟩ := by
        rw [coreOf_ifElse]
        exact (Relation.ReflTransGen.single (Step.ifTrue hc0)).trans hrun
      have hall := lift P host st hrun₀
      rw [stackCode_cons, asI32?_eq hc', hst, stackCode_append, List.append_assoc]
      exact hall

/-- **A well-typed sequence.** -/
theorem sim_execT (hC : CallsTyped (realInst H P host mi ma) rt)
    (hK : CallsKeepMem P host mi ma) :
    ∀ (is : List XInstr) {ts ts' : List NumType}, tyExec rt lt is ts = some ts' →
    ∀ {f f' : Silmaril.Wasm.Jco.Frame} {s s' : Store H}, Typed lt ts f → MemOk ma s →
    execX (realInst H P host mi ma) is f s (.ok f' s') →
    ∀ {cf : Silmaril.Wasm.Execution.Core.Frame}, FrameEnv mi ma fi cf →
    cf.locals = localsOf f.locals → Sim P host f f' s s' cf (codeOf fi is)
  | [], _, _, _, f, f', s, s', _, _, h, cf, _, hl => by
    have h' : (pure f : RM (Store H) Silmaril.Wasm.Jco.Frame) s (.ok f' s') := h
    obtain ⟨rfl, rfl⟩ := ok_pure h'
    exact ⟨cf, rfl, hl, by simpa [codeOf] using Relation.ReflTransGen.refl⟩
  | i :: is, ts, ts', hty, f, f', s, s', hf, hok, h, cf, he, hl => by
    simp only [tyExec] at hty
    split at hty
    swap
    · cases hty
    rename_i ts₁ h₁
    rw [execX_cons] at h
    obtain ⟨f₁, s₁, hs₁, hr⟩ := ok_bind h
    obtain ⟨cf₁, hm₁, hl₁, hrun₁⟩ := sim_stepT hC hK i h₁ hf hok hs₁ he hl
    have hok₁ := step_memOk P host mi ma hK i hs₁ hok
    have hf₁ := typed_step hC h₁ hf hs₁
    obtain ⟨cf₂, hm₂, hl₂, hrun₂⟩ :=
      sim_execT hC hK is hty hf₁ hok₁ hr (FrameEnv.of_module mi ma fi he hm₁) hl₁
    refine ⟨cf₂, hm₂.trans hm₁, hl₂, ?_⟩
    have hA := Silmaril.Wasm.Execution.Core.Sim.Steps.append_right hrun₁ (codeOf fi is)
    simp only [List.append_assoc] at hA
    exact hA.trans hrun₂

end

/-! ## Functions -/

theorem types_init (args : List Flat) (n : Nat) :
    (args ++ List.replicate n (i32n 0)).map (·.type) =
      args.map (·.type) ++ List.replicate n tI32 := by
  simp [List.map_replicate]

/-- **A well-typed adaptor function, in a Core call frame of its image.** -/
theorem run_frameT (hC : CallsTyped (realInst H P host mi ma) rt) (hK : CallsKeepMem P host mi ma)
    (fn : XFn) (ty : Nat) {rts : List NumType}
    (hty : tyExec rt (lt ++ List.replicate fn.locals tI32) fn.body [] = some rts)
    {args rs : List Flat} (ha : args.map (·.type) = lt) {s s' : Store H} (hok : MemOk ma s)
    (h : fn.run (realInst H P host mi ma) args s (.ok rs s'))
    (mod : Silmaril.Wasm.Execution.Core.ModuleInst) (he : FrameEnv mi ma fi { module := mod })
    (g : Silmaril.Wasm.Execution.Core.Frame) :
    Steps P host ⟨s, g, [.frame rs.length (Frame.forCall mod (args.map toVal)
        (fn.toLime fi ty).toCore.locals)
        [.label rs.length [] (expression (fn.toLime fi ty).toCore.body)]]⟩
      ⟨s', g, vals (rs.map toVal)⟩ := by
  obtain ⟨u, s₁, hc, h₁⟩ := ok_bind h
  obtain ⟨-, rfl⟩ : args.length = fn.params ∧ s₁ = s := by
    unfold RM.check at hc
    split at hc
    · rename_i hb
      obtain ⟨-, rfl⟩ := ok_pure hc
      exact ⟨by simpa using hb, rfl⟩
    · cases hc
  obtain ⟨fr, s₂, hx, hp⟩ := ok_bind h₁
  obtain ⟨rfl, rfl⟩ := ok_pure hp
  set cf := Frame.forCall mod (args.map toVal) (fn.toLime fi ty).toCore.locals with hcf
  have hloc : cf.locals = localsOf (args ++ List.replicate fn.locals (i32n 0)) :=
    forCall_i32 fi mod args fn ty
  have he' : FrameEnv mi ma fi cf := FrameEnv.of_module mi ma fi he rfl
  have htyped : Typed (lt ++ List.replicate fn.locals tI32) []
      ⟨args ++ List.replicate fn.locals (i32n 0), []⟩ := ⟨by rw [types_init, ha], rfl⟩
  obtain ⟨cf', -, -, hrun⟩ := sim_execT P host mi ma fi hC hK fn.body hty htyped hok hx he' hloc
  have hbody : expression (fn.toLime fi ty).toCore.body = codeOf fi fn.body :=
    codeOf_toLimeL fi fn.body
  have hnil : stackCode ([] : List Flat) = [] := rfl
  rw [hnil, List.nil_append] at hrun
  rw [hbody]
  have hL := Steps.frame (f := g) (n := fr.stack.reverse.length)
    (Steps.label (n := fr.stack.reverse.length) (cont := []) hrun)
  exact (hL.tail (Step.ctxtFrame Step.labelVals)).tail (Step.frameVals (by simp))

/-- **A well-typed adaptor function, invoked.** -/
theorem invoke_xfnT (hC : CallsTyped (realInst H P host mi ma) rt) (hK : CallsKeepMem P host mi ma)
    (fn : XFn) (ty : Nat) {rts : List NumType}
    (hty : tyExec rt (lt ++ List.replicate fn.locals tI32) fn.body [] = some rts)
    {args rs : List Flat} (ha : args.map (·.type) = lt) {s s' : Store H} (hok : MemOk ma s)
    (h : fn.run (realInst H P host mi ma) args s (.ok rs s')) {b : Nat}
    {fA : FuncInst H} (hb : s.funcs[b]? = some fA)
    (hcode : fA.code = .wasm (fn.toLime fi ty).toCore)
    (he : FrameEnv mi ma fi { module := fA.module })
    {ps rts' : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hexp : Silmaril.Wasm.Validation.Expand fA.type (.func ps rts'))
    (hps : args.length = ps.length) (hrts : rs.length = rts'.length) :
    Steps P host (invoke s b (args.map toVal)) ⟨s', {}, vals (rs.map toVal)⟩ := by
  have hinv : invoke s b (args.map toVal) =
      ⟨s, {}, vals (args.map toVal) ++ [.ref (.func b), .callRefType fA.type]⟩ := by
    simp [invoke, hb]
  rw [hinv]
  have hstep := Step.callRefFunc (P := P) (host := host) (f := {})
    (c := .callRefType fA.type) (vs := args.map toVal) trivial hb hexp (by simpa using hps) hcode
  rw [← hrts] at hstep
  exact (Relation.ReflTransGen.single hstep).trans
    (run_frameT P host mi ma fi hC hK fn ty hty ha hok h _ he _)

/-! ## The moving `cabi_realloc` -/

/-- A call whose results have the types `[i32]` returns one `i32`. -/
theorem returns_one_i32 {M : CoreInst} (hC : CallsTyped M rt) {g : String} (hA : rt g = [tI32])
    (args : List Flat) : RM.Returns (M.call g args) fun r => ∃ p, r = [Flat.i32 p] := by
  intro s r s' h
  have ht := hC g args r s s' h
  rw [hA] at ht
  match r, ht with
  | [⟨.int .i32, p⟩], _ => exact ⟨p, rfl⟩

theorem realloc_core (hC : CallsTyped (realInst H P host mi ma) rt)
    (hK : CallsKeepMem P host mi ma) (alloc : String) (hA : rt alloc = [tI32])
    (hty : tyExec rt ([tI32, tI32, tI32, tI32] ++ List.replicate (reallocShimX alloc).locals tI32)
      (reallocShimX alloc).body [] = some [tI32]) (ty : Nat)
    {old os al ns : BitVec 32} {rs : List Flat} {s s' : Store H} (hok : MemOk ma s)
    (h : reallocEmu (realInst H P host mi ma) alloc old os al ns s (.ok rs s')) {b : Nat}
    {fA : FuncInst H} (hb : s.funcs[b]? = some fA)
    (hcode : fA.code = .wasm ((reallocShimX alloc).toLime fi ty).toCore)
    (he : FrameEnv mi ma fi { module := fA.module })
    {ps rts' : Silmaril.Wasm.Validation.Ty (.list .val)}
    (hexp : Silmaril.Wasm.Validation.Expand fA.type (.func ps rts'))
    (hps : 4 = ps.length) (hrts : rs.length = rts'.length) :
    Steps P host (invoke s b ([Flat.i32 old, Flat.i32 os, Flat.i32 al, Flat.i32 ns].map toVal))
      ⟨s', {}, vals (rs.map toVal)⟩ := by
  have hrun : (reallocShimX alloc).run (realInst H P host mi ma)
      [Flat.i32 old, Flat.i32 os, Flat.i32 al, Flat.i32 ns] s (.ok rs s') := by
    rw [reallocShimX_run _ alloc old os al ns (returns_one_i32 hC hA _)]
    exact h
  exact invoke_xfnT P host mi ma fi hC hK (reallocShimX alloc) ty hty rfl hok hrun hb hcode he
    hexp hps hrts

end Silmaril.Proofs.Wasm.Jco.Real
