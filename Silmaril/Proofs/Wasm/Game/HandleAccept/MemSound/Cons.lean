module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Cons.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Langs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Rules

/-!
# Proofs: the cons API through linear memory

* `rolesFixedLang_subset`, `rolesWriterLang_subset`: the memory writer bridge
  (`memFixedLang_subset`, `memWriterLang_subset`) for any roles decoding accepts at calls and
  writes at answers, and any writer, under `roleWriterContract`.
* `cons_sat`: in a fixed environment `ρ` (no sentinel), `consMod` meets the writer contract
  with `L = {(hi)}`: `symbol(0, 2)` observes `68 69`, the UTF-8 text `hi`, so its handle `r₁`
  denotes the symbol `hi`; `nil()` returns `r₂` denoting `()`; `cons(r₁, r₂)` returns `r₃`
  denoting `(hi)`, and `accept(r₃)` names it.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.Game Silmaril.Wasm.Game.Accept
  Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.IO Silmaril.Accept.Handle
  Silmaril.Accept.Host Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Cons
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-! ## The bridge for any roles -/

section Bridge

variable {Op Y : Type} {W : Writer Op Y} {R : Roles Unit (WEv Op (BitVec 32)) Unit Unit}

/-- **The writer bridge in a fixed environment**, for any roles and writer. -/
theorem rolesFixedLang_subset (hcall : ∀ o e, R.callIn o = some e → ∃ h, e = .accept h)
    (hans : ∀ o w e, R.answerIn o w = some e → ∃ op args r, e = .write op args r)
    {P : Numerics.Profile} {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat} {m : Module}
    {pol : Policy (BitVec 32)} {ρ : Env (BitVec 32) Y} {L : Set Y}
    {reply : UCall Nat → UReply → Prop} {Inv : Store Nat → Prop}
    (hsat : MemSat P m memIdx R (roleWriterContract R W pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) :
    fixedLang W pol {ρ} (inputsOf (some .enter) '' tagTraces P Envs memIdx m R) ⊆ L := by
  intro x hx
  simp only [fixedLang, langOver, Set.mem_iUnion] at hx
  obtain ⟨⟨ρ', hρ'⟩, hx⟩ := hx
  rw [Set.mem_singleton_iff] at hρ'
  subst ρ'
  obtain ⟨t, ⟨ts, hts, rfl⟩, s, A, hr, hxA⟩ := mem_lang.1 hx
  obtain ⟨hwr, hacc⟩ := run_fixed hr ⟨by simp [writer, WState.init],
    fun _ _ h => by simp [writer, WState.init, Env.empty] at h⟩
  obtain ⟨ev, hev, hby⟩ := hacc x hxA
  have hall : ∀ y, Tag.inp y ∈ ts → (roleWriterContract R W pol.sentinel ρ L reply).ans y := by
    rintro y hy op args r rfl
    exact hwr op args r (mem_inputsOf_of_inp hy)
  rcases hby with ⟨h, rfl, hρ⟩ | ⟨h, b, rfl⟩ | rfl | ⟨k, rfl⟩
  · obtain ⟨u, v, hu⟩ := List.append_of_mem hev
    obtain ⟨u', v', hd, -⟩ := inputsOf_split (e := WEv.enter) (by simp) hu
    obtain ⟨o, hpre, hc | ⟨w, hd'⟩⟩ := tagTraces_pre hsat hE hts hd
      fun y hy => hall y (by rw [hd]; exact List.mem_append_left _ hy)
    · exact hpre h hc x hρ
    · obtain ⟨_, _, _, he⟩ := hans _ _ _ hd'; cases he
  all_goals
    rcases mem_inputsOf hev with hi | hi
    · obtain ⟨u, v, hu⟩ := List.append_of_mem hi
      obtain ⟨o, -, hc | ⟨w, hd'⟩⟩ := tagTraces_pre hsat hE hts hu
        fun y hy => hall y (by rw [hu]; exact List.mem_append_left _ hy)
      · obtain ⟨_, he⟩ := hcall _ _ hc; cases he
      · obtain ⟨_, _, _, he⟩ := hans _ _ _ hd'; cases he
    · cases hi

/-- **The writer bridge** (store semantics, no undefined behaviour), for any roles and writer. -/
theorem rolesWriterLang_subset (hcall : ∀ o e, R.callIn o = some e → ∃ h, e = .accept h)
    (hans : ∀ o w e, R.answerIn o w = some e → ∃ op args r, e = .write op args r)
    {P : Numerics.Profile} {Envs : Store Nat → SEnv UImp → Prop} {memIdx : Nat} {m : Module}
    {pol : Policy (BitVec 32)} {L : Set Y} {reply : UCall Nat → UReply → Prop}
    {Inv : Store Nat → Prop}
    (hsat : ∀ ρ, MemSat P m memIdx R (roleWriterContract R W pol.sentinel ρ L reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) (hw : pol.onWrite ≠ .ub)
    (ha : pol.onAccept ≠ .ub) :
    writerLang W pol (inputsOf (some .enter) '' tagTraces P Envs memIdx m R) ⊆ L := by
  intro x hx
  have hx' := writerLang_subset_fixedLang hw ha _ hx
  rw [fixedLang, langOver, Set.mem_iUnion] at hx'
  obtain ⟨⟨ρ, _⟩, hρx⟩ := hx'
  refine rolesFixedLang_subset (pol := {pol with onAccept := .ub}) (ρ := ρ) hcall hans
    (hsat ρ) hE ?_
  simp only [fixedLang, langOver, Set.mem_iUnion]
  exact ⟨⟨ρ, rfl⟩, hρx⟩

end Bridge

/-! ## The cons decoder -/

theorem consAccept_isAccept {ix : ConsImports} {o : Callout} {e : ConsWEv}
    (h : consAccept ix o = some e) : ∃ h, e = .accept h := by
  unfold consAccept at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨h, -, rfl⟩ := h
    exact ⟨h, rfl⟩
  · cases h

theorem consWrite_isWrite {ix : ConsImports} {o : Callout} {w : HostReply} {e : ConsWEv}
    (h : consWrite ix o w = some e) : ∃ op args r, e = .write op args r := by
  unfold consWrite at h
  rcases hr : replyI32 w with _ | r
  · simp [hr] at h
  · simp only [hr] at h
    split_ifs at h
    all_goals
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      aesop

theorem consAccept_eq_none {o : Callout} (h : o.imp ≠ ("sexp", "accept")) :
    consAccept {} o = none := by
  simp [consAccept, h]

theorem hi_utf8 : utf8? [0x68, 0x69] = some "hi" := by decide +kernel

theorem consWrite_symbol {o : Callout} {r : BitVec 32} {mem : Option ByteArray}
    (hi : o.imp = ("sexp", "symbol")) (hb : o.bytes32 = some [0x68, 0x69]) :
    consWrite {} o ⟨.values [.i32 r], mem⟩ = some (.write (.atom hiAtom) [] r) := by
  have hr : replyI32 ⟨.values [.i32 r], mem⟩ = some r := rfl
  simp [consWrite, hr, hi, hb, hi_utf8, hiAtom]

theorem consWrite_nil {o : Callout} {r : BitVec 32} {mem : Option ByteArray}
    (hi : o.imp = ("sexp", "nil")) (ha : o.args = []) :
    consWrite {} o ⟨.values [.i32 r], mem⟩ = some (.write .nil [] r) := by
  have hr : replyI32 ⟨.values [.i32 r], mem⟩ = some r := rfl
  simp [consWrite, hr, hi, ha]

theorem consWrite_cons {o : Callout} {a b r : BitVec 32} {mem : Option ByteArray}
    (hi : o.imp = ("sexp", "cons")) (ha : o.args = [.i32 a, .i32 b]) :
    consWrite {} o ⟨.values [.i32 r], mem⟩ = some (.write .cons [a, b] r) := by
  simp [consWrite, replyI32, hi, ha, Callout.args2, Callout.i32?, Val.i32]

/-! ## The instantiated module -/

/-- The shape of the instantiated module. -/
def consOk : Bool :=
  match prep consMod with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [4] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂, f₃, f₄] => stubOk 0 2 f₀ && stubOk 1 0 f₁ && stubOk 2 2 f₂ &&
          stubOk 3 1 f₃ && fnOk [] consBody 0 0 [0, 1, 2, 3, 4] [0] [] f₄
       | _ => false)
  | none => false

theorem consOk_true : consOk = true := by decide +kernel

theorem cons_facts {c : Config Nat} {st : Option FuncIdx} (hp : prep consMod = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [4] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂ f₃ f₄, c.store.funcs = [f₀, f₁, f₂, f₃, f₄] ∧
      stubOk 0 2 f₀ = true ∧ stubOk 1 0 f₁ = true ∧ stubOk 2 2 f₂ = true ∧
      stubOk 3 1 f₃ = true ∧ fnOk [] consBody 0 0 [0, 1, 2, 3, 4] [0] [] f₄ = true := by
  have h := consOk_true
  unfold consOk at h
  rw [hp] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  split at h6
  · rename_i f₀ f₁ f₂ f₃ f₄ hf
    simp only [Bool.and_eq_true] at h6
    exact ⟨f₀, f₁, f₂, f₃, f₄, hf, h6.1.1.1.1, h6.1.1.1.2, h6.1.1.2, h6.1.2, h6.2⟩
  · cases h6

/-- The store invariant: the instantiated functions and one memory. -/
def consInv (s : Store Nat) : Prop :=
  ∃ c st, prep consMod = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The writer contract in the fixed environment `ρ`. -/
abbrev consK (ρ : Env (BitVec 32) (SExp2 MemAtom)) : MemContract ConsWEv :=
  roleWriterContract (consRoles {}) (consW MemAtom) none ρ {hiList} consReply

abbrev impSym : Import := ⟨"sexp", "symbol", .func ⟨0⟩⟩
abbrev impNil : Import := ⟨"sexp", "nil", .func ⟨3⟩⟩
abbrev impCons : Import := ⟨"sexp", "cons", .func ⟨0⟩⟩
abbrev impAcc : Import := ⟨"sexp", "accept", .func ⟨1⟩⟩

/-- Calls of other imports than `accept` are always allowed. -/
theorem pre_other {ρ : Env (BitVec 32) (SExp2 MemAtom)} {i : Import} {s : Store Nat}
    {args : List Val} (hi : (i.moduleName, i.name) ≠ ("sexp", "accept")) :
    (consK ρ).pre (calloutIn i (some 0) s args) := by
  intro h hd
  change consAccept {} _ = _ at hd
  rw [consAccept_eq_none hi] at hd
  cases hd

/-- **The body of `run`**, in the fixed environment `ρ`. -/
theorem cons_body {P : Profile} {ρ : Env (BitVec 32) (SExp2 MemAtom)}
    {f₀ f₁ f₂ f₃ : FuncInst Nat} (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 0 f₁ = true)
    (h2 : stubOk 2 2 f₂ = true) (h3 : stubOk 3 1 f₃ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3, 4]) (hFm : F.module.mems = [0])
    {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁, f₂, f₃] ++ fs.drop 4) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → consInv s') {Q : Post Nat}
    (hQ : BodyExits consInv Q) :
    HWP P (memHost consMod (some 0) (consRoles {}) (consK ρ)) s F
      (vals [] ++ expression consBody) Q := by
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  obtain ⟨ps₃, rs₃, hc₃, he₃, hn₃⟩ := stubOk_spec h3
  have hfk : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[0]? = some f₀ ∧
      s'.funcs[1]? = some f₁ ∧ s'.funcs[2]? = some f₂ ∧ s'.funcs[3]? = some f₃ :=
    fun s' h => by rw [h, hfs]; exact ⟨rfl, rfl, rfl, rfl⟩
  have htrap : ∀ s' (F' : Frame), s'.funcs = fs → s'.mems.length = 1 → Q s' F' .trap :=
    fun s' F' h h' => (hQ s' (hinv s' h h') F').2.2.1
  have hthrow : ∀ s' (F' : Frame) a, s'.funcs = fs → s'.mems.length = 1 → Q s' F' (.throw a) :=
    fun s' F' a h h' => (hQ s' (hinv s' h h') F').2.2.2 a
  unfold consBody
  -- "hi" at 0
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.storePack (us := []) hFm hml (htrap s F hsf hml) fun mi b hmi hst => ?_
  obtain ⟨-, hl₁, hf₁⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  have hfs₁ : (s.setMem 0 { mi with bytes := b }).funcs = fs := hf₁.trans hsf
  -- symbol(0, 2)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine hwp_call (us := []) (args := [.i32 0, .i32 2]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := impSym) (by rw [hFf]; rfl) (hfk _ hfs₁).1 hc₀ he₀ (by simp [hn₀]) rfl
    (pre_other (by decide)) ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ hans
  have hfs₂' : s₂.funcs = fs := hfs₂.trans hfs₁
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hl₁
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F hfs₂' hml₂',
    fun a _ => hthrow s₂ F a hfs₂' hml₂'⟩
  obtain ⟨r₁, rfl⟩ := (hshape res hr).1 (.inl rfl)
  subst hr
  have hρ₁ : ρ r₁ = some (.atom hiAtom) := by
    have hb : (calloutIn impSym (some 0) (s.setMem 0 { mi with bytes := b })
        [.i32 0, .i32 2]).bytes32 = some [0x68, 0x69] := by
      rw [bytes32_of_store hml hst rfl]
      decide
    rcases hans _ (consWrite_symbol rfl hb) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, consW] at ht
      rw [hρ, ← ht]
  -- nil()
  refine hwp_call (us := [.i32 r₁]) (args := []) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := impNil) (by rw [hFf]; rfl) (hfk _ hfs₂').2.1 hc₁ he₁ (by simp [hn₁]) rfl
    (pre_other (by decide)) ?_
  rintro s₃ r ⟨⟨hfs₃, hml₃⟩, hshape⟩ hans
  have hfs₃' : s₃.funcs = fs := hfs₃.trans hfs₂'
  have hml₃' : s₃.mems.length = 1 := hml₃.trans hml₂'
  refine ⟨fun res hr => ?_, fun _ => htrap s₃ F hfs₃' hml₃',
    fun a _ => hthrow s₃ F a hfs₃' hml₃'⟩
  obtain ⟨r₂, rfl⟩ := (hshape res hr).1 (.inr (.inl rfl))
  subst hr
  have hρ₂ : ρ r₂ = some .nil := by
    rcases hans _ (consWrite_nil rfl rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, consW] at ht
      rw [hρ, ← ht]
  -- cons(r₁, r₂)
  refine hwp_call (us := []) (args := [.i32 r₁, .i32 r₂]) (x := ⟨2⟩) (k := 2) (fk := f₂)
    (i := impCons) (by rw [hFf]; rfl) (hfk _ hfs₃').2.2.1 hc₂ he₂ (by simp [hn₂]) rfl
    (pre_other (by decide)) ?_
  rintro s₄ r ⟨⟨hfs₄, hml₄⟩, hshape⟩ hans
  have hfs₄' : s₄.funcs = fs := hfs₄.trans hfs₃'
  have hml₄' : s₄.mems.length = 1 := hml₄.trans hml₃'
  refine ⟨fun res hr => ?_, fun _ => htrap s₄ F hfs₄' hml₄',
    fun a _ => hthrow s₄ F a hfs₄' hml₄'⟩
  obtain ⟨r₃, rfl⟩ := (hshape res hr).1 (.inr (.inr rfl))
  subst hr
  have hρ₃ : ρ r₃ = some hiList := by
    rcases hans _ (consWrite_cons rfl rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, consW, hρ₁, hρ₂] at ht
      rw [hρ, ← ht]
      rfl
  -- accept(r₃)
  refine hwp_call (us := []) (args := [.i32 r₃]) (x := ⟨3⟩) (k := 3) (fk := f₃)
    (i := impAcc) (by rw [hFf]; rfl) (hfk _ hfs₄').2.2.2 hc₃ he₃ (by simp [hn₃]) rfl ?_ ?_
  · intro h hd t ht
    simp [consRoles, consAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32] at hd
    subst hd
    rw [hρ₃] at ht
    cases ht
    rfl
  rintro s₅ r ⟨⟨hfs₅, hml₅⟩, hshape⟩ -
  have hfs₅' : s₅.funcs = fs := hfs₅.trans hfs₄'
  have hml₅' : s₅.mems.length = 1 := hml₅.trans hml₄'
  refine ⟨fun res hr => ?_, fun _ => htrap s₅ _ hfs₅' hml₅',
    fun a _ => hthrow s₅ _ a hfs₅' hml₅'⟩
  obtain rfl := (hshape res hr).2 rfl
  exact X.done (hQ s₅ (hinv s₅ hfs₅' hml₅') _).1

/-- **`consMod` meets the writer contract** in every fixed environment, for every profile. -/
theorem cons_sat (P : Profile) (ρ : Env (BitVec 32) (SExp2 MemAtom)) :
    MemSat P consMod 0 (consRoles {}) (consK ρ) consInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, f₄, hf, h0, h1, h2, h3, h4⟩ :=
    cons_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 4 := by simpa using ha
  obtain ⟨code, ps, rs, hcode4, hloc, hbody, he, hps, hrs, hfuncs, hmems4, -⟩ := fnOk_spec h4
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → consInv s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, consInv s → s.funcs = c.store.funcs := by
    rintro s ⟨c', st', hp', hfs, _⟩
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc]
  refine export_valid (fi := f₄) (fun s hs => by rw [hfi s hs, hf]; rfl) hcode4 he hrs ?_
  intro s args hs hok Q hQ
  have hargs : args = [] := by
    have := args_length (by rw [hfi s hs, hf]; rfl) he hok
    rw [hps] at this
    exact List.eq_nil_of_length_eq_zero this
  subst hargs
  rw [hbody, hloc]
  have hml' : s.mems.length = 1 := by obtain ⟨_, _, _, _, h⟩ := hs; exact h
  exact cons_body h0 h1 h2 h3 (by simp [Frame.forCall, hfuncs])
    (by simp [Frame.forCall, hmems4]) (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs)
    hml' hinv hQ

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons
