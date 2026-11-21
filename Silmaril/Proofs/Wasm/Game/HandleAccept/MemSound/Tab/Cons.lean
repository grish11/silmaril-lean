module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab.Atom
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.ConsLive

/-!
# Proofs: atom tables, the cons writer

* `tabCons_sat`: in a fixed environment `ρ` (no sentinel), `consAtomMod name` meets the writer
  contract with `L = {(a)}` through a table decoding the bytes `68 69` of `<name>(0, 2)` to `a`:
  its handle `r₁` denotes the atom `a`; `nil()` returns `r₂` denoting `()`; `cons(r₁, r₂)`
  returns `r₃` denoting `(a)`, and `accept(r₃)` names it (the proof of `cons_sat` with the atom
  import and its decoder abstracted);
* `tabCons_traces`: the traced session against the counting host `countEnv consOut`;
* `tabCons_sound`, `tabCons_live`.

New proofs (no source).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Cons
  Silmaril.Wasm.Game.HandleAccept.MemSound.Live Silmaril.Wasm.Game.HandleAccept.MemSound.Tab
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

variable {α : Type} {T : AtomTable α} {name : String} {dec : List UInt8 → Option α} {a : α}

/-- The table names none of the non-atom imports. -/
def TabFree (T : AtomTable α) : Prop :=
  T.lookup ("sexp", "nil") = none ∧ T.lookup ("sexp", "cons") = none ∧
    T.lookup ("sexp", "accept") = none

/-! ## The decoder -/

theorem tabConsWrite_isWrite {o : Callout} {w : HostReply} {e : WEv (ConsOp α) (BitVec 32)}
    (h : tabConsWrite T {} o w = some e) : ∃ op args r, e = .write op args r := by
  unfold tabConsWrite at h
  rcases hr : replyI32 w with _ | r
  · simp [hr] at h
  · simp only [hr] at h
    split at h
    · simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨_, _, _, _, _, _, rfl⟩ := h
      exact ⟨_, _, _, rfl⟩
    · split_ifs at h
      all_goals
        simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
          Option.some.injEq] at h
        aesop

theorem tabConsWrite_atom (hT : T.lookup ("sexp", name) = some (.seg dec))
    (hd : dec [0x68, 0x69] = some a) {o : Callout} {r : BitVec 32} {mem : Option ByteArray}
    (hi : o.imp = ("sexp", name)) (hb : o.bytes32 = some [0x68, 0x69]) :
    tabConsWrite T {} o ⟨.values [.i32 r], mem⟩ = some (.write (.atom a) [] r) := by
  have hr : replyI32 ⟨.values [.i32 r], mem⟩ = some r := rfl
  simp [tabConsWrite, hr, hi, hT, AtomDec.decode, hb, hd]

theorem tabConsWrite_nil (hf : TabFree T) {o : Callout} {r : BitVec 32}
    {mem : Option ByteArray} (hi : o.imp = ("sexp", "nil")) (ha : o.args = []) :
    tabConsWrite T {} o ⟨.values [.i32 r], mem⟩ = some (.write .nil [] r) := by
  have hr : replyI32 ⟨.values [.i32 r], mem⟩ = some r := rfl
  simp [tabConsWrite, hr, hi, ha, hf.1]

theorem tabConsWrite_cons (hf : TabFree T) {o : Callout} {x y r : BitVec 32}
    {mem : Option ByteArray} (hi : o.imp = ("sexp", "cons")) (ha : o.args = [.i32 x, .i32 y]) :
    tabConsWrite T {} o ⟨.values [.i32 r], mem⟩ = some (.write .cons [x, y] r) := by
  have hr : replyI32 ⟨.values [.i32 r], mem⟩ = some r := rfl
  unfold tabConsWrite
  rw [hr]
  simp [hi, ha, hf.2.1, Callout.args2, Callout.i32?, Val.i32]

/-! ## The instantiated module -/

/-- The shape of the instantiated module. -/
def consAtomOk (name : String) : Bool :=
  match prep (consAtomMod name) with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [4] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂, f₃, f₄] => stubOk 0 2 f₀ && stubOk 1 0 f₁ && stubOk 2 2 f₂ &&
          stubOk 3 1 f₃ && fnOk [] consBody 0 0 [0, 1, 2, 3, 4] [0] [] f₄
       | _ => false)
  | none => false

theorem consAtomOk_of (hn : name ∈ atomNames) : consAtomOk name = true := by
  simp only [atomNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem consAtomSpec_of (hn : name ∈ atomNames) :
    (Silmaril.Wasm.Verify.specInstance? (consAtomMod name)).isSome = true := by
  simp only [atomNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem consAtomMem_of (hn : name ∈ atomNames) : memSizes (consAtomMod name) = [65536] := by
  simp only [atomNames, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl <;> decide +kernel

theorem consAtom_facts (hn : name ∈ atomNames) {c : Config Nat} {st : Option FuncIdx}
    (hp : prep (consAtomMod name) = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [4] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂ f₃ f₄, c.store.funcs = [f₀, f₁, f₂, f₃, f₄] ∧
      stubOk 0 2 f₀ = true ∧ stubOk 1 0 f₁ = true ∧ stubOk 2 2 f₂ = true ∧
      stubOk 3 1 f₃ = true ∧ fnOk [] consBody 0 0 [0, 1, 2, 3, 4] [0] [] f₄ = true := by
  have h := consAtomOk_of hn
  unfold consAtomOk at h
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
def consAtomInv (name : String) (s : Store Nat) : Prop :=
  ∃ c st, prep (consAtomMod name) = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The writer contract in the fixed environment `ρ`. -/
abbrev tabConsK (T : AtomTable α) (a : α) (ρ : Env (BitVec 32) (SExp2 α)) :
    MemContract (WEv (ConsOp α) (BitVec 32)) :=
  roleWriterContract (tabConsRoles T {}) (consW α) none ρ {.cons (.atom a) .nil} consReply

/-- Calls of other imports than `accept` are always allowed. -/
theorem tab_pre_other {ρ : Env (BitVec 32) (SExp2 α)} {i : Import} {s : Store Nat}
    {args : List Val} (hi : (i.moduleName, i.name) ≠ ("sexp", "accept")) :
    (tabConsK T a ρ).pre (calloutIn i (some 0) s args) := by
  intro h hd
  change tabAccept {} _ = _ at hd
  rw [tabAccept_none hi] at hd
  cases hd

/-- **The body of `run`**, in the fixed environment `ρ`. -/
theorem tabCons_body {P : Profile} (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hf : TabFree T) {ρ : Env (BitVec 32) (SExp2 α)}
    {f₀ f₁ f₂ f₃ : FuncInst Nat} (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 0 f₁ = true)
    (h2 : stubOk 2 2 f₂ = true) (h3 : stubOk 3 1 f₃ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3, 4]) (hFm : F.module.mems = [0])
    {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁, f₂, f₃] ++ fs.drop 4) (hsf : s.funcs = fs) (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → consAtomInv name s') {Q : Post Nat}
    (hQ : BodyExits (consAtomInv name) Q) :
    HWP P (memHost (consAtomMod name) (some 0) (tabConsRoles T {}) (tabConsK T a ρ)) s F
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
  -- <name>(0, 2)
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine hwp_call (us := []) (args := [.i32 0, .i32 2]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := ⟨"sexp", name, .func ⟨0⟩⟩) (by rw [hFf]; rfl) (hfk _ hfs₁).1 hc₀ he₀ (by simp [hn₀])
    rfl (tab_pre_other (Tab.accept_ne_of hn)) ?_
  rintro s₂ r ⟨⟨hfs₂, hml₂⟩, hshape⟩ hans
  have hfs₂' : s₂.funcs = fs := hfs₂.trans hfs₁
  have hml₂' : s₂.mems.length = 1 := hml₂.trans hl₁
  refine ⟨fun res hr => ?_, fun _ => htrap s₂ F hfs₂' hml₂',
    fun a _ => hthrow s₂ F a hfs₂' hml₂'⟩
  obtain ⟨r₁, rfl⟩ := (hshape res hr).1 (.inl rfl)
  subst hr
  have hρ₁ : ρ r₁ = some (.atom a) := by
    have hb : (calloutIn ⟨"sexp", name, .func ⟨0⟩⟩ (some 0) (s.setMem 0 { mi with bytes := b })
        [.i32 0, .i32 2]).bytes32 = some [0x68, 0x69] := by
      rw [bytes32_of_store hml hst rfl]
      decide
    rcases hans _ (tabConsWrite_atom hT hd rfl hb) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, consW] at ht
      rw [hρ, ← ht]
  -- nil()
  refine hwp_call (us := [.i32 r₁]) (args := []) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := impNil) (by rw [hFf]; rfl) (hfk _ hfs₂').2.1 hc₁ he₁ (by simp [hn₁]) rfl
    (tab_pre_other (by decide)) ?_
  rintro s₃ r ⟨⟨hfs₃, hml₃⟩, hshape⟩ hans
  have hfs₃' : s₃.funcs = fs := hfs₃.trans hfs₂'
  have hml₃' : s₃.mems.length = 1 := hml₃.trans hml₂'
  refine ⟨fun res hr => ?_, fun _ => htrap s₃ F hfs₃' hml₃',
    fun a _ => hthrow s₃ F a hfs₃' hml₃'⟩
  obtain ⟨r₂, rfl⟩ := (hshape res hr).1 (.inr (.inl rfl))
  subst hr
  have hρ₂ : ρ r₂ = some .nil := by
    rcases hans _ (tabConsWrite_nil hf rfl rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, consW] at ht
      rw [hρ, ← ht]
  -- cons(r₁, r₂)
  refine hwp_call (us := []) (args := [.i32 r₁, .i32 r₂]) (x := ⟨2⟩) (k := 2) (fk := f₂)
    (i := impCons) (by rw [hFf]; rfl) (hfk _ hfs₃').2.2.1 hc₂ he₂ (by simp [hn₂]) rfl
    (tab_pre_other (by decide)) ?_
  rintro s₄ r ⟨⟨hfs₄, hml₄⟩, hshape⟩ hans
  have hfs₄' : s₄.funcs = fs := hfs₄.trans hfs₃'
  have hml₄' : s₄.mems.length = 1 := hml₄.trans hml₃'
  refine ⟨fun res hr => ?_, fun _ => htrap s₄ F hfs₄' hml₄',
    fun a _ => hthrow s₄ F a hfs₄' hml₄'⟩
  obtain ⟨r₃, rfl⟩ := (hshape res hr).1 (.inr (.inr rfl))
  subst hr
  have hρ₃ : ρ r₃ = some (.cons (.atom a) .nil) := by
    rcases hans _ (tabConsWrite_cons hf rfl rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, consW, hρ₁, hρ₂] at ht
      rw [hρ, ← ht]
  -- accept(r₃)
  refine hwp_call (us := []) (args := [.i32 r₃]) (x := ⟨3⟩) (k := 3) (fk := f₃)
    (i := impAcc) (by rw [hFf]; rfl) (hfk _ hfs₄').2.2.2 hc₃ he₃ (by simp [hn₃]) rfl ?_ ?_
  · intro h hd t ht
    simp [tabConsRoles, tabAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32] at hd
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

/-- **`consAtomMod name` meets the writer contract** in every fixed environment. -/
theorem tabCons_sat (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hf : TabFree T) (ρ : Env (BitVec 32) (SExp2 α)) :
    MemSat P (consAtomMod name) 0 (tabConsRoles T {}) (tabConsK T a ρ) (consAtomInv name) := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, f₄, hf', h0, h1, h2, h3, h4⟩ :=
    consAtom_facts hn hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a' ha
  rw [← haddr, hexp] at ha
  obtain rfl : a' = 4 := by simpa using ha
  obtain ⟨code, ps, rs, hcode4, hloc, hbody, he, hps, hrs, hfuncs, hmems4, -⟩ := fnOk_spec h4
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → consAtomInv name s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, consAtomInv name s → s.funcs = c.store.funcs := by
    rintro s ⟨c', st', hp', hfs, _⟩
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc]
  refine export_valid (fi := f₄) (fun s hs => by rw [hfi s hs, hf']; rfl) hcode4 he hrs ?_
  intro s args hs hok Q hQ
  have hargs : args = [] := by
    have := args_length (by rw [hfi s hs, hf']; rfl) he hok
    rw [hps] at this
    exact List.eq_nil_of_length_eq_zero this
  subst hargs
  rw [hbody, hloc]
  have hml' : s.mems.length = 1 := by obtain ⟨_, _, _, _, h⟩ := hs; exact h
  exact tabCons_body hn hT hd hf h0 h1 h2 h3 (by simp [Frame.forCall, hfuncs])
    (by simp [Frame.forCall, hmems4]) (fs := c.store.funcs) (by rw [hf']; rfl) (hfi s hs)
    hml' hinv hQ

/-- **`consAtomMod name` writes only `(a)`** (no sentinel, no undefined behaviour). -/
theorem tabCons_sound (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hf : TabFree T) {pol : Policy (BitVec 32)} (hs : pol.sentinel = none)
    (hw : pol.onWrite ≠ .ub) (ha : pol.onAccept ≠ .ub) :
    tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod name) T {} pol ⊆
      {.cons (.atom a) .nil} :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons.rolesWriterLang_subset
    (fun _ _ h => tabAccept_isAccept h) (fun _ _ _ h => tabConsWrite_isWrite h)
    (fun ρ => by rw [hs]; exact tabCons_sat P hn hT hd hf ρ) (fun _ _ h => h) hw ha

/-! ## The session -/

/-- **The writer trace of the session.** -/
theorem tabCons_traces (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hf : TabFree T) (q : BitVec 32) :
    [.enter, .write (.atom a) [] q, .write .nil [] (q + 1),
      .write .cons [q, q + 1] (q + 1 + 1), .accept (q + 1 + 1)] ∈
      tabConsTraces P (ReplyEnvs consReply) 0 (consAtomMod name) T {} := by
  obtain ⟨mt, Is, c₀, hI⟩ := spec_exists (consAtomSpec_of hn)
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, f₄, hf', h0, h1, h2, h3, h4⟩ :=
    consAtom_facts hn hp
  obtain ⟨mi, hmis, hsize⟩ := one_page (consAtomMem_of hn) hp
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  obtain ⟨ps₃, rs₃, hc₃, he₃, hn₃⟩ := stubOk_spec h3
  obtain ⟨code, ps, rs, hcode4, hloc, hbody, he, hps, hrs, hfuncs, hmems4, -⟩ := fnOk_spec h4
  rw [show c.withStart none = c from rfl] at hI
  have hmem0 : c.frame.module.mems[0]? = some 0 := by rw [hmems]; rfl
  have hmi : c.store.mems[0]? = some mi := by rw [hmis]; rfl
  let L := countEnv consOut
  let R := tabConsRoles T {}
  have t₀ : TSession P L (consAtomMod name) (some 0) R c q Is.addrs .inst false (c, q) [] :=
    .start
  have hf4 : c.store.funcs[4]? = some f₄ := by rw [hf']; rfl
  have hok : InvokeOk c.store 4 [] := ⟨f₄, ps, rs, hf4, he, by
    rw [List.eq_nil_of_length_eq_zero (l := ps.toList) hps]; exact .nil⟩
  have ha : 4 ∈ Is.addrs := by rw [← haddr, hexp]; simp
  have t₁ := TSession.invoke t₀ (by decide) ⟨[], hcode⟩ ha hok
  let F : Frame := Frame.forCall f₄.module [] []
  have hFf : F.module.funcs = [0, 1, 2, 3, 4] := by simp [F, Frame.forCall, hfuncs]
  have hFm : F.module.mems = [0] := by simp [F, Frame.forCall, hmems4]
  have st₀ : Step P NH (invoke c.store 4 [])
      ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression consBody)]]⟩ := by
    have h := Step.callRefFunc (P := P) (host := NH) (s := c.store) (f := {})
      (c := .callRefType ((c.store.funcs[4]?.map FuncInst.type).getD default)) (vs := [])
      (a := 4) (fi := f₄) (code := code) trivial hf4 he (by rw [hps]; rfl) hcode4
    rw [hrs, hloc, hbody] at h
    exact h
  -- "hi" at 0
  obtain ⟨b, hst⟩ := store_some (B := mi.bytes) (a := effAddr (0 : BitVec 32).toNat ⟨0, 0⟩)
    (n := PackSize.i16.width / 8) ((0x6968 : BitVec 32).setWidth _) (by rw [hsize]; decide)
  let s₁ := c.store.setMem 0 { mi with bytes := b }
  obtain ⟨-, hl₁, hfs₁⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  have hfk : s₁.funcs[0]? = some f₀ ∧ s₁.funcs[1]? = some f₁ ∧ s₁.funcs[2]? = some f₂ ∧
      s₁.funcs[3]? = some f₃ := by rw [hfs₁, hf']; exact ⟨rfl, rfl, rfl, rfl⟩
  have st₁ : Step P NH ⟨c.store, {}, [.frame 0 F [.label 0 [] (expression consBody)]]⟩
      ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (consBody.drop 3))]]⟩ :=
    step_body (step_mid [] _ (step_storePack hFm hmi hst))
  -- <name>(0, 2)
  have st₂ : Step P NH ⟨s₁, {}, [.frame 0 F [.label 0 [] (expression (consBody.drop 3))]]⟩
      ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 6))).fill
        (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ :=
    step_body (step_mid [.i32 0, .i32 2] (expression (consBody.drop 6))
      (step_call (x := ⟨0⟩) (by rw [hFf]; rfl) hfk.1))
  have hd₁ : decompose? s₁ ((bodyCtx F (expression (consBody.drop 6))).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])) =
      some (bodyCtx F (expression (consBody.drop 6)), 0, 0, [.i32 0, .i32 2]) :=
    decompose_fill _ trivial hfk.1 he₀ (by rw [hn₀]; rfl) hc₀
  have t₂ := TSession.call (TSession.of_core_steps t₁
    ((st₀.steps.trans st₁.steps).trans st₂.steps)) hd₁
  have t₃ := TSession.answer t₂ hd₁ (a := ⟨s₁, .values [.i32 q]⟩) (q' := q + 1) ⟨rfl, rfl⟩
  -- nil()
  let E₂ : Ctx := .frame [] 0 F (.label [] 0 [] (.top [.i32 q] (expression (consBody.drop 7)))
    []) []
  have st₃ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 6))).fill
      (Result.values [.i32 q]).toAdmin⟩
      ⟨s₁, {}, E₂.fill (vals [] ++ [.ref (.func 1), .callRefType f₁.type])⟩ :=
    step_body (step_mid [.i32 q] (expression (consBody.drop 7))
      (step_call (x := ⟨1⟩) (by rw [hFf]; rfl) hfk.2.1))
  have hd₂ : decompose? s₁ (E₂.fill (vals [] ++ [.ref (.func 1), .callRefType f₁.type])) =
      some (E₂, 1, 1, []) :=
    decompose_fill _ trivial hfk.2.1 he₁ (by rw [hn₁]; rfl) hc₁
  have t₄ := TSession.call (TSession.of_core_steps t₃ st₃.steps) hd₂
  have t₅ := TSession.answer t₄ hd₂ (a := ⟨s₁, .values [.i32 (q + 1)]⟩) (q' := q + 1 + 1)
    ⟨rfl, rfl⟩
  -- cons(q, q + 1)
  have st₄ : Step P NH ⟨s₁, {}, E₂.fill (Result.values [.i32 (q + 1)]).toAdmin⟩
      ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 8))).fill
        (vals [.i32 q, .i32 (q + 1)] ++ [.ref (.func 2), .callRefType f₂.type])⟩ :=
    step_body (step_mid [.i32 q, .i32 (q + 1)] (expression (consBody.drop 8))
      (step_call (x := ⟨2⟩) (by rw [hFf]; rfl) hfk.2.2.1))
  have hd₃ : decompose? s₁ ((bodyCtx F (expression (consBody.drop 8))).fill
      (vals [.i32 q, .i32 (q + 1)] ++ [.ref (.func 2), .callRefType f₂.type])) =
      some (bodyCtx F (expression (consBody.drop 8)), 2, 2, [.i32 q, .i32 (q + 1)]) :=
    decompose_fill _ trivial hfk.2.2.1 he₂ (by rw [hn₂]; rfl) hc₂
  have t₆ := TSession.call (TSession.of_core_steps t₅ st₄.steps) hd₃
  have t₇ := TSession.answer t₆ hd₃ (a := ⟨s₁, .values [.i32 (q + 1 + 1)]⟩)
    (q' := q + 1 + 1 + 1) ⟨rfl, rfl⟩
  -- accept(q + 2)
  have st₅ : Step P NH ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 8))).fill
      (Result.values [.i32 (q + 1 + 1)]).toAdmin⟩
      ⟨s₁, {}, (bodyCtx F []).fill
        (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 3), .callRefType f₃.type])⟩ :=
    step_body (step_mid [.i32 (q + 1 + 1)] [] (step_call (x := ⟨3⟩) (by rw [hFf]; rfl)
      hfk.2.2.2))
  have hd₄ : decompose? s₁ ((bodyCtx F []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 3), .callRefType f₃.type])) =
      some (bodyCtx F [], 3, 3, [.i32 (q + 1 + 1)]) :=
    decompose_fill _ trivial hfk.2.2.2 he₃ (by rw [hn₃]; rfl) hc₃
  have t₈ := TSession.call (TSession.of_core_steps t₇ st₅.steps) hd₄
  -- the decoded events
  have hco₁ : calloutAt? (consAtomMod name) (some 0)
      ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 6))).fill
      (vals [.i32 0, .i32 2] ++ [.ref (.func 0), .callRefType f₀.type])⟩ =
      some (co name ⟨0⟩ s₁ [.i32 0, .i32 2]) := by
    unfold calloutAt?; rw [hd₁]; rfl
  have hco₂ : calloutAt? (consAtomMod name) (some 0)
      ⟨s₁, {}, E₂.fill (vals [] ++ [.ref (.func 1), .callRefType f₁.type])⟩ =
      some (co "nil" ⟨3⟩ s₁ []) := by
    unfold calloutAt?; rw [hd₂]; rfl
  have hco₃ : calloutAt? (consAtomMod name) (some 0)
      ⟨s₁, {}, (bodyCtx F (expression (consBody.drop 8))).fill
      (vals [.i32 q, .i32 (q + 1)] ++ [.ref (.func 2), .callRefType f₂.type])⟩ =
      some (co "cons" ⟨0⟩ s₁ [.i32 q, .i32 (q + 1)]) := by
    unfold calloutAt?; rw [hd₃]; rfl
  have hco₄ : calloutAt? (consAtomMod name) (some 0) ⟨s₁, {}, (bodyCtx F []).fill
      (vals [.i32 (q + 1 + 1)] ++ [.ref (.func 3), .callRefType f₃.type])⟩ =
      some (co "accept" ⟨1⟩ s₁ [.i32 (q + 1 + 1)]) := by
    unfold calloutAt?; rw [hd₄]; rfl
  have hb : (co name ⟨0⟩ s₁ [.i32 0, .i32 2]).bytes32 = some [0x68, 0x69] := by
    rw [bytes32_of_store hml hst rfl]
    decide
  have hw₁ := tabConsWrite_atom (r := q) (mem := memOf (some 0) s₁) hT hd rfl hb
  have hw₂ := tabConsWrite_nil (o := co "nil" ⟨3⟩ s₁ []) (r := q + 1)
    (mem := memOf (some 0) s₁) hf rfl rfl
  have hw₃ := tabConsWrite_cons (o := co "cons" ⟨0⟩ s₁ [.i32 q, .i32 (q + 1)])
    (r := q + 1 + 1) (mem := memOf (some 0) s₁) hf rfl rfl
  have hna₁ : tabAccept (Op := ConsOp α) {} (co name ⟨0⟩ s₁ [.i32 0, .i32 2]) = none :=
    tabAccept_none (Tab.accept_ne_of hn)
  have hna₂ : tabAccept (Op := ConsOp α) {} (co "nil" ⟨3⟩ s₁ []) = none :=
    tabAccept_none (by show ("sexp", "nil") ≠ ("sexp", "accept"); decide)
  have hna₃ : tabAccept (Op := ConsOp α) {} (co "cons" ⟨0⟩ s₁ [.i32 q, .i32 (q + 1)]) = none :=
    tabAccept_none (by show ("sexp", "cons") ≠ ("sexp", "accept"); decide)
  have hac : tabAccept (Op := ConsOp α) {} (co "accept" ⟨1⟩ s₁ [.i32 (q + 1 + 1)]) =
      some (.accept (q + 1 + 1)) :=
    tabAccept_acc _ _ rfl rfl
  rw [hco₁, hco₂, hco₃, hco₄] at t₈
  refine ⟨_, ⟨mt, Is, c, hI, L, q, countEnv_reply consOut_shape _, .run, true, _,
    by rw [hmem0]; exact t₈⟩, ?_⟩
  simp only [Option.elim, Roles.callTags, Roles.answerTags, R, tabConsRoles]
  rw [hna₁, hw₁, hna₂, hw₂, hna₃, hw₃, hac]
  rfl

/-- **`consAtomMod name` writes `(a)`**, for every profile and policy. -/
theorem tabCons_live (P : Profile) (hn : name ∈ atomNames)
    (hT : T.lookup ("sexp", name) = some (.seg dec)) (hd : dec [0x68, 0x69] = some a)
    (hf : TabFree T) (pol : Policy (BitVec 32)) :
    .cons (.atom a) .nil ∈ tabConsWriterLang P (ReplyEnvs consReply) 0 (consAtomMod name) T {}
      pol := by
  let q := base pol
  have hn₀ : pol.sentinel ≠ some q := by simpa using base_ne pol (k := 0) (by decide)
  have hn₁ : pol.sentinel ≠ some (q + 1) := base_ne pol (k := 1) (by decide)
  have hn₂ : pol.sentinel ≠ some (q + 1 + 1) := by
    rw [BitVec.add_assoc]; exact base_ne pol (k := 1 + 1) (by decide)
  have d₁ : q + 1 ≠ q := by bv_omega
  have d₂ : q + 1 + 1 ≠ q := by bv_omega
  have d₃ : q + 1 + 1 ≠ q + 1 := by bv_omega
  have e₁ : Function.update (Env.empty : Env (BitVec 32) (SExp2 α)) q
      (some (.atom a)) (q + 1) = none := by
    rw [Function.update_of_ne d₁]; rfl
  have e₂ : Function.update (Function.update (Env.empty : Env (BitVec 32) (SExp2 α)) q
      (some (.atom a))) (q + 1) (some .nil) (q + 1 + 1) = none := by
    rw [Function.update_of_ne d₃, Function.update_of_ne d₂]; rfl
  have hb : (consW α).built (Function.update (Function.update
      (Env.empty : Env (BitVec 32) (SExp2 α)) q (some (.atom a))) (q + 1)
      (some .nil)) .cons [q, q + 1] = some (.cons (.atom a) .nil) := by
    simp [Writer.built, Env.lookupAll, consW]
  simp only [tabConsWriterLang, writerLang, Host.lang]
  refine Set.mem_biUnion (tabCons_traces P hn hT hd hf q) ⟨_, _, .cons .enter
    (.cons (.writeOk (t := .atom a) rfl ⟨hn₀, .inl rfl⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := .nil) rfl ⟨hn₁, .inl e₁⟩ fun _ h => by cases h)
    (.cons (.writeOk (t := .cons (.atom a) .nil) hb ⟨hn₂, .inl e₂⟩ fun _ h => by cases h)
    (.cons (.acceptOk (t := .cons (.atom a) .nil) (by simp)) (.nil _))))), by simp⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Tab
