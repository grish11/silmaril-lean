module

public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons

/-!
# Proofs: the cons API through linear memory with mixed atom kinds

`consMix_sat`: in a fixed environment `ρ` (no sentinel), `consMix` meets the writer contract with
`L = {(hi "hi")}`: `symbol(0, 2)` and `string(0, 2)` each observe `68 69` (stored again before
each call, since the host may rewrite memory), so their handles denote the symbol `hi` and the
string `"hi"`; `nil()`, `cons` and `cons` build `(hi "hi")`, which `accept` names.
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

theorem consWrite_string {o : Callout} {r : BitVec 32} {mem : Option ByteArray}
    (hi : o.imp = ("sexp", "string")) (hb : o.bytes32 = some [0x68, 0x69]) :
    consWrite {} o ⟨.values [.i32 r], mem⟩ = some (.write (.atom hiStr) [] r) := by
  have hr : replyI32 ⟨.values [.i32 r], mem⟩ = some r := rfl
  simp [consWrite, hr, hi, hb, hi_utf8, hiStr]

/-- The shape of the instantiated module. -/
def consMixOk : Bool :=
  match prep consMix with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [5] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂, f₃, f₄, f₅] => stubOk 0 2 f₀ && stubOk 1 2 f₁ && stubOk 2 0 f₂ &&
          stubOk 3 2 f₃ && stubOk 4 1 f₄ && fnOk [] consMixBody 0 0 [0, 1, 2, 3, 4, 5] [0] [] f₅
       | _ => false)
  | none => false

theorem consMixOk_true : consMixOk = true := by decide +kernel

theorem consMix_facts {c : Config Nat} {st : Option FuncIdx}
    (hp : prep consMix = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [5] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂ f₃ f₄ f₅, c.store.funcs = [f₀, f₁, f₂, f₃, f₄, f₅] ∧
      stubOk 0 2 f₀ = true ∧ stubOk 1 2 f₁ = true ∧ stubOk 2 0 f₂ = true ∧
      stubOk 3 2 f₃ = true ∧ stubOk 4 1 f₄ = true ∧
      fnOk [] consMixBody 0 0 [0, 1, 2, 3, 4, 5] [0] [] f₅ = true := by
  have h := consMixOk_true
  unfold consMixOk at h
  rw [hp] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  split at h6
  · rename_i f₀ f₁ f₂ f₃ f₄ f₅ hf
    simp only [Bool.and_eq_true] at h6
    exact ⟨f₀, f₁, f₂, f₃, f₄, f₅, hf, h6.1.1.1.1.1, h6.1.1.1.1.2, h6.1.1.1.2, h6.1.1.2,
      h6.1.2, h6.2⟩
  · cases h6

/-- The store invariant: the instantiated functions and one memory. -/
def consMixInv (s : Store Nat) : Prop :=
  ∃ c st, prep consMix = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-- The writer contract in the fixed environment `ρ`. -/
abbrev consMixK (ρ : Env (BitVec 32) (SExp2 MemAtom)) : MemContract ConsWEv :=
  roleWriterContract (consRoles {}) (consW MemAtom) none ρ {mixList} consMixReply

abbrev impStr : Import := ⟨"sexp", "string", .func ⟨0⟩⟩

theorem mix_pre_other {ρ : Env (BitVec 32) (SExp2 MemAtom)} {i : Import} {s : Store Nat}
    {args : List Val} (hi : (i.moduleName, i.name) ≠ ("sexp", "accept")) :
    (consMixK ρ).pre (calloutIn i (some 0) s args) := by
  intro h hd
  change consAccept {} _ = _ at hd
  rw [consAccept_eq_none hi] at hd
  cases hd

/-- **The body of `run`** in `consMix`, in the fixed environment `ρ`. -/
theorem consMix_body {P : Profile} {ρ : Env (BitVec 32) (SExp2 MemAtom)}
    {f₀ f₁ f₂ f₃ f₄ : FuncInst Nat} (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 2 f₁ = true)
    (h2 : stubOk 2 0 f₂ = true) (h3 : stubOk 3 2 f₃ = true) (h4 : stubOk 4 1 f₄ = true)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2, 3, 4, 5]) (hFm : F.module.mems = [0])
    {s : Store Nat} {fs : List (FuncInst Nat)}
    (hfs : fs = [f₀, f₁, f₂, f₃, f₄] ++ fs.drop 5) (hsf : s.funcs = fs)
    (hml : s.mems.length = 1)
    (hinv : ∀ s', s'.funcs = fs → s'.mems.length = 1 → consMixInv s') {Q : Post Nat}
    (hQ : BodyExits consMixInv Q) :
    HWP P (memHost consMix (some 0) (consRoles {}) (consMixK ρ)) s F
      (vals [] ++ expression consMixBody) Q := by
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  obtain ⟨ps₂, rs₂, hc₂, he₂, hn₂⟩ := stubOk_spec h2
  obtain ⟨ps₃, rs₃, hc₃, he₃, hn₃⟩ := stubOk_spec h3
  obtain ⟨ps₄, rs₄, hc₄, he₄, hn₄⟩ := stubOk_spec h4
  have hfk : ∀ s' : Store Nat, s'.funcs = fs → s'.funcs[0]? = some f₀ ∧
      s'.funcs[1]? = some f₁ ∧ s'.funcs[2]? = some f₂ ∧ s'.funcs[3]? = some f₃ ∧
      s'.funcs[4]? = some f₄ :=
    fun s' h => by rw [h, hfs]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have htrap : ∀ s' (F' : Frame), s'.funcs = fs → s'.mems.length = 1 → Q s' F' .trap :=
    fun s' F' h h' => (hQ s' (hinv s' h h') F').2.2.1
  have hthrow : ∀ s' (F' : Frame) a, s'.funcs = fs → s'.mems.length = 1 → Q s' F' (.throw a) :=
    fun s' F' a h h' => (hQ s' (hinv s' h h') F').2.2.2 a
  unfold consMixBody
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
    (mix_pre_other (by decide)) ?_
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
  -- "hi" at 0 again
  refine X.i32Const (us := [.i32 r₁]) ?_
  refine X.i32Const (us := [.i32 r₁] ++ [.i32 0]) ?_
  refine X.storePack (us := [.i32 r₁]) hFm hml₂' (htrap s₂ F hfs₂' hml₂')
    fun mi' b' hmi' hst' => ?_
  obtain ⟨-, hl₃, hf₃⟩ := setMem_mems (mi := { mi' with bytes := b' }) hml₂'
  have hfs₃ : (s₂.setMem 0 { mi' with bytes := b' }).funcs = fs := hf₃.trans hfs₂'
  -- string(0, 2)
  refine X.i32Const (us := [.i32 r₁]) ?_
  refine X.i32Const (us := [.i32 r₁] ++ [.i32 0]) ?_
  refine hwp_call (us := [.i32 r₁]) (args := [.i32 0, .i32 2]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := impStr) (by rw [hFf]; rfl) (hfk _ hfs₃).2.1 hc₁ he₁ (by simp [hn₁]) rfl
    (mix_pre_other (by decide)) ?_
  rintro s₄ r ⟨⟨hfs₄, hml₄⟩, hshape⟩ hans
  have hfs₄' : s₄.funcs = fs := hfs₄.trans hfs₃
  have hml₄' : s₄.mems.length = 1 := hml₄.trans hl₃
  refine ⟨fun res hr => ?_, fun _ => htrap s₄ F hfs₄' hml₄',
    fun a _ => hthrow s₄ F a hfs₄' hml₄'⟩
  obtain ⟨r₂, rfl⟩ := (hshape res hr).1 (.inr (.inl rfl))
  subst hr
  have hρ₂ : ρ r₂ = some (.atom hiStr) := by
    have hb : (calloutIn impStr (some 0) (s₂.setMem 0 { mi' with bytes := b' })
        [.i32 0, .i32 2]).bytes32 = some [0x68, 0x69] := by
      rw [bytes32_of_store hml₂' hst' rfl]
      decide
    rcases hans _ (consWrite_string rfl hb) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, consW] at ht
      rw [hρ, ← ht]
  -- nil()
  refine hwp_call (us := [.i32 r₁, .i32 r₂]) (args := []) (x := ⟨2⟩) (k := 2) (fk := f₂)
    (i := impNil) (by rw [hFf]; rfl) (hfk _ hfs₄').2.2.1 hc₂ he₂ (by simp [hn₂]) rfl
    (mix_pre_other (by decide)) ?_
  rintro s₅ r ⟨⟨hfs₅, hml₅⟩, hshape⟩ hans
  have hfs₅' : s₅.funcs = fs := hfs₅.trans hfs₄'
  have hml₅' : s₅.mems.length = 1 := hml₅.trans hml₄'
  refine ⟨fun res hr => ?_, fun _ => htrap s₅ F hfs₅' hml₅',
    fun a _ => hthrow s₅ F a hfs₅' hml₅'⟩
  obtain ⟨r₃, rfl⟩ := (hshape res hr).1 (.inr (.inr (.inl rfl)))
  subst hr
  have hρ₃ : ρ r₃ = some .nil := by
    rcases hans _ (consWrite_nil rfl rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, consW] at ht
      rw [hρ, ← ht]
  -- cons(r₂, r₃)
  refine hwp_call (us := [.i32 r₁]) (args := [.i32 r₂, .i32 r₃]) (x := ⟨3⟩) (k := 3) (fk := f₃)
    (i := impCons) (by rw [hFf]; rfl) (hfk _ hfs₅').2.2.2.1 hc₃ he₃ (by simp [hn₃]) rfl
    (mix_pre_other (by decide)) ?_
  rintro s₆ r ⟨⟨hfs₆, hml₆⟩, hshape⟩ hans
  have hfs₆' : s₆.funcs = fs := hfs₆.trans hfs₅'
  have hml₆' : s₆.mems.length = 1 := hml₆.trans hml₅'
  refine ⟨fun res hr => ?_, fun _ => htrap s₆ F hfs₆' hml₆',
    fun a _ => hthrow s₆ F a hfs₆' hml₆'⟩
  obtain ⟨r₄, rfl⟩ := (hshape res hr).1 (.inr (.inr (.inr rfl)))
  subst hr
  have hρ₄ : ρ r₄ = some (.cons (.atom hiStr) .nil) := by
    rcases hans _ (consWrite_cons rfl rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, consW, hρ₂, hρ₃] at ht
      rw [hρ, ← ht]
  -- cons(r₁, r₄)
  refine hwp_call (us := []) (args := [.i32 r₁, .i32 r₄]) (x := ⟨3⟩) (k := 3) (fk := f₃)
    (i := impCons) (by rw [hFf]; rfl) (hfk _ hfs₆').2.2.2.1 hc₃ he₃ (by simp [hn₃]) rfl
    (mix_pre_other (by decide)) ?_
  rintro s₇ r ⟨⟨hfs₇, hml₇⟩, hshape⟩ hans
  have hfs₇' : s₇.funcs = fs := hfs₇.trans hfs₆'
  have hml₇' : s₇.mems.length = 1 := hml₇.trans hml₆'
  refine ⟨fun res hr => ?_, fun _ => htrap s₇ F hfs₇' hml₇',
    fun a _ => hthrow s₇ F a hfs₇' hml₇'⟩
  obtain ⟨r₅, rfl⟩ := (hshape res hr).1 (.inr (.inr (.inr rfl)))
  subst hr
  have hρ₅ : ρ r₅ = some mixList := by
    rcases hans _ (consWrite_cons rfl rfl) _ _ _ rfl with h | ⟨t, ht, hρ⟩
    · cases h
    · simp [Writer.built, Env.lookupAll, consW, hρ₁, hρ₄] at ht
      rw [hρ, ← ht]
      rfl
  -- accept(r₅)
  refine hwp_call (us := []) (args := [.i32 r₅]) (x := ⟨4⟩) (k := 4) (fk := f₄)
    (i := impAcc) (by rw [hFf]; rfl) (hfk _ hfs₇').2.2.2.2 hc₄ he₄ (by simp [hn₄]) rfl ?_ ?_
  · intro h hd t ht
    simp [consRoles, consAccept, calloutIn, Callout.args1, Callout.i32?, Val.i32] at hd
    subst hd
    rw [hρ₅] at ht
    cases ht
    rfl
  rintro s₈ r ⟨⟨hfs₈, hml₈⟩, hshape⟩ -
  have hfs₈' : s₈.funcs = fs := hfs₈.trans hfs₇'
  have hml₈' : s₈.mems.length = 1 := hml₈.trans hml₇'
  refine ⟨fun res hr => ?_, fun _ => htrap s₈ _ hfs₈' hml₈',
    fun a _ => hthrow s₈ _ a hfs₈' hml₈'⟩
  obtain rfl := (hshape res hr).2 rfl
  exact X.done (hQ s₈ (hinv s₈ hfs₈' hml₈') _).1

/-- **`consMix` meets the writer contract** in every fixed environment, for every profile. -/
theorem consMix_sat (P : Profile) (ρ : Env (BitVec 32) (SExp2 MemAtom)) :
    MemSat P consMix 0 (consRoles {}) (consMixK ρ) consMixInv := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, f₃, f₄, f₅, hf, h0, h1, h2, h3, h4, h5⟩ :=
    consMix_facts hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 5 := by simpa using ha
  obtain ⟨code, ps, rs, hcode5, hloc, hbody, he, hps, hrs, hfuncs, hmems5, -⟩ := fnOk_spec h5
  have hinv : ∀ s', s'.funcs = c.store.funcs → s'.mems.length = 1 → consMixInv s' :=
    fun s' h h' => ⟨c, none, hp, h, h'⟩
  have hfi : ∀ s, consMixInv s → s.funcs = c.store.funcs := by
    rintro s ⟨c', st', hp', hfs, _⟩
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc]
  refine export_valid (fi := f₅) (fun s hs => by rw [hfi s hs, hf]; rfl) hcode5 he hrs ?_
  intro s args hs hok Q hQ
  have hargs : args = [] := by
    have := args_length (by rw [hfi s hs, hf]; rfl) he hok
    rw [hps] at this
    exact List.eq_nil_of_length_eq_zero this
  subst hargs
  rw [hbody, hloc]
  have hml' : s.mems.length = 1 := by obtain ⟨_, _, _, _, h⟩ := hs; exact h
  exact consMix_body h0 h1 h2 h3 h4 (by simp [Frame.forCall, hfuncs])
    (by simp [Frame.forCall, hmems5]) (fs := c.store.funcs) (by rw [hf]; rfl) (hfi s hs)
    hml' hinv hQ

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Cons
