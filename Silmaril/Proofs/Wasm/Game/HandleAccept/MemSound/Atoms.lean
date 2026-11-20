module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms.Defs
public import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.LiveRun

/-!
# Proofs: atom kinds through linear memory

* `rolesLang_subset_of_closed`: the closed-writes bridge for any roles decoding n-ary writes at
  answers and never at calls (`memWriterLang_subset_of_closed` for `memRoles` is one instance;
  `kwRoles` is another).
* `atom_sat`: for every roles `R` and every set `S`, `atomMod name` meets the closed-writes
  contract `rolesClosed R S hiReply` whenever every write decoded from a call of `sexp.<name>`
  observing `68 69` is closed in `S` and calls of `accept` decode no write: the Hoare-logic proof
  of `hiMod` (`Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Hi.hi_body`) with the import
  name and the decoder abstracted.
* `atom_traces`: the traced session of `hiMod` (`LiveHi`) with the import name and the decoder
  abstracted: against the counting host started at `q`, the trace is
  `[enter, write-at-answer q, accept q]`.
* Instances: `string`, `blob` (through `memRoles`), `keyword` (through `kwRoles`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game
  Silmaril.Wasm.Game.Accept Silmaril.Wasm.Game.IOAccept Silmaril.Accept Silmaril.Accept.Handle
  Silmaril.Accept.IO Silmaril.Formats Silmaril.Formats.Api
  Silmaril.Wasm.Game.HandleAccept.Memory Silmaril.Wasm.Game.HandleAccept.MemSound
  Silmaril.Wasm.Game.HandleAccept.MemSound.Hi Silmaril.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Game.HandleAccept.MemSound.Atoms
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Live
  Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Outcome Post)

/-! ## The closed-writes bridge for any roles -/

theorem rolesLang_subset_of_closed {α : Type} {P : Profile} {Envs : Store Nat → SEnv UImp → Prop}
    {memIdx : Nat} {m : Module} {R : Roles Unit (WEv (SxOp α) (BitVec 32)) Unit Unit}
    (hcall : ∀ o op args r, R.callIn o ≠ some (.write op args r))
    {pol : Policy (BitVec 32)} {S : Set (SExp α)} {reply : UCall Nat → UReply → Prop}
    {Inv : Store Nat → Prop} (hsat : MemSat P m memIdx R (rolesClosed R S reply) Inv)
    (hE : ∀ s L, Envs s L → ReplyEnvs reply s L) (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    writerLang (sexpW α) pol (inputsOf (some .enter) '' tagTraces P Envs memIdx m R) ⊆ S := by
  refine Silmaril.Wasm.Game.HandleAccept.Writers.writerLang_subset_of_closed ha hw ?_
  rintro _ ⟨ts, hts, rfl⟩ op args r hm
  obtain ⟨u0, v0, hu0⟩ := List.append_of_mem hm
  obtain ⟨u, v, hd, -⟩ := inputsOf_split (e := WEv.enter) (by simp) hu0
  obtain ⟨o, hpre, hc | ⟨w, hd'⟩⟩ := tagTraces_pre hsat hE hts hd fun _ _ => trivial
  · exact absurd hc (hcall o op args r)
  · exact hpre w op args r hd'

/-! ## The instantiated module -/

/-- The shape of the instantiated module. -/
def atomOk (name : String) : Bool :=
  match prep (atomMod name) with
  | some (c, st) => st.isNone && c.code.isEmpty && c.frame.module.mems == [0] &&
      exportFuncAddrs c.frame.module == [2] && c.store.mems.length == 1 &&
      (match c.store.funcs with
       | [f₀, f₁, f₂] => stubOk 0 2 f₀ && stubOk 1 1 f₁ &&
          fnOk [] hiBody 0 0 [0, 1, 2] [0] [] f₂
       | _ => false)
  | none => false

theorem atom_facts {name : String} (hok : atomOk name = true) {c : Config Nat}
    {st : Option FuncIdx} (hp : prep (atomMod name) = some (c, st)) :
    st = none ∧ c.code = [] ∧ c.frame.module.mems = [0] ∧ exportFuncAddrs c.frame.module = [2] ∧
    c.store.mems.length = 1 ∧ ∃ f₀ f₁ f₂, c.store.funcs = [f₀, f₁, f₂] ∧ stubOk 0 2 f₀ = true ∧
      stubOk 1 1 f₁ = true ∧ fnOk [] hiBody 0 0 [0, 1, 2] [0] [] f₂ = true := by
  have h := hok
  unfold atomOk at h
  rw [hp] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
    List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_⟩
  split at h6
  · rename_i f₀ f₁ f₂ hf
    simp only [Bool.and_eq_true] at h6
    exact ⟨f₀, f₁, f₂, hf, h6.1.1, h6.1.2, h6.2⟩
  · cases h6

/-- The store invariant: the instantiated functions and one memory. -/
def atomInv (name : String) (s : Store Nat) : Prop :=
  ∃ c st, prep (atomMod name) = some (c, st) ∧ s.funcs = c.store.funcs ∧ s.mems.length = 1

/-! ## Every-run proof -/

section Sat

variable {α : Type} {name : String} {R : Roles Unit (WEv (SxOp α) (BitVec 32)) Unit Unit}
  {S : Set (SExp α)}

/-- **The body of `run`** under the closed-writes contract. -/
theorem atom_body {P : Profile} {c : Config Nat} {st : Option FuncIdx}
    (hp : prep (atomMod name) = some (c, st)) {f₀ f₁ f₂ : FuncInst Nat}
    (hf : c.store.funcs = [f₀, f₁, f₂]) (h0 : stubOk 0 2 f₀ = true) (h1 : stubOk 1 1 f₁ = true)
    (hsym : ∀ o : Callout, o.imp = ("sexp", name) → o.bytes32 = some [0x68, 0x69] →
      (rolesClosed R S hiReply).pre o)
    (hacc : ∀ o : Callout, o.imp = ("sexp", "accept") → (rolesClosed R S hiReply).pre o)
    {F : Frame} (hFf : F.module.funcs = [0, 1, 2]) (hFm : F.module.mems = [0]) {s : Store Nat}
    (hs : atomInv name s) {Q : Post Nat} (hQ : BodyExits (atomInv name) Q) :
    HWP P (memHost (atomMod name) (some 0) R (rolesClosed R S hiReply)) s F
      (vals [] ++ expression hiBody) Q := by
  obtain ⟨c', st', hp', hsf, hml⟩ := hs
  have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
  rw [hcc, hf] at hsf
  have hs : atomInv name s := ⟨c, st, hp, by rw [hsf, hf], hml⟩
  have hinv : ∀ s', s'.funcs = s.funcs → s'.mems.length = s.mems.length → atomInv name s' :=
    fun s' h1 h2 => ⟨c, st, hp, by rw [h1, hsf, hf], by rw [h2, hml]⟩
  obtain ⟨ps₀, rs₀, hc₀, he₀, hn₀⟩ := stubOk_spec h0
  obtain ⟨ps₁, rs₁, hc₁, he₁, hn₁⟩ := stubOk_spec h1
  unfold hiBody
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  refine X.storePack (us := []) hFm hml ((hQ s hs F).2.2.1) fun mi b hmi hst => ?_
  obtain ⟨-, hl₁, hf₁⟩ := setMem_mems (mi := { mi with bytes := b }) hml
  refine X.i32Const (us := []) ?_
  refine X.i32Const (us := [] ++ [.i32 0]) ?_
  have hb : (calloutIn ⟨"sexp", name, .func ⟨0⟩⟩ (some 0) (s.setMem 0 { mi with bytes := b })
      [.i32 0, .i32 2]).bytes32 = some [0x68, 0x69] := by
    rw [bytes32_of_store hml hst rfl]
    decide
  refine hwp_call (us := []) (args := [.i32 0, .i32 2]) (x := ⟨0⟩) (k := 0) (fk := f₀)
    (i := ⟨"sexp", name, .func ⟨0⟩⟩) (by rw [hFf]; rfl) (by rw [hf₁, hsf]; rfl) hc₀ he₀
    (by simp [hn₀]) rfl (hsym _ rfl hb) ?_
  rintro s' r ⟨⟨hfs', hml'⟩, hshape⟩ -
  have hs' : atomInv name s' := hinv s' (by rw [hfs', hf₁]) (by rw [hml', hl₁, hml])
  refine ⟨fun res hr => ?_, fun _ => (hQ s' hs' F).2.2.1, fun a _ => (hQ s' hs' F).2.2.2 a⟩
  obtain ⟨v, rfl⟩ := (hshape res hr).1 rfl
  refine hwp_call (us := []) (args := [.i32 v]) (x := ⟨1⟩) (k := 1) (fk := f₁)
    (i := ⟨"sexp", "accept", .func ⟨1⟩⟩) (by rw [hFf]; rfl) (by rw [hfs', hf₁, hsf]; rfl) hc₁
    he₁ (by simp [hn₁]) rfl (hacc _ rfl) ?_
  rintro s'' r' ⟨⟨hfs'', hml''⟩, hshape'⟩ -
  have hs'' : atomInv name s'' := hinv s'' (by rw [hfs'', hfs', hf₁])
    (by rw [hml'', hml', hl₁, hml])
  refine ⟨fun res hr => ?_, fun _ => (hQ s'' hs'' F).2.2.1, fun a _ => (hQ s'' hs'' F).2.2.2 a⟩
  obtain rfl := (hshape' res hr).2 rfl
  exact X.done (hQ s'' hs'' F).1

/-- **`atomMod name` meets the closed-writes contract**, for every profile. -/
theorem atom_sat (P : Profile) (hok : atomOk name = true)
    (hsym : ∀ o : Callout, o.imp = ("sexp", name) → o.bytes32 = some [0x68, 0x69] →
      (rolesClosed R S hiReply).pre o)
    (hacc : ∀ o : Callout, o.imp = ("sexp", "accept") → (rolesClosed R S hiReply).pre o) :
    MemSat P (atomMod name) 0 R (rolesClosed R S hiReply) (atomInv name) := by
  intro mt Is c₀ hI
  obtain ⟨c, st, hp, rfl, -, haddr⟩ := prep_of_spec hI
  obtain ⟨rfl, hcode, hmems, hexp, hml, f₀, f₁, f₂, hf, h0, h1, h2⟩ := atom_facts hok hp
  have hmem : (c.withStart none).frame.module.mems[0]? = some 0 := by
    simp [Config.withStart, hmems]
  rw [hmem]
  refine ⟨fun n => Safe.of_exits (o := .normal []) (by simp [Config.withStart, hcode]; rfl)
    (fun _ _ => ⟨c, none, hp, rfl, hml⟩), ?_⟩
  intro a ha
  rw [← haddr, hexp] at ha
  obtain rfl : a = 2 := by simpa using ha
  obtain ⟨code, ps, rs, hcode2, hloc, hbody, he, -, hrs, hfuncs, hmems2, -⟩ := fnOk_spec h2
  refine export_valid (fi := f₂) (fun s hs => ?_) hcode2 he hrs ?_
  · obtain ⟨c', st', hp', hfs, _⟩ := hs
    have hcc : c' = c := (Prod.mk.inj (Option.some.inj (hp'.symm.trans hp))).1
    rw [hfs, hcc, hf]
    rfl
  · intro s args hs _ Q hQ
    rw [hbody]
    exact atom_body hp hf h0 h1 hsym hacc (by simp [Frame.forCall, hfuncs])
      (by simp [Frame.forCall, hmems2]) hs hQ

end Sat

/-! ## Decoding the atoms -/

/-- A write built from no children is closed in `{atom a}`. -/
theorem closed_atom {α : Type} {a : α} {op : SxOp α} {args : List (BitVec 32)}
    (hop : op = .atom a) (hargs : args = []) :
    Silmaril.Wasm.Game.HandleAccept.Writers.WriteClosed (sexpW α) {.atom a} op args := by
  subst hop hargs
  intro ts y hl hbuild _
  cases ts with
  | nil => cases hbuild; rfl
  | cons _ _ => cases hl

theorem utf8_hi : utf8? [0x68, 0x69] = some "hi" := by decide +kernel

theorem memWrite_string {o : Callout} {w : HostReply} {op : SxOp MemAtom}
    {args : List (BitVec 32)} {r : BitVec 32} (hi : o.imp = ("sexp", "string"))
    (hb : o.bytes32 = some [0x68, 0x69]) (h : memWrite {} o w = some (.write op args r)) :
    op = .atom strAtom ∧ args = [] := by
  unfold memWrite at h
  rcases hr : replyI32 w with _ | r'
  · simp [hr] at h
  · simp only [hr, hi, hb, utf8_hi, Option.bind_eq_bind, Option.bind_some] at h
    simp at h
    exact ⟨h.1.symm, h.2.1⟩

theorem memWrite_blob {o : Callout} {w : HostReply} {op : SxOp MemAtom}
    {args : List (BitVec 32)} {r : BitVec 32} (hi : o.imp = ("sexp", "blob"))
    (hb : o.bytes32 = some [0x68, 0x69]) (h : memWrite {} o w = some (.write op args r)) :
    op = .atom blobAtom ∧ args = [] := by
  unfold memWrite at h
  rcases hr : replyI32 w with _ | r'
  · simp [hr] at h
  · simp only [hr, hi, hb, Option.bind_eq_bind, Option.bind_some] at h
    simp at h
    exact ⟨h.1.symm, h.2.1⟩

theorem kwWrite_keyword {o : Callout} {w : HostReply} {op : SxOp KwAtom}
    {args : List (BitVec 32)} {r : BitVec 32} (hi : o.imp = ("sexp", "keyword"))
    (hb : o.bytes32 = some [0x68, 0x69]) (h : kwWrite {} o w = some (.write op args r)) :
    op = .atom kwAtom ∧ args = [] := by
  unfold kwWrite at h
  rcases hr : replyI32 w with _ | r'
  · simp [hr] at h
  · simp only [hr, hi, hb, utf8_hi, Option.bind_eq_bind, Option.bind_some] at h
    simp at h
    exact ⟨h.1.symm, h.2.1⟩

theorem memWrite_accept {o : Callout} {w : HostReply} (hi : o.imp = ("sexp", "accept")) :
    memWrite {} o w = none :=
  memWrite_eq_none (by rw [hi]; decide) (by rw [hi]; decide) (by rw [hi]; decide)
    (by rw [hi]; decide)

theorem kwWrite_accept {o : Callout} {w : HostReply} (hi : o.imp = ("sexp", "accept")) :
    kwWrite {} o w = none := by
  unfold kwWrite
  rcases replyI32 w with _ | r <;> simp [hi]

theorem kwAccept_not_write (o : Callout) (op : SxOp KwAtom) (args : List (BitVec 32))
    (r : BitVec 32) : kwAccept {} o ≠ some (.write op args r) := by
  unfold kwAccept
  split
  · cases Callout.args1 Callout.i32? o.args <;> simp
  · simp

/-! ## Soundness of the instances -/

theorem atomOk_string : atomOk "string" = true := by decide +kernel
theorem atomOk_blob : atomOk "blob" = true := by decide +kernel
theorem atomOk_keyword : atomOk "keyword" = true := by decide +kernel

/-- `atomMod "string"` accepts only the string `"hi"`. -/
theorem str_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "string") {} pol ⊆ {.atom strAtom} :=
  rolesLang_subset_of_closed (R := memRoles {}) (fun _ _ _ _ => memAccept_not_write)
    (atom_sat P atomOk_string
      (fun _ hi hb _ _ _ _ hw => let ⟨h1, h2⟩ := memWrite_string hi hb hw; closed_atom h1 h2)
      (fun o hi w _ _ _ hw => by
        change memWrite {} o w = _ at hw; rw [memWrite_accept hi] at hw; cases hw))
    (fun _ _ h => h) ha hw

/-- `atomMod "blob"` accepts only the byte string `68 69`. -/
theorem blob_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    memWriterLang P (ReplyEnvs hiReply) 0 (atomMod "blob") {} pol ⊆ {.atom blobAtom} :=
  rolesLang_subset_of_closed (R := memRoles {}) (fun _ _ _ _ => memAccept_not_write)
    (atom_sat P atomOk_blob
      (fun _ hi hb _ _ _ _ hw => let ⟨h1, h2⟩ := memWrite_blob hi hb hw; closed_atom h1 h2)
      (fun o hi w _ _ _ hw => by
        change memWrite {} o w = _ at hw; rw [memWrite_accept hi] at hw; cases hw))
    (fun _ _ h => h) ha hw

/-- `atomMod "keyword"` accepts only the keyword `hi`. -/
theorem kw_sound (P : Profile) {pol : Policy (BitVec 32)} (ha : pol.onAccept ≠ .ub)
    (hw : pol.onWrite ≠ .ub) :
    kwWriterLang P (ReplyEnvs hiReply) 0 (atomMod "keyword") {} pol ⊆ {.atom kwAtom} :=
  rolesLang_subset_of_closed (R := kwRoles {}) kwAccept_not_write
    (atom_sat P atomOk_keyword
      (fun _ hi hb _ _ _ _ hw => let ⟨h1, h2⟩ := kwWrite_keyword hi hb hw; closed_atom h1 h2)
      (fun o hi w _ _ _ hw => by
        change kwWrite {} o w = _ at hw; rw [kwWrite_accept hi] at hw; cases hw))
    (fun _ _ h => h) ha hw

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.Atoms
