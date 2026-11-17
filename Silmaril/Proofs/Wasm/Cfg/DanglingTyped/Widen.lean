module

public import Silmaril.Wasm.Execution.Core.Typing.Config

@[expose] public section

/-!
# Typing transfer to a store with more exceptions and tags (proofs)

`Widen s t`: `t` agrees with `s` except in its tags and exceptions, the tags of `s` are a prefix
of those of `t`, and every exception address of `s` is one of `t` (contents may differ). Every
typing judgement except `StoreOk` reads exceptions only through their existence and tags only by
lookup, so it transfers from `s` to `t`: references, values, external addresses, module
instances, frames and administrative code.
-/

namespace Silmaril.Wasm.Cfg.Proofs.DanglingTyped

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-- **`t` widens `s`**: equal except tags (a prefix extension) and exceptions (every address of
`s` stays an address). -/
structure Widen (s t : Store H) : Prop where
  eq : t = { s with tags := t.tags, exns := t.exns }
  tags : s.tags <+: t.tags
  exns : ∀ (a : Nat) (e : ExnInst), s.exns[a]? = some e → ∃ e', t.exns[a]? = some e'

namespace Widen

variable {s t : Store H}

theorem refl (s : Store H) : Widen s s := ⟨rfl, List.prefix_refl _, fun _ e h => ⟨e, h⟩⟩

theorem globals (h : Widen s t) : t.globals = s.globals := by rw [h.eq]
theorem mems (h : Widen s t) : t.mems = s.mems := by rw [h.eq]
theorem tables (h : Widen s t) : t.tables = s.tables := by rw [h.eq]
theorem funcs (h : Widen s t) : t.funcs = s.funcs := by rw [h.eq]
theorem datas (h : Widen s t) : t.datas = s.datas := by rw [h.eq]
theorem elems (h : Widen s t) : t.elems = s.elems := by rw [h.eq]
theorem structs (h : Widen s t) : t.structs = s.structs := by rw [h.eq]
theorem arrays (h : Widen s t) : t.arrays = s.arrays := by rw [h.eq]

theorem tag? (h : Widen s t) {a : Nat} {ti : TagInst} (ht : s.tags[a]? = some ti) :
    t.tags[a]? = some ti := by
  obtain ⟨u, hu⟩ := h.tags
  rw [← hu, List.getElem?_append_left (List.getElem?_eq_some_iff.1 ht).1]
  exact ht

theorem refOk (h : Widen s t) {r : Ref} {rt : CRefType} (hr : RefOk s r rt) : RefOk t r rt := by
  induction hr with
  | null => exact .null
  | i31 b => exact .i31 b
  | struct hh => exact .struct (by rw [h.structs]; exact hh)
  | array hh => exact .array (by rw [h.arrays]; exact hh)
  | func hh => exact .func (by rw [h.funcs]; exact hh)
  | exn hh =>
    obtain ⟨e', h'⟩ := h.exns _ _ hh
    exact .exn h'
  | host a => exact .host a
  | extern _ hn ih => exact .extern ih hn
  | sub _ hok hs ih => exact .sub ih hok hs

theorem valOk (h : Widen s t) {v : Val} {ty : CValType} (hv : ValOk s v ty) : ValOk t v ty := by
  cases hv with
  | num v => exact .num v
  | vec b => exact .vec b
  | ref hr => exact .ref (h.refOk hr)

theorem fieldValOk (h : Widen s t) {v : FieldVal} {ty : CStorageType} (hv : FieldValOk s v ty) :
    FieldValOk t v ty := by
  cases hv with
  | val hv => exact .val (h.valOk hv)
  | pack p b => exact .pack p b

theorem localValOk (h : Widen s t) {v : Option Val} {lt : LocalType} (hv : LocalValOk s v lt) :
    LocalValOk t v lt := by
  cases hv with
  | set hv => exact .set (h.valOk hv)
  | unset hv => exact .unset hv

theorem externAddrOk (h : Widen s t) {xa : ExternAddr} {xt : CExternType}
    (hx : ExternAddrOk s xa xt) : ExternAddrOk t xa xt := by
  induction hx with
  | tag hh => exact .tag (h.tag? hh)
  | global hh => exact .global (by rw [h.globals]; exact hh)
  | mem hh => exact .mem (by rw [h.mems]; exact hh)
  | table hh => exact .table (by rw [h.tables]; exact hh)
  | func hh => exact .func (by rw [h.funcs]; exact hh)
  | sub _ hok hs ih => exact .sub ih hok hs

theorem elemInstOk (h : Widen s t) {ei : ElemInst} (he : ElemInstOk s ei) : ElemInstOk t ei :=
  ⟨he.1, fun r hr => h.refOk (he.2 r hr)⟩

theorem moduleInstOk (h : Widen s t) {mi : ModuleInst} {C : Context} (hm : ModuleInstOk s mi C) :
    ModuleInstOk t mi C := by
  cases hm with
  | mk htypes htags hglobals hfuncs hmems htables hdatas helems hexports hdisjoint hexportAddrs hk =>
    refine .mk htypes (htags.imp fun _ _ hh => h.externAddrOk hh)
      (hglobals.imp fun _ _ hh => h.externAddrOk hh) (hfuncs.imp fun _ _ hh => h.externAddrOk hh)
      (hmems.imp fun _ _ hh => h.externAddrOk hh) (htables.imp fun _ _ hh => h.externAddrOk hh)
      (fun a ha => by rw [h.datas]; exact hdatas a ha)
      (helems.imp fun _ _ hh => ?_) (fun xi hxi => ?_) hdisjoint hexportAddrs hk
    · obtain ⟨ei, hei, hok, rfl⟩ := hh
      exact ⟨ei, by rw [h.elems]; exact hei, h.elemInstOk hok, rfl⟩
    · obtain ⟨xt, hxt⟩ := hexports xi hxi
      exact ⟨xt, h.externAddrOk hxt⟩

theorem frameOk (h : Widen s t) {f : Frame} {C : Context} (hf : FrameOk s f C) : FrameOk t f C := by
  obtain ⟨C₀, lts, hm, hl, rfl⟩ := hf
  exact ⟨C₀, lts, h.moduleInstOk hm, hl.imp fun _ _ hh => h.localValOk hh, rfl⟩

mutual

theorem adminOk (h : Widen s t) :
    ∀ {C : Context} {a : Admin} {it : InstrType}, AdminOk s C a it → AdminOk t C a it
  | _, _, _, .plain hh => .plain hh
  | _, _, _, .callRefType hok hex => .callRefType hok hex
  | _, _, _, .returnCallRefType hok hex hr hsub hit => .returnCallRefType hok hex hr hsub hit
  | _, _, _, .ref hh => .ref (h.refOk hh)
  | _, _, _, .label hn hc hb => .label hn (adminsOk h hc) (adminsOk h hb)
  | _, _, _, .frame hf hn hb hok => .frame (h.frameOk hf) hn (adminsOk h hb) hok
  | _, _, _, .handler hc hb => .handler hc (adminsOk h hb)
  | _, _, _, .trap hok => .trap hok
  | _, _, _, .throwRefInits hok => .throwRefInits hok

theorem adminsOk (h : Widen s t) :
    ∀ {C : Context} {as : List Admin} {it : InstrType}, AdminsOk s C as it → AdminsOk t C as it
  | _, _, _, .nil => .nil
  | _, _, _, .single hh => .single (adminOk h hh)
  | _, _, _, .seq h₁ hx h₂ => .seq (adminsOk h h₁) hx (adminsOk h h₂)
  | _, _, _, .cons ha hx hs => .cons (adminOk h ha) hx (adminsOk h hs)
  | _, _, _, .sub hh hsub hok => .sub (adminsOk h hh) hsub hok
  | _, _, _, .frame hh hok => .frame (adminsOk h hh) hok

end

theorem globalInstOk (h : Widen s t) {gi : GlobalInst} (hg : GlobalInstOk s gi) :
    GlobalInstOk t gi := ⟨hg.1, h.valOk hg.2⟩

theorem tableInstOk (h : Widen s t) {ti : TableInst} (hg : TableInstOk s ti) :
    TableInstOk t ti := ⟨hg.1, hg.2.1, fun r hr => h.refOk (hg.2.2 r hr)⟩

theorem structInstOk (h : Widen s t) {si : StructInst} (hg : StructInstOk s si) :
    StructInstOk t si := by
  obtain ⟨fs, he, hf⟩ := hg
  exact ⟨fs, he, hf.imp fun _ _ hh => h.fieldValOk hh⟩

theorem arrayInstOk (h : Widen s t) {ai : ArrayInst} (hg : ArrayInstOk s ai) :
    ArrayInstOk t ai := by
  obtain ⟨ft, he, hf⟩ := hg
  exact ⟨ft, he, fun fv hfv => h.fieldValOk (hf fv hfv)⟩

theorem funcInstOk (h : Widen s t) {fi : FuncInst H} (hg : FuncInstOk s fi) : FuncInstOk t fi := by
  cases hg with
  | wasm hdt hm hcode hf hs => exact .wasm hdt (h.moduleInstOk hm) hcode hf hs
  | host hdt he hcode => exact .host hdt he hcode

end Widen

end Silmaril.Wasm.Cfg.Proofs.DanglingTyped
