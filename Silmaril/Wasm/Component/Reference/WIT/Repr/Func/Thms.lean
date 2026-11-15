module

public import Silmaril.Wasm.Component.Reference.WIT.Repr.Thms
public import Silmaril.Semantics.Accept.Func.Thms

/-! # WIT representations as relations

A WIT representation `r : Repr E α t` (an equivalence `α ≃ t.Interp E`) is, as a relation
(`Silmaril.Accept.ofTotal r`, #253), **one-to-one** in the sense of
`Silmaril.Semantics.Accept.Func` (#270): total, single-valued, injective and surjective
(`Repr.oneToOne`). Its inverse relation is too (`Repr.oneToOne_symm`). This is the
relational form of "the Lean type and the WIT type are isomorphic": the representation
relates every Lean value to exactly one WIT value and back.

The WIT decoders of components (`Silmaril.Wasi.Accept.decode`, `bytes?`) are partial maps
`Val → Option _`, so as `Silmaril.Accept.ofPartial` relations they are single-valued
(`Silmaril.Accept.singleValued_ofPartial`), but in general neither total nor injective.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.WIT.Repr

universe u v

variable {Ref : Type u} {Resource : Type v} {E : Env Ref Resource} {α : Type}
  {t : ValType Ref Resource}

/-- **A representation is a one-to-one relation.** -/
theorem oneToOne (r : Repr E α t) : Silmaril.Accept.OneToOne (Silmaril.Accept.ofTotal r) :=
  ⟨Silmaril.Accept.functional_ofTotal r,
    fun _ _ _ h h' => r.injective (h.trans h'.symm),
    fun b => ⟨r.symm b, r.apply_symm_apply b⟩⟩

/-- Its inverse too. -/
theorem oneToOne_symm (r : Repr E α t) :
    Silmaril.Accept.OneToOne (Silmaril.Accept.ofTotal r.symm) :=
  ⟨Silmaril.Accept.functional_ofTotal r.symm,
    fun _ _ _ h h' => r.symm.injective (h.trans h'.symm),
    fun b => ⟨r b, r.symm_apply_apply b⟩⟩

end Silmaril.Wasm.Component.WIT.Repr
