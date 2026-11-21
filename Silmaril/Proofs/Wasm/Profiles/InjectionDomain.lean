module

public import Silmaril.Wasm.Versions.Thms

public section

namespace Silmaril.Wasm.Proofs.Profiles.InjectionDomain

open V2

mutual
private theorem instr (op : V2.Instr) (valid : op.immediatesValid = true) :
    ∃ core, op.toCore = some core := by
  cases op <;> try exact ⟨_, rfl⟩
  case block ty body =>
    obtain ⟨core, eq⟩ := expr body (by simpa [V2.Instr.immediatesValid] using valid)
    exact ⟨.block ty.toCore core, by rw [V2.Instr.toCore, eq]; rfl⟩
  case loop ty body =>
    obtain ⟨core, eq⟩ := expr body (by simpa [V2.Instr.immediatesValid] using valid)
    exact ⟨.loop ty.toCore core, by rw [V2.Instr.toCore, eq]; rfl⟩
  case if_ ty left right =>
    have both : left.all V2.Instr.immediatesValid = true ∧ right.all V2.Instr.immediatesValid = true := by
      simpa [V2.Instr.immediatesValid] using valid
    obtain ⟨coreLeft, eqLeft⟩ := expr left both.1
    obtain ⟨coreRight, eqRight⟩ := expr right both.2
    exact ⟨.if_ ty.toCore coreLeft coreRight, by rw [V2.Instr.toCore, eqLeft, eqRight]; rfl⟩
  case cvtOp target source convert =>
    simp only [V2.Instr.immediatesValid, Bool.and_eq_true] at valid
    obtain ⟨core, eq⟩ := Option.isSome_iff_exists.mp valid.2
    exact ⟨.convert core, by rw [V2.Instr.toCore, V2.CvtOp.toCore, eq]; rfl⟩
termination_by sizeOf op

private theorem expr (body : V2.Expr) (valid : body.all V2.Instr.immediatesValid = true) :
    ∃ core, V2.Expr.toCore body = some core := by
  cases body with
  | nil => exact ⟨[], rfl⟩
  | cons head tail =>
    have both := Bool.and_eq_true_iff.mp valid
    obtain ⟨coreHead, eqHead⟩ := instr head both.1
    obtain ⟨coreTail, eqTail⟩ := expr tail both.2
    exact ⟨coreHead :: coreTail, by rw [V2.Expr.toCore, eqHead, eqTail]; rfl⟩
termination_by sizeOf body
end

private theorem mapM_defined {A B : Type} {translate : A → Option B} :
    ∀ (items : List A), (∀ item ∈ items, ∃ image, translate item = some image) →
      ∃ images, items.mapM translate = some images
  | [], _ => ⟨[], rfl⟩
  | head :: tail, defined => by
    obtain ⟨image, headEq⟩ := defined head (by simp)
    obtain ⟨images, tailEq⟩ := mapM_defined tail fun item mem => defined item (List.mem_cons_of_mem _ mem)
    exact ⟨image :: images, by simp [List.mapM_cons, headEq, tailEq]⟩

private theorem mapM_rel {A B T : Type} {rel : A → T → Prop} {translate : A → Option B}
    {items : List A} {types : List T} (checked : List.Forall₂ rel items types)
    (defined : ∀ {item ty}, rel item ty → ∃ image, translate item = some image) :
    ∃ images, items.mapM translate = some images := by
  induction checked with
  | nil => exact ⟨[], rfl⟩
  | cons head tail ih =>
    obtain ⟨image, headEq⟩ := defined head
    obtain ⟨images, tailEq⟩ := ih
    exact ⟨image :: images, by simp [List.mapM_cons, headEq, tailEq]⟩

theorem funcDefined {ctx : V2.Validation.Context} {source : V2.Func} {sig : V2.FuncType}
    (checked : V2.Validation.FuncOk ctx source sig) : ∃ core, source.toCore = some core := by
  cases checked with
  | mk _ body =>
    obtain ⟨image, eq⟩ := expr source.body body.immediatesValid
    exact ⟨_, by rw [V2.Func.toCore, eq]; rfl⟩

private theorem elemModeDefined {ctx : V2.Validation.Context} {mode : V2.ElemMode} {ty : V2.RefType}
    (checked : V2.Validation.ElemModeOk ctx mode ty) : ∃ core, mode.toCore = some core := by
  cases checked with
  | active _ _ offset =>
    obtain ⟨image, eq⟩ := expr _ offset.typed.immediatesValid
    exact ⟨_, by rw [V2.ElemMode.toCore, eq]; rfl⟩
  | passive => exact ⟨_, rfl⟩
  | declare => exact ⟨_, rfl⟩

private theorem dataModeDefined {ctx : V2.Validation.Context} {mode : V2.DataMode}
    (checked : V2.Validation.DataModeOk ctx mode) : ∃ core, mode.toCore = some core := by
  cases checked with
  | active _ _ offset =>
    obtain ⟨image, eq⟩ := expr _ offset.typed.immediatesValid
    exact ⟨_, by rw [V2.DataMode.toCore, eq]; rfl⟩
  | passive => exact ⟨_, rfl⟩

theorem moduleDefined {source : V2.Module} {imports exports : List V2.ExternType}
    (checked : V2.Validation.ModuleOk source imports exports) : ∃ core, source.toCore = some core := by
  cases checked with
  | mk _ _ globals _ _ elems datas funcs _ _ _ _ _ _ =>
    obtain ⟨_, eqGlobals⟩ := mapM_rel (translate := V2.Global.toCore) globals fun hg => by
      obtain ⟨_, eq⟩ := expr _ hg.2.2.typed.immediatesValid
      exact ⟨_, by rw [V2.Global.toCore, eq]; rfl⟩
    obtain ⟨_, eqFuncs⟩ := mapM_rel (translate := V2.Func.toCore) funcs fun hf => funcDefined hf
    obtain ⟨_, eqElems⟩ := mapM_rel (translate := V2.Elem.toCore) elems fun {item _} he => by
      obtain ⟨_, eqInit⟩ := mapM_defined (translate := V2.Expr.toCore) item.init fun body mem =>
        expr body (he.2.1 body mem).typed.immediatesValid
      obtain ⟨_, eqMode⟩ := elemModeDefined he.2.2
      exact ⟨_, by rw [V2.Elem.toCore, eqInit, eqMode]; rfl⟩
    obtain ⟨_, eqDatas⟩ := mapM_defined (translate := V2.Data.toCore) source.data fun data mem => by
      obtain ⟨_, eq⟩ := dataModeDefined (datas data mem)
      exact ⟨_, by rw [V2.Data.toCore, eq]; rfl⟩
    exact ⟨_, by rw [V2.Module.toCore, eqGlobals, eqFuncs, eqElems, eqDatas]; rfl⟩

end Silmaril.Wasm.Proofs.Profiles.InjectionDomain
