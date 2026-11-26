module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Defs
public import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs.Lime1

open Wasm.Lime1.Execution
open Execution.Runtime (Frame Value AdminInstr FuncAddr)

inductive Focus : Admin → Prop where
  | invoke (a : FuncAddr) : Focus (.invoke a)
  | frame (n : Nat) (f : Frame) (body : List Admin) : Focus (.frame n f body)
  | label (n : Nat) (cont : Wasm.Lime1.Expr) (body : List Admin) : Focus (.label n cont body)
  | nop : Focus (.source .nop)
  | trap : Focus .trap

theorem Focus.nonvalue {a : Admin} (h : Focus a) : asValue? a = none := by
  cases h <;> rfl

def first (code : List Admin) := code.find? (fun a => (asValue? a).isNone)

@[simp] theorem first_value (v : Value) (tail : List Admin) :
    first (value v :: tail) = first tail := by simp [first, asValue?_value]

@[simp] theorem first_prefix (vs : List Value) (tail : List Admin) :
    first (values vs ++ tail) = first tail := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change first (value v :: (values vs ++ tail)) = first tail
    rw [first_value, ih]

theorem first_head {a : Admin} (tail : List Admin) (ha : asValue? a = none) :
    first (a :: tail) = some a := by simp [first, ha]

theorem peel {saved stack : List Value} {op : Admin} {mid tail rest : List Admin}
    (active : ∃ a ∈ mid, asValue? a = none)
    (eq : values saved ++ mid ++ tail = values stack ++ op :: rest) (ho : asValue? op = none) :
    ∃ args pre, stack = saved ++ args ∧ mid = values args ++ op :: pre ∧ rest = pre ++ tail := by
  induction saved generalizing stack with
  | nil =>
    change mid ++ tail = values stack ++ op :: rest at eq
    rcases List.append_eq_append_iff.mp eq with ⟨pre, front, suffix⟩ | ⟨pre, front, suffix⟩
    · obtain ⟨a, member, none⟩ := active
      have inValues : a ∈ values stack := front ▸ List.mem_append_left pre member
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp inValues
      simp at none
    · rcases pre with _ | ⟨hd, pre⟩
      · obtain ⟨a, member, none⟩ := active
        rw [List.append_nil] at front
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp (front ▸ member)
        simp at none
      · obtain ⟨rfl, rfl⟩ := List.cons.inj suffix
        exact ⟨stack, pre, rfl, front, rfl⟩
  | cons v saved ih =>
    cases stack with
    | nil =>
      have head := List.cons.inj eq |>.1
      have decoded := congrArg asValue? head
      rw [asValue?_value, ho] at decoded
      contradiction
    | cons w stack =>
      have ⟨head, tailEq⟩ := List.cons.inj eq
      have same : v = w := by simpa using congrArg asValue? head
      subst w
      obtain ⟨args, pre, rfl, rfl, rfl⟩ := ih tailEq
      exact ⟨args, pre, rfl, rfl, rfl⟩

@[simp] theorem first_values (vs : List Value) : first (values vs) = none := by
  change first (values vs) = first []
  rw [← first_prefix vs [], List.append_nil]

def wrapper : Admin → Prop
  | .label _ _ _ | .frame _ _ _ => True
  | _ => False

inductive WrapperStep {H : Type} (s : Store H) (f : Frame) : Admin → Config H → Prop where
  | pure {a out} (step : PureStep f.module.types [a] out) :
      WrapperStep s f a ⟨s, f, out⟩
  | label {n cont body} {target : Config H} (step : Step CallFrame.limeNoHost ⟨s, f, body⟩ target) :
      WrapperStep s f (.label n cont body) ⟨target.store, target.frame, [.label n cont target.code]⟩
  | frame {n inner body} {target : Config H} (step : Step CallFrame.limeNoHost ⟨s, inner, body⟩ target) :
      WrapperStep s f (.frame n inner body) ⟨target.store, f, [.frame n target.frame target.code]⟩

theorem wrapper_step {H : Type} {a b : Config H}
    (h : Step CallFrame.limeNoHost a b) {op : Admin} (shape : a.code = [op]) (hw : wrapper op) :
    WrapperStep a.store a.frame op b := by
  induction h with
  | pure _ _ h => exact .pure (shape ▸ h)
  | label h n cont _ =>
    cases (List.cons.inj shape).1
    exact .label h
  | frame h n outer _ =>
    cases (List.cons.inj shape).1
    exact .frame h
  | @context s s' f f' before after h saved tail ih =>
    change values saved ++ before ++ tail = [op] at shape
    have lengths := congrArg List.length shape
    simp only [List.length_append, values_length, List.length_cons, List.length_nil] at lengths
    obtain ⟨op, mem, _⟩ := h.nonvalue
    have pos : 0 < before.length := List.length_pos_iff.mpr
      (List.ne_nil_of_mem (show op ∈ before from mem))
    have hs : saved = [] := List.eq_nil_of_length_eq_zero (by omega)
    have ht : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst saved tail
    simpa [values] using ih (by simpa [values] using shape)
  | invokeHost | invokeHostDiverges => contradiction
  | invokeWasm =>
    have same := congrArg List.getLast? shape
    simp [List.getLast?_append] at same
    subst op
    contradiction
  | _ =>
    have same := congrArg List.getLast? shape
    simp at same
    subst op
    contradiction

theorem frame_label_stays {types : List Wasm.Lime1.FuncType} {n : Nat} {f : Frame}
    {k : Nat} {cont : Wasm.Lime1.Expr} {body out : List Admin} (h : PureStep types [.frame n f [.label k cont body]] out) : False := by
  generalize eq : ([.frame n f [.label k cont body]] : List Admin) = before at h
  cases h with
  | frameDone | frameReturn | frameTrap =>
    have code := (AdminInstr.frame.inj (List.cons.inj eq).1).2.2
    have seen := congrArg first code
    try simp only [List.append_assoc, List.singleton_append, first_prefix, first_values] at seen
    simp [first, asValue?] at seen
  | trapValues | trapTail =>
    have len := congrArg List.length eq
    simp [values] at len
  | _ =>
    have last := congrArg List.getLast? eq
    simp [values, List.getLast?_append] at last

inductive Front {H : Type} (s : Store H) (f : Frame) :
    List Value → Admin → List Admin → Config H → Prop where
  | normal {vs op rest} {mid : Config H} (notNop : op ≠ .source .nop) (notTrap : op ≠ .trap)
      (h : Step CallFrame.limeNoHost ⟨s, f, values vs ++ [op]⟩ mid) :
      Front s f vs op rest ⟨mid.store, mid.frame, mid.code ++ rest⟩
  | nop (vs : List Value) (rest : List Admin) :
      Front s f vs (.source .nop) rest ⟨s, f, values vs ++ rest⟩
  | bubble (kept removed : List Value) (pre rest : List Admin) (active : removed ≠ [] ∨ pre ≠ []) :
      Front s f (kept ++ removed) .trap (pre ++ rest) ⟨s, f, values kept ++ .trap :: rest⟩

private theorem pure_front {H : Type} {s : Store H} {f : Frame} {vs : List Value}
    {op : Admin} {rest out : List Admin}
    (focus : Focus op) (h : PureStep f.module.types (values vs ++ op :: rest) out) :
    Front s f vs op rest ⟨s, f, out⟩ := by
  have compact {e : Admin} {output : List Admin} (nop : e ≠ .source .nop) (trap : e ≠ .trap)
      (h : PureStep f.module.types [e] output) : Front s f [] e [] ⟨s, f, output⟩ := by
    simpa only [List.append_nil] using
      (Front.normal (vs := []) (op := e) (rest := []) nop trap (Step.pure s f h))
  generalize eq : values vs ++ op :: rest = before at h
  have seen := congrArg first eq
  rw [first_prefix, first_head rest focus.nonvalue] at seen
  cases h with
  | trapValues v xs cut =>
    change values vs ++ op :: rest = values (v :: xs) ++ [.trap] ++ cut at eq
    obtain ⟨args, prior, valuesEq, one, cutEq⟩ :=
      peel (saved := v :: xs) (mid := [.trap]) (tail := cut) ⟨.trap, List.Mem.head _, rfl⟩ eq.symm focus.nonvalue
    have len := congrArg List.length one
    simp at len
    obtain ⟨rfl, rfl⟩ : args = [] ∧ prior = [] := ⟨
      List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
    have opEq : AdminInstr.trap = op := (List.cons.inj one).1
    subst op
    rw [List.append_nil] at valuesEq
    subst vs
    subst rest
    simpa only [List.append_nil, List.nil_append, values, List.map_nil] using
      (Front.bubble (s := s) (f := f) [] (v :: xs) cut [] (.inl (List.cons_ne_nil _ _)))
  | trapTail hd cut =>
    obtain ⟨args, prior, valuesEq, one, cutEq⟩ :=
      peel (saved := []) (mid := [.trap]) (tail := hd :: cut) ⟨.trap, List.Mem.head _, rfl⟩ eq.symm focus.nonvalue
    have len := congrArg List.length one
    simp at len
    obtain ⟨rfl, rfl⟩ : args = [] ∧ prior = [] := ⟨
      List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
    have opEq : AdminInstr.trap = op := (List.cons.inj one).1
    subst op
    subst vs
    subst rest
    simpa only [List.append_nil, List.nil_append, values, List.map_nil] using
      (Front.bubble (s := s) (f := f) [] [] (hd :: cut) [] (.inr (List.cons_ne_nil _ _)))
  | nop =>
    have len := congrArg List.length eq
    simp at len
    have hv : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst vs rest
    cases (List.cons.inj eq).1
    exact .nop [] []
  | _ =>
    first
    | solve
      | (try simp only [List.append_assoc, List.singleton_append, first_prefix, first_value] at seen)
        simp [first, asValue?] at seen
        subst op
        cases focus
    | have len := congrArg List.length eq
      simp at len
      have hv : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
      have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst vs rest
      cases (List.cons.inj eq).1
      refine compact ?_ ?_ ?_
      rotate_left 2
      · first
        | exact .labelDone _ _ _
        | exact .labelBranch _ _ _ _ _ (by assumption)
        | exact .labelBranchOuter _ _ _ _ _ (by assumption)
        | exact .labelReturn _ _ _ _
        | exact .labelTrap _ _
        | exact .frameDone _ _ _ (by assumption)
        | exact .frameReturn _ _ _ _ _ (by assumption)
        | exact .frameTrap _ _
      all_goals intro bad; cases bad

theorem front {H : Type} {src dst : Config H} (h : Step CallFrame.limeNoHost src dst)
    {vs : List Value} {op : Admin} {rest : List Admin} (focus : Focus op)
    (eq : src.code = values vs ++ op :: rest) : Front src.store src.frame vs op rest dst := by
  induction h generalizing vs rest with
  | pure s f h => exact pure_front focus (eq ▸ h)
  | @context s s' f f' before after h saved tail ih =>
    obtain ⟨args, pre, rfl, he, rfl⟩ := peel h.nonvalue eq focus.nonvalue
    cases ih he with
    | @normal _ _ _ mid hNop hTrap step =>
      have lifted := Step.context (tail := []) step saved
      refine (show Front s f (saved ++ args) op (pre ++ tail)
        ⟨mid.store, mid.frame, values saved ++ (mid.code ++ pre) ++ tail⟩ from ?_)
      have isolated : Step CallFrame.limeNoHost ⟨s, f, values (saved ++ args) ++ [op]⟩
          ⟨mid.store, mid.frame, values saved ++ mid.code⟩ := by
        simpa only [List.append_nil, values_append, List.append_assoc] using lifted
      simpa only [List.append_assoc] using (Front.normal (rest := pre ++ tail) hNop hTrap isolated)
    | nop =>
      simpa only [values_append, List.append_assoc] using Front.nop (s := s) (f := f) (saved ++ args) (pre ++ tail)
    | bubble kept removed discard tail' nonempty =>
      simpa only [values_append, List.append_assoc, List.cons_append] using
        (Front.bubble (s := s) (f := f) (saved ++ kept) removed discard (tail' ++ tail) nonempty)
  | @label s s' f f' before after step n cont _ =>
    have same := congrArg List.length eq
    simp at same
    have hv : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst vs rest
    obtain rfl : AdminInstr.label n cont before = op := (List.cons.inj eq).1
    exact Front.normal (vs := []) (rest := []) (by intro bad; cases bad)
      (by intro bad; cases bad) (.label step n cont)
  | @frame s s' inner inner' before after step n outer _ =>
    have same := congrArg List.length eq
    simp at same
    have hv : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst vs rest
    obtain rfl : AdminInstr.frame n inner before = op := (List.cons.inj eq).1
    exact Front.normal (vs := []) (rest := []) (by intro bad; cases bad)
      (by intro bad; cases bad) (.frame step n outer)
  | invokeWasm s f a ft module fn args found arity =>
    obtain ⟨more, pre, stack, one, rfl⟩ :=
      peel (saved := args) (mid := [.invoke a]) (tail := []) ⟨.invoke a, List.Mem.head _, rfl⟩
        (by simpa using eq) focus.nonvalue
    have len := congrArg List.length one
    simp at len
    have hm : more = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hp : pre = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst more pre
    obtain rfl : AdminInstr.invoke a = op := (List.cons.inj one).1
    rw [List.append_nil] at stack
    subst vs
    exact Front.normal (vs := args) (rest := []) (by intro bad; cases bad)
      (by intro bad; cases bad) (.invokeWasm s f a ft module fn args found arity)
  | invokeHost => contradiction
  | invokeHostDiverges => contradiction
  | _ =>
    have seen := congrArg first eq
    rw [first_prefix, first_head rest focus.nonvalue] at seen
    simp only [first_value] at seen
    simp [first, asValue?] at seen
    subst op
    cases focus

private inductive MemoryHead : Admin → Nat → Prop where
  | load (arg : V1.MemArg) : MemoryHead (.source (.intLoad .i32 none arg)) 1
  | store (arg : V1.MemArg) : MemoryHead (.source (.intStore .i32 none arg)) 2

private theorem MemoryHead.nonvalue {op : Admin} {arity : Nat} (h : MemoryHead op arity) :
    asValue? op = none := by
  cases h <;> rfl

private theorem memory_leaf {H : Type} {s : Store H} {f : Frame}
    {stack used : List Value} {op : Admin} {tail : List Admin} {arity : Nat} {dst : Config H}
    (shape : MemoryHead op arity) (len : used.length = arity)
    (code : values used ++ [op] = values stack ++ op :: tail)
    (step : Internal ⟨s, f, values used ++ [op]⟩ dst) :
    ∃ kept operands mid, stack = kept ++ operands ∧ operands.length = arity ∧
      Internal ⟨s, f, values operands ++ [op]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values kept ++ mid.code ++ tail⟩ := by
  obtain ⟨extra, pre, split, one, suffix⟩ :=
    peel (saved := used) (mid := [op]) (tail := []) ⟨op, by simp, shape.nonvalue⟩
      (by simpa using code) shape.nonvalue
  have length := congrArg List.length one
  simp at length
  obtain ⟨rfl, rfl⟩ : extra = [] ∧ pre = [] := ⟨
    List.eq_nil_of_length_eq_zero (by omega), List.eq_nil_of_length_eq_zero (by omega)⟩
  simp at split suffix
  subst stack tail
  exact ⟨[], used, dst, rfl, len, step, by cases dst; simp [values]⟩

set_option linter.unusedSimpArgs false in
private theorem memory_cut {H : Type} {src dst : Config H} {op : Admin} {arity : Nat}
    (shape : MemoryHead op arity) (move : Internal src dst)
    {stack : List Value} {tail : List Admin} (code : src.code = values stack ++ op :: tail) :
    ∃ kept operands mid, stack = kept ++ operands ∧ operands.length = arity ∧
      Internal ⟨src.store, src.frame, values operands ++ [op]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values kept ++ mid.code ++ tail⟩ := by
  have seen : first src.code = some op := by rw [code, first_prefix, first_head _ shape.nonvalue]
  induction move generalizing stack tail with
  | @context s s' f f' before after move saved rest ih =>
    obtain ⟨args, pre, rfl, inside, rfl⟩ := peel move.nonvalue code shape.nonvalue
    change before = values args ++ op :: pre at inside
    have inHead : first before = some op := by rw [inside, first_prefix, first_head _ shape.nonvalue]
    obtain ⟨kept, used, mid, rfl, len, leaf, eq⟩ := ih inside inHead
    refine ⟨saved ++ kept, used, mid, (List.append_assoc ..).symm, len, leaf, ?_⟩
    change (⟨s', f', after⟩ : Config H) = _ at eq
    simpa only [values_append, List.append_assoc] using congrArg
      (fun cfg : Config H => (⟨cfg.store, cfg.frame, values saved ++ cfg.code ++ rest⟩ : Config H)) eq
  | intLoad s f t packed arg address a m v found read =>
    cases shape <;> simp only [first_value] at seen <;> simp [first, asValue?] at seen
    obtain ⟨rfl, rfl, rfl⟩ := seen
    exact memory_leaf (.load _) (used := [Value.int .i32 address]) rfl code
      (.intLoad s f _ _ _ _ a m v found read)
  | intLoadTrap s f t packed arg address a m found read =>
    cases shape <;> simp only [first_value] at seen <;> simp [first, asValue?] at seen
    obtain ⟨rfl, rfl, rfl⟩ := seen
    exact memory_leaf (.load _) (used := [Value.int .i32 address]) rfl code
      (.intLoadTrap s f _ _ _ _ a m found read)
  | intStore s f t packed arg address word a m out found write =>
    cases shape <;> simp only [first_value] at seen <;> simp [first, asValue?] at seen
    obtain ⟨rfl, rfl, rfl⟩ := seen
    exact memory_leaf (.store _) (used := [Value.int .i32 address, Value.int .i32 word]) rfl code
      (.intStore s f _ _ _ _ _ a m out found write)
  | intStoreTrap s f t packed arg address word a m found write =>
    cases shape <;> simp only [first_value] at seen <;> simp [first, asValue?] at seen
    obtain ⟨rfl, rfl, rfl⟩ := seen
    exact memory_leaf (.store _) (used := [Value.int .i32 address, Value.int .i32 word]) rfl code
      (.intStoreTrap s f _ _ _ _ _ a m found write)
  | invokeHost | invokeHostDiverges => contradiction
  | pure s f move =>
    cases move <;> cases shape <;>
      simp only [List.append_assoc, List.singleton_append, first_prefix, first_values, first_value] at seen <;>
      simp [first, asValue?] at seen
  | _ =>
    cases shape <;>
      simp only [List.append_assoc, List.singleton_append, first_prefix, first_values, first_value] at seen <;>
      simp [first, asValue?] at seen

theorem intLoad_strip {H : Type} {s : Store H} {f : Frame} {arg : V1.MemArg}
    {ptr : BitVec 32} {saved : List Value} {tail : List Admin} {dst : Config H}
    (move : Internal ⟨s, f, values (saved ++ [Value.int .i32 ptr]) ++ .source (.intLoad .i32 none arg) :: tail⟩ dst) :
    ∃ mid, Internal ⟨s, f, [value (Value.int .i32 ptr), .source (.intLoad .i32 none arg)]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values saved ++ mid.code ++ tail⟩ := by
  obtain ⟨_, _, mid, split, len, head, eq⟩ := memory_cut (.load arg) move rfl
  obtain ⟨rfl, rfl⟩ := List.append_inj' split len.symm
  exact ⟨mid, head, eq⟩

theorem intStore_strip {H : Type} {s : Store H} {f : Frame} {arg : V1.MemArg}
    {ptr word : BitVec 32} {saved : List Value} {tail : List Admin} {dst : Config H}
    (move : Internal ⟨s, f, values (saved ++ [Value.int .i32 ptr, Value.int .i32 word]) ++
      .source (.intStore .i32 none arg) :: tail⟩ dst) :
    ∃ mid, Internal ⟨s, f, [value (Value.int .i32 ptr), value (Value.int .i32 word),
      .source (.intStore .i32 none arg)]⟩ mid ∧
      dst = ⟨mid.store, mid.frame, values saved ++ mid.code ++ tail⟩ := by
  obtain ⟨_, _, mid, split, len, head, eq⟩ := memory_cut (.store arg) move rfl
  obtain ⟨rfl, rfl⟩ := List.append_inj' split len.symm
  exact ⟨mid, head, eq⟩

end Silmaril.Wasm.Institution.Operational.CallContinuation.Proofs.Lime1
