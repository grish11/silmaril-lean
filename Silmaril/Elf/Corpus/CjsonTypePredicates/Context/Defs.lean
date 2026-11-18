module
public import Silmaril.Elf.Corpus.CjsonTypePredicates.Source.Elaboration.Thms
public import Silmaril.Elf.Corpus.CjsonTypePredicates.Thms
public import Silmaril.Elf.Corpus.CjsonTypePredicates.Source.Projection.Thms
public import Silmaril.Project.Shapes.Contextual.Defs
public import Silmaril.X86.Open.Thms

/-! Concrete memory contexts for the ten unchanged cJSON predicates in the
actual preprocessed declaration closure. Full-TU acceptance and correspondence
of host preprocessing to canonical system headers are not established. These
are source-to-ELF problems, not semantic proofs. No expected predicate result
or refinement certificate is an entry assumption. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.CjsonTypePredicates.Context
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes Silmaril.Project.Shapes.Contextual

structure Input where
  isNull : Bool
  typeBits : BitVec 32

def placement (p : Predicate) : Silmaril.Project.Shapes.Placement := ⟨p.address, p.code, 0⟩

/-- Actual parameter and struct tag; typed stores establish pointer provenance
and initialized field bytes. A failure is exposed by the entry relation, never
replaced with a default body/state. Joint entry existence in `Obligation` must
establish success for every input. -/
def prepare (p : Predicate) (i : Input) : Except String State := do
  let F := Source.Elaboration.function p
  let [(symbol, pointerType)] := F.params | throw "expected one actual pointer parameter"
  let [(tag, _)] := Source.Elaboration.core.tagDefs | throw "expected one actual struct tag"
  let aggregate : Ctype := .mk [] (.struct tag)
  let layout ← (Mem.Concrete.typeLayout 64 F.file.tagDefs aggregate).mapError (fun _ => "struct layout failed")
  unless layout.size == 64 && layout.align == 8 do throw "unexpected cJSON layout"
  let some (_, fieldType, offset) := layout.members.find? (fun (name, _, _) => name.key == "type")
    | throw "missing actual type member"
  unless offset == 24 do throw "unexpected type member offset"
  let .mk _ (.basic (.integer (.signed .int))) := fieldType
    | throw "actual type member is not signed int"
  let memory : Mem.Concrete.State :=
    {nextId := 2, lastAddress := 4096, allocations := Map.ofList
      [(0, ⟨4096, 8, false, false, some pointerType, none, .UB064_modifying_const⟩),
       (1, ⟨8192, 64, false, false, some aggregate, none, .UB064_modifying_const⟩)]}
  let (_, memory) ← (Mem.Concrete.storeTyped F.file.tagDefs memory pointerType (.allocated 0 4096)
    (.pointer aggregate (if i.isNull then .null aggregate else .allocated 1 8192))).mapError
      (fun _ => "actual pointer parameter store failed")
  let (_, memory) ← (Mem.Concrete.storeTyped F.file.tagDefs memory fieldType (.allocated 1 (8192 + offset))
    (.integer (.signed .int) i.typeBits.toInt)).mapError (fun _ => "type member store failed")
  let env := extendEnv [(symbol, .object (.pointer (.allocated 0 4096)))] ∅
  pure ⟨.effectExpr F.body env, [.procedureReturn F.bodyLabels], memory⟩

/-- Return, optional caller-visible type field, and preservation of source
allocations/bytes/lifetimes/stdout. Diagnostic location/read markers are not
observable. There are no calls, global objects, or supplied callee assumptions. -/
abbrev Observation := Option Int × Option Int × Prop

def context (p : Predicate) : Context Input Observation where
  sourceEntry i s := prepare p i = .ok s
  machineEntry i m :=
    SysV.CallEntry (placement p) Source.signature 0
      (.cons (BitVec.ofNat 64 (if i.isNull then 0 else 8192)) .nil) m ∧
    65536 < (m.core.read .rsp).toNat ∧
    (i.isNull = false → m.memory.Permitted .read 8192 64)
  related i _ m := i.isNull = false →
    Silmaril.X86.Ext.loadN m.memory 8216 4 = some (BitVec.ofNat 64 i.typeBits.toNat)
  footprint _ m := SysV.StackBelow m 0
  sourceObservation i s t v :=
    (match v with | .loaded (.specified (.integer n)) => some n | _ => none,
     if i.isNull then none else Mem.Concrete.readInt 8216 t.memory.bytes,
     t.memory.allocations = s.memory.allocations ∧ t.memory.bytes = s.memory.bytes ∧
       t.memory.dead = s.memory.dead ∧ t.memory.stdout = s.memory.stdout)
  machineObservation i _ t :=
    (some ((t.core.read .rax).extractLsb' 0 32).toInt,
     if i.isNull then none else (Silmaril.X86.Ext.loadN t.memory 8216 4).map
       (fun n => (n.extractLsb' 0 32).toInt), True)
  callees := []

/-- Includes actual Ail elaboration/procedure/parameter identity, joint-entry
existence, Core safety and first-return machine refinement with memory effects.
All are obligations; none is assumed as a context validity law. -/
def statement (p : Predicate) : Prop :=
  Source.Projection.exact ∧
  Silmaril.Elf.CodeAt Silmaril.Elf.Staged.Corpus.Cjson.X8664.LibcjsonSo1.F p.address p.code ∧
  C.ElaboratesWith Source.inputs Source.ail p.name (Source.Elaboration.function p) ∧
  Obligation (Source.Elaboration.function p) Silmaril.X86.Open.isa (placement p) (context p)

@[problem "silmaril.corpus.cjson.is_null.contextual_memory"
  (title := "Actual cJSON_IsNull pointer and type-field context")]
def Task.isNull : Prop := statement .isNull
@[problem "silmaril.corpus.cjson.is_bool.contextual_memory"
  (title := "Actual cJSON_IsBool pointer and type-field context")]
def Task.isBool : Prop := statement .isBool
@[problem "silmaril.corpus.cjson.is_number.contextual_memory"
  (title := "Actual cJSON_IsNumber pointer and type-field context")]
def Task.isNumber : Prop := statement .isNumber
@[problem "silmaril.corpus.cjson.is_string.contextual_memory"
  (title := "Actual cJSON_IsString pointer and type-field context")]
def Task.isString : Prop := statement .isString
@[problem "silmaril.corpus.cjson.is_array.contextual_memory"
  (title := "Actual cJSON_IsArray pointer and type-field context")]
def Task.isArray : Prop := statement .isArray
@[problem "silmaril.corpus.cjson.is_object.contextual_memory"
  (title := "Actual cJSON_IsObject pointer and type-field context")]
def Task.isObject : Prop := statement .isObject
@[problem "silmaril.corpus.cjson.is_invalid.contextual_memory"
  (title := "Actual cJSON_IsInvalid pointer and type-field context")]
def Task.isInvalid : Prop := statement .isInvalid
@[problem "silmaril.corpus.cjson.is_false.contextual_memory"
  (title := "Actual cJSON_IsFalse pointer and type-field context")]
def Task.isFalse : Prop := statement .isFalse
@[problem "silmaril.corpus.cjson.is_true.contextual_memory"
  (title := "Actual cJSON_IsTrue pointer and type-field context")]
def Task.isTrue : Prop := statement .isTrue
@[problem "silmaril.corpus.cjson.is_raw.contextual_memory"
  (title := "Actual cJSON_IsRaw pointer and type-field context")]
def Task.isRaw : Prop := statement .isRaw
end Silmaril.Elf.Corpus.CjsonTypePredicates.Context
