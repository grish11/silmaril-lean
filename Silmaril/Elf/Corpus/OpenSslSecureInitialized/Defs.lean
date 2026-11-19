module
public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Project.Shapes.Contextual.Defs
public import Silmaril.X86.Open.Thms
public import Silmaril.Cerberus.Core.Quote.Defs
public import Silmaril.Cerberus.Ail.Quote.Defs
public import Silmaril.Elf.Staged.Reader.Thms
public import Silmaril.Data.IncludeBytes.Kernel
public import Silmaril.Elf.Staged.Corpus.Openssl.X8664.LibcryptoSo3.Bytes
public meta import Silmaril.Project.CompilesTo.Probe.Defs

/-! Actual configured OpenSSL secure-memory getter. The source adapter selects
exact declaration, signature, enabled-branch return and closing-brace spans;
it does not claim a full preprocessed translation unit. The build's enabled
secure-memory configuration correspondence remains explicit provenance evidence.
Global memory and observations are retained; semantic correctness is unproved. -/
@[expose] public section
namespace Silmaril.Elf.Corpus.OpenSslSecureInitialized
open Silmaril.Project.CompilesTo
open Silmaril.Project.Shapes.C
noncomputable def upstreamSource : ByteArray := include_bytes "../../../../corpus/openssl/upstream/openssl-3.5.9/crypto/mem_sec.c"
kbytes_def Source of_include upstreamSource

def cText : String := "static int secure_mem_initialized;\nint CRYPTO_secure_malloc_initialized(void)\n{\n    return secure_mem_initialized;\n}\n"
set_option maxRecDepth 100000 in
def ail : Silmaril.Cerberus.Ail.TypedProgram := ail_program% "($tuple ($none) (sigma ($list ($tuple (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 1 (SD_ObjectAddress ($str \"secure_mem_initialized\"))) ($tuple ($loc_region ($str \"\") 1 12 ($str \"\") 1 34) (Attrs ($list)) (Decl_object ($tuple (Static) ($false)) ($none) (qualifiers ($false) ($false) ($false)) (Ctype ($list (Aloc ($loc_region ($str \"\") 1 8 ($str \"\") 1 11))) (Basic (Integer (Signed (Int_)))))))) ($tuple (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 2 (SD_Id ($str \"CRYPTO_secure_malloc_initialized\"))) ($tuple ($loc_region ($str \"\") 2 5 ($str \"\") 2 37) (Attrs ($list)) (Decl_function ($false) ($tuple (qualifiers ($false) ($false) ($false)) (Ctype ($list (Aloc ($loc_region ($str \"\") 2 1 ($str \"\") 2 4))) (Basic (Integer (Signed (Int_)))))) ($list) ($false) ($false) ($false))))) ($list ($tuple (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 1 (SD_ObjectAddress ($str \"secure_mem_initialized\"))) (AnnotatedExpression (GenRValueType (GenBasic (GenInteger (Concrete (Signed (Int_)))))) ($list (Astd ($str \"\u00a76.5.1#3\")) (Astd ($str \"\u00a76.7.9#11, sentence 3\"))) ($loc_unknown) (AilEconst (ConstantInteger (IConstant 0 (Octal) ($none))))))) ($list ($tuple (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 2 (SD_Id ($str \"CRYPTO_secure_malloc_initialized\"))) ($tuple ($loc_region ($str \"\") 2 1 ($str \"\") 5 2) 3 (Attrs ($list)) ($list) (statement ($loc_region ($str \"\") 3 1 ($str \"\") 5 2) (desug_info ($false) ($none)) (Attrs ($list)) (AilSblock ($list) ($list (statement ($loc_region ($str \"\") 4 5 ($str \"\") 4 35) (desug_info ($false) ($none)) (Attrs ($list)) (AilSreturn (AnnotatedExpression (GenRValueType (GenBasic (GenInteger (Concrete (Signed (Int_)))))) ($list (Astd ($str \"\u00a76.5.16.1#1, bullet 1\"))) ($loc_region ($str \"\") 4 12 ($str \"\") 4 34) (AilErvalue (AnnotatedExpression (GenLValueType (qualifiers ($false) ($false) ($false)) (Ctype ($list (Aloc ($loc_region ($str \"\") 1 8 ($str \"\") 1 11))) (Basic (Integer (Signed (Int_))))) ($false)) ($list (Astd ($str \"\u00a76.5.16.1#1, bullet 1\"))) ($loc_region ($str \"\") 4 12 ($str \"\") 4 34) (AilEident (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 1 (SD_ObjectAddress ($str \"secure_mem_initialized\"))))))))))))))) ($list) ($list) ($map ($tuple (Identifier ($loc_region ($str \"\") 2 5 ($str \"\") 2 37) ($str \"CRYPTO_secure_malloc_initialized\")) ($tuple (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 2 (SD_Id ($str \"CRYPTO_secure_malloc_initialized\"))) (IK_definition)))) ($map) ($map) ($list) ($list) ($list) ($list) ($list) ($map)))"
#guard (FrontendAil cText).toOption.map Silmaril.Project.CompilesTo.Probe.ailText ==
  some (Silmaril.Project.CompilesTo.Probe.ailText ail)
set_option maxRecDepth 100000 in
def doc : Silmaril.Cerberus.Codec.Document := core_document% "($document 1 ($str \"silmaril-lean Lean Cerberus port (Project.Shapes.C.ElabAil)\") ($str \"TargetCoherence.linuxLP64; ParameterCallReturn.Example.runtime (constructed)\") (generic_file ($none) (Normal_callconv) ($map) ($map ($tuple (Symbol ($str \"\") 2 (SD_Id ($str \"conv_loaded_int\"))) (Fun (BTy_loaded (OTy_integer)) ($list ($tuple (Symbol ($str \"\") 10 (SD_Id ($str \"type\"))) (BTy_ctype)) ($tuple (Symbol ($str \"\") 11 (SD_Id ($str \"value\"))) (BTy_loaded (OTy_integer)))) (Pexpr ($list) ($unit) (PEcase (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 11 (SD_Id ($str \"value\"))))) ($list ($tuple (Pattern ($list) (CaseCtor (Cspecified) ($list (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 12 (SD_Id ($str \"number\")))) (BTy_object (OTy_integer)))))))) (Pexpr ($list) ($unit) (PEctor (Cspecified) ($list (Pexpr ($list) ($unit) (PEcall (Sym (Symbol ($str \"\") 3 (SD_Id ($str \"conv_int\")))) ($list (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 10 (SD_Id ($str \"type\"))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))))))))))))))))) ($tuple (Symbol ($str \"\") 3 (SD_Id ($str \"conv_int\"))) (Fun (BTy_object (OTy_integer)) ($list ($tuple (Symbol ($str \"\") 10 (SD_Id ($str \"type\"))) (BTy_ctype)) ($tuple (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))) (BTy_object (OTy_integer)))) (Pexpr ($list) ($unit) (PEif (Pexpr ($list) ($unit) (PEop (OpEq) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 10 (SD_Id ($str \"type\"))))) (Pexpr ($list) ($unit) (PEval (Vctype (Ctype ($list) (Basic (Integer (Bool))))))))) (Pexpr ($list) ($unit) (PEval (Vobject (OVinteger ($iv 0))))) (Pexpr ($list) ($unit) (PEif (Pexpr ($list) ($unit) (PEcall (Sym (Symbol ($str \"\") 4 (SD_Id ($str \"is_representable_integer\")))) ($list (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 10 (SD_Id ($str \"type\")))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))))) (Pexpr ($list) ($unit) (PEval (Vobject (OVinteger ($iv 0))))))))))) ($tuple (Symbol ($str \"\") 4 (SD_Id ($str \"is_representable_integer\"))) (Fun (BTy_boolean) ($list ($tuple (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))) (BTy_object (OTy_integer))) ($tuple (Symbol ($str \"\") 10 (SD_Id ($str \"type\"))) (BTy_ctype))) (Pexpr ($list) ($unit) (PEop (OpAnd) (Pexpr ($list) ($unit) (PEop (OpLe) (Pexpr ($list) ($unit) (PEctor (Civmin) ($list (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 10 (SD_Id ($str \"type\")))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))))))) (Pexpr ($list) ($unit) (PEop (OpLe) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))))) (Pexpr ($list) ($unit) (PEctor (Civmax) ($list (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 10 (SD_Id ($str \"type\")))))))))))))) ($tuple (Symbol ($str \"\") 30 (SD_Id ($str \"params_length\"))) (Fun (BTy_object (OTy_integer)) ($list ($tuple (Symbol ($str \"\") 32 (SD_Id ($str \"cs\"))) (BTy_list (BTy_ctype)))) (Pexpr ($list) ($unit) (PEcall (Sym (Symbol ($str \"\") 31 (SD_Id ($str \"params_length_aux\")))) ($list (Pexpr ($list) ($unit) (PEval (Vobject (OVinteger ($iv 0))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 32 (SD_Id ($str \"cs\")))))))))) ($tuple (Symbol ($str \"\") 31 (SD_Id ($str \"params_length_aux\"))) (Fun (BTy_object (OTy_integer)) ($list ($tuple (Symbol ($str \"\") 33 (SD_Id ($str \"acc\"))) (BTy_object (OTy_integer))) ($tuple (Symbol ($str \"\") 34 (SD_Id ($str \"cs_aux\"))) (BTy_list (BTy_ctype)))) (Pexpr ($list) ($unit) (PEcase (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 34 (SD_Id ($str \"cs_aux\"))))) ($list ($tuple (Pattern ($list) (CaseCtor (Cnil (BTy_ctype)) ($list))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 33 (SD_Id ($str \"acc\")))))) ($tuple (Pattern ($list) (CaseCtor (Ccons) ($list (Pattern ($list) (CaseBase ($tuple ($none) (BTy_ctype)))) (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 35 (SD_Id ($str \"xs\")))) (BTy_list (BTy_ctype)))))))) (Pexpr ($list) ($unit) (PEcall (Sym (Symbol ($str \"\") 31 (SD_Id ($str \"params_length_aux\")))) ($list (Pexpr ($list) ($unit) (PEop (OpAdd) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 33 (SD_Id ($str \"acc\"))))) (Pexpr ($list) ($unit) (PEval (Vobject (OVinteger ($iv 1))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 35 (SD_Id ($str \"xs\")))))))))))))) ($tuple (Symbol ($str \"\") 36 (SD_Id ($str \"params_nth\"))) (Fun (BTy_ctype) ($list ($tuple (Symbol ($str \"\") 37 (SD_Id ($str \"cs_nth\"))) (BTy_list (BTy_ctype))) ($tuple (Symbol ($str \"\") 38 (SD_Id ($str \"n\"))) (BTy_object (OTy_integer)))) (Pexpr ($list) ($unit) (PEcase (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 37 (SD_Id ($str \"cs_nth\"))))) ($list ($tuple (Pattern ($list) (CaseCtor (Cnil (BTy_ctype)) ($list))) (Pexpr ($list) ($unit) (PEundef ($loc_unknown) (UB038_number_of_args)))) ($tuple (Pattern ($list) (CaseCtor (Ccons) ($list (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 39 (SD_Id ($str \"head\")))) (BTy_ctype)))) (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 40 (SD_Id ($str \"tail\")))) (BTy_list (BTy_ctype)))))))) (Pexpr ($list) ($unit) (PEif (Pexpr ($list) ($unit) (PEop (OpEq) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 38 (SD_Id ($str \"n\"))))) (Pexpr ($list) ($unit) (PEval (Vobject (OVinteger ($iv 0))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 39 (SD_Id ($str \"head\"))))) (Pexpr ($list) ($unit) (PEundef ($loc_unknown) (UB038_number_of_args)))))))))))) ($map) ($list ($tuple (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 1 (SD_ObjectAddress ($str \"secure_mem_initialized\"))) (GlobalDef ($tuple (BTy_object (OTy_pointer)) (Ctype ($list (Aloc ($loc_region ($str \"\") 1 8 ($str \"\") 1 11))) (Basic (Integer (Signed (Int_)))))) (Expr ($list (Aloc ($loc_unknown))) (Esseq (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 104 (SD_None))) (BTy_object (OTy_pointer))))) (Expr ($list) (Eaction (Paction (Pos) (Action ($loc_region ($str \"\") 1 12 ($str \"\") 1 34) ($unit) (Create (Pexpr ($list) ($unit) (PEctor (Civalignof) ($list (Pexpr ($list) ($unit) (PEval (Vctype (Ctype ($list (Aloc ($loc_region ($str \"\") 1 8 ($str \"\") 1 11))) (Basic (Integer (Signed (Int_))))))))))) (Pexpr ($list) ($unit) (PEval (Vctype (Ctype ($list (Aloc ($loc_region ($str \"\") 1 8 ($str \"\") 1 11))) (Basic (Integer (Signed (Int_)))))))) (PrefSource ($loc_region ($str \"\") 1 12 ($str \"\") 1 34) ($list (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 1 (SD_ObjectAddress ($str \"secure_mem_initialized\")))))))))) (Expr ($list) (Esseq (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 105 (SD_None))) (BTy_loaded (OTy_integer))))) (Expr ($list (Astd ($str \"\u00a76.5#2\"))) (Ebound (Expr ($list (Aloc ($loc_unknown)) (Aexpr) (Avalue (Ainteger (Signed (Int_))))) (Epure (Pexpr ($list) ($unit) (PEval (Vloaded (LVspecified (OVinteger ($iv 0)))))))))) (Expr ($list) (Esseq (Pattern ($list) (CaseBase ($tuple ($none) (BTy_unit)))) (Expr ($list) (Eaction (Paction (Pos) (Action ($loc_region ($str \"\") 1 12 ($str \"\") 1 34) ($unit) (Store ($false) (Pexpr ($list) ($unit) (PEval (Vctype (Ctype ($list (Aloc ($loc_region ($str \"\") 1 8 ($str \"\") 1 11))) (Basic (Integer (Signed (Int_)))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 104 (SD_None)))) (Pexpr ($list) ($unit) (PEcall (Sym (Symbol ($str \"\") 2 (SD_Id ($str \"conv_loaded_int\")))) ($list (Pexpr ($list) ($unit) (PEval (Vctype (Ctype ($list (Aloc ($loc_region ($str \"\") 1 8 ($str \"\") 1 11))) (Basic (Integer (Signed (Int_)))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 105 (SD_None))))))) (NA)))))) (Expr ($list) (Epure (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 104 (SD_None))))))))))))))) ($map ($tuple (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 2 (SD_Id ($str \"CRYPTO_secure_malloc_initialized\"))) (Proc ($loc_region ($str \"\") 2 1 ($str \"\") 5 2) ($some 3) (BTy_loaded (OTy_integer)) ($list) (Expr ($list) (Esseq (Pattern ($list) (CaseBase ($tuple ($none) (BTy_unit)))) (Expr ($list (Aloc ($loc_region ($str \"\") 3 1 ($str \"\") 5 2)) (Astmt)) (Esseq (Pattern ($list) (CaseBase ($tuple ($none) (BTy_unit)))) (Expr ($list (Aloc ($loc_region ($str \"\") 4 5 ($str \"\") 4 35)) (Astmt)) (Esseq (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 102 (SD_None))) (BTy_loaded (OTy_integer))))) (Expr ($list (Astd ($str \"\u00a76.5#2\"))) (Ebound (Expr ($list (Aloc ($loc_region ($str \"\") 4 12 ($str \"\") 4 34)) (Aexpr) (Avalue (Ainteger (Signed (Int_))))) (Ewseq (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 101 (SD_None))) (BTy_object (OTy_pointer))))) (Expr ($list (Aloc ($loc_region ($str \"\") 4 12 ($str \"\") 4 34)) (Aexpr)) (Epure (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 1 (SD_ObjectAddress ($str \"secure_mem_initialized\"))))))) (Expr ($list) (Eaction (Paction (Pos) (Action ($loc_region ($str \"\") 4 12 ($str \"\") 4 34) ($unit) (Load (Pexpr ($list) ($unit) (PEval (Vctype (Ctype ($list (Aloc ($loc_region ($str \"\") 1 8 ($str \"\") 1 11))) (Basic (Integer (Signed (Int_)))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 101 (SD_None)))) (NA)))))))))) (Expr ($list) (Erun ($unit) (Symbol ($str \"\") 100 (SD_Id ($str \"ret_100\"))) ($list (Pexpr ($list) ($unit) (PEcall (Sym (Symbol ($str \"\") 2 (SD_Id ($str \"conv_loaded_int\")))) ($list (Pexpr ($list) ($unit) (PEval (Vctype (Ctype ($list (Aloc ($loc_region ($str \"\") 2 1 ($str \"\") 2 4))) (Basic (Integer (Signed (Int_)))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 102 (SD_None)))))))))))) (Expr ($list) (Epure (Pexpr ($list) ($unit) (PEval (Vunit))))))) (Expr ($list (Alabel (LAreturn)) (Aloc ($loc_region ($str \"\") 2 1 ($str \"\") 5 2))) (Esave ($tuple (Symbol ($str \"\") 100 (SD_Id ($str \"ret_100\"))) (BTy_loaded (OTy_integer))) ($list ($tuple (Symbol ($str \"\") 103 (SD_None)) ($tuple ($tuple (BTy_loaded (OTy_integer)) ($some ($tuple (Ctype ($list (Aloc ($loc_region ($str \"\") 2 1 ($str \"\") 2 4))) (Basic (Integer (Signed (Int_))))) (By_value)))) (Pexpr ($list (Astd ($str \"\u00a76.9.1#12\"))) ($unit) (PEundef ($loc_region ($str \"\") 2 1 ($str \"\") 5 2) (UB088_reached_end_of_function)))))) (Expr ($list) (Epure (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 103 (SD_None))))))))))))) ($map ($tuple (Identifier ($loc_region ($str \"\") 2 5 ($str \"\") 2 37) ($str \"CRYPTO_secure_malloc_initialized\")) ($tuple ($list (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 2 (SD_Id ($str \"CRYPTO_secure_malloc_initialized\")))) (LK_normal (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 2 (SD_Id ($str \"CRYPTO_secure_malloc_initialized\"))))))) ($map ($tuple (Symbol ($str \"11db5df2f711ffc72acc8b1300081ab8\") 2 (SD_Id ($str \"CRYPTO_secure_malloc_initialized\"))) ($tuple ($loc_region ($str \"\") 2 1 ($str \"\") 5 2) (Attrs ($list)) (Ctype ($list (Aloc ($loc_region ($str \"\") 2 1 ($str \"\") 2 4))) (Basic (Integer (Signed (Int_))))) ($list) ($false) ($false)))) ($map) ($map)))\n"
def core : Silmaril.Cerberus.Codec.FileBindings := fixRet doc.bindings
def signature : Silmaril.X86.SystemV.CApi.Signature := ⟨[], some .int32⟩
def sourceFn : CFn signature where
  file := core.toFile
  params := paramsOf core "CRYPTO_secure_malloc_initialized"
  body := (procParts core "CRYPTO_secure_malloc_initialized").2

theorem source_span_0 : Silmaril.Elf.Staged.Reader.kread Source 2227 34 =
    some (Silmaril.X86.Link.Blob.valueLE ("static int secure_mem_initialized;".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat)) := by
  decide +kernel

theorem source_span_1 : Silmaril.Elf.Staged.Reader.kread Source 3497 44 =
    some (Silmaril.X86.Link.Blob.valueLE ("int CRYPTO_secure_malloc_initialized(void)\n{".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat)) := by
  decide +kernel

theorem source_span_2 : Silmaril.Elf.Staged.Reader.kread Source 3575 34 =
    some (Silmaril.X86.Link.Blob.valueLE ("    return secure_mem_initialized;".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat)) := by
  decide +kernel

theorem source_span_3 : Silmaril.Elf.Staged.Reader.kread Source 3668 1 =
    some (Silmaril.X86.Link.Blob.valueLE ("}".toUTF8.data.toList.map fun b => BitVec.ofNat 8 b.toNat)) := by
  decide +kernel

def code : List (BitVec 8) := [0x8b, 0x5, 0x2, 0x17, 0x2a, 0x0, 0xc3]
def placement : Silmaril.Project.Shapes.Placement := ⟨0x1eab70, code, 0⟩
open Silmaril.Cerberus Silmaril.Cerberus.Core.Dynamics
open Silmaril.Project.Shapes.Contextual
/-- Exact symbol from the real elaborated global table, not an arbitrary Core variable. -/
def globalSymbol : Sym := (core.globs[0]'(by decide +kernel)).1

def intType : Ctype := .mk [] (.basic (.integer (.signed .int)))
/-- One live signed-int global; no heap, threads, callbacks or external callees. -/
def globalMemory (n : BitVec 32) : Mem.Concrete.State :=
  { nextId := 1, lastAddress := 4096,
    allocations := Map.ofList [(0, ⟨4096, 4, false, false, some intType, none, .UB064_modifying_const⟩)],
    bytes := Mem.Concrete.writeInt 4096 (Mem.Concrete.reprInt n.toInt) ∅ }

def entry (n : BitVec 32) : State :=
  ⟨.effectExpr sourceFn.body
    (extendEnv [(globalSymbol, .object (.pointer (.allocated 0 4096)))] ∅),
    [.procedureReturn sourceFn.bodyLabels], globalMemory n⟩

/-- Return value, global contents and stdout. Source allocations, bytes, lifetime and stdout must remain unchanged;
read diagnostics (`lastUsed`, `currentLocation`) are deliberately unobserved. Machine writes are confined to the explicit stack frame. -/
abbrev Observation := Option Int × Option Int × Prop

def context : Context (BitVec 32) Observation where
  sourceEntry n s := s = entry n
  machineEntry _ m :=
    Silmaril.Project.Shapes.SysV.CallEntry placement signature 0 .nil m ∧
    m.memory.Permitted .read 0x48c278 4
  related n _ m := Silmaril.X86.Ext.loadN m.memory 0x48c278 4 = some (BitVec.ofNat 64 n.toNat)
  footprint _ m := Silmaril.Project.Shapes.SysV.StackBelow m 0
  sourceObservation _ s t v :=
    (match v with | .loaded (.specified (.integer z)) => some z | _ => none,
     Mem.Concrete.readInt 4096 t.memory.bytes,
     (t.memory.allocations = s.memory.allocations ∧ t.memory.bytes = s.memory.bytes ∧
       t.memory.dead = s.memory.dead ∧ t.memory.stdout = s.memory.stdout))
  machineObservation _ _ t :=
    (some ((t.core.read .rax).extractLsb' 0 32).toInt,
     (Silmaril.X86.Ext.loadN t.memory 0x48c278 4).map fun z => (z.extractLsb' 0 32).toInt,
     True)
  callees := []

/-- Every signed-int global value admits a joint entry and is safe in actual
Core; every first machine return matches the return and preserved global state.
No theorem claiming this obligation is supplied. -/
@[problem "silmaril.corpus.openssl.secure_initialized.contextual_memory"
  (title := "Configured OpenSSL global getter preserves caller-visible state")]
def Task.compiles_to : Prop :=
  ElaboratesTo ail "CRYPTO_secure_malloc_initialized" sourceFn ∧
  Obligation sourceFn Silmaril.X86.Open.isa placement context
end Silmaril.Elf.Corpus.OpenSslSecureInitialized
