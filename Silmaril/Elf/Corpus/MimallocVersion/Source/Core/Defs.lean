module

public import Silmaril.Elf.Corpus.MimallocVersion.Source.Defs
public import Silmaril.Elf.Corpus.MimallocVersion.Thms
public import Silmaril.Elf.Staged.Corpus.Mimalloc.X8664.LibmimallocSo21.Thms
public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.Quote.Defs
public import Silmaril.Cerberus.Ail.Quote.Defs
public meta import Silmaril.Project.CompilesTo.Probe.Defs
public meta import Silmaril.Elf.Corpus.MimallocVersion.Source.Defs

/-!
# Pinned mimalloc C definition to canonical ELF: a contextual function problem

`Source.cText` is the exact closed preprocessed definition from the build that reproduced
canonical mimalloc2.1.9 byte-for-byte. Its byte span is kernel checked against the included
translation unit. The external GCC preprocessing/build provenance is a trust boundary;
this is not a successful frontend parse or semantic validation of the whole translation unit.

The actual Lean frontend produces the quoted typed Ail (checked by compiled evaluation,
because its typing is partial). The actual LP64 elaborator produces the quoted Core;
`Thms.elaborates` checks that binding in the kernel. The C-to-ELF goal is unproved.

Context: System V AMD64, no arguments, signed int32 return, Open/Ext8 model, valid entry
with a readable return address and disjoint loaded code, zero writable stack frame below
entry RSP, callee-saved registers restored. No globals, heap, callee or environment effects
are permitted by the contract. Source UB follows the CFn meaning; `CompilesTo` additionally
requires an inhabited safe source meaning and enterable machine calls, not a vacuous
source-safety assumption. The definition is a literal-return leaf in the current narrow
integer/call-free profile, not support for the allocator or arbitrary C memory/calls.
-/

@[expose] public section

namespace Silmaril.Elf.Corpus.MimallocVersion.Source.Core

open Silmaril.Project.CompilesTo
open Silmaril.Project.Shapes.C

set_option maxRecDepth 100000 in
def ail : Silmaril.Cerberus.Ail.TypedProgram := ail_program% "($tuple ($none) (sigma ($list ($tuple (Symbol ($str \"b4cc5ccaa25245ed7ea981dc179c7f19\") 1 (SD_Id ($str \"mi_version\"))) ($tuple ($loc_region ($str \"\") 1 5 ($str \"\") 1 15) (Attrs ($list)) (Decl_function ($false) ($tuple (qualifiers ($false) ($false) ($false)) (Ctype ($list (Aloc ($loc_region ($str \"\") 1 1 ($str \"\") 1 4))) (Basic (Integer (Signed (Int_)))))) ($list) ($false) ($false) ($false))))) ($list) ($list ($tuple (Symbol ($str \"b4cc5ccaa25245ed7ea981dc179c7f19\") 1 (SD_Id ($str \"mi_version\"))) ($tuple ($loc_region ($str \"\") 1 1 ($str \"\") 3 2) 2 (Attrs ($list)) ($list) (statement ($loc_region ($str \"\") 1 22 ($str \"\") 3 2) (desug_info ($false) ($none)) (Attrs ($list)) (AilSblock ($list) ($list (statement ($loc_region ($str \"\") 2 3 ($str \"\") 2 14) (desug_info ($false) ($none)) (Attrs ($list)) (AilSreturn (AnnotatedExpression (GenRValueType (GenBasic (GenInteger (Concrete (Signed (Int_)))))) ($list (Astd ($str \"§6.5.1#3\"))) ($loc_region ($str \"\") 2 10 ($str \"\") 2 13) (AilEconst (ConstantInteger (IConstant 219 (Decimal) ($none))))))))))))) ($list) ($list) ($map ($tuple (Identifier ($loc_region ($str \"\") 1 5 ($str \"\") 1 15) ($str \"mi_version\")) ($tuple (Symbol ($str \"b4cc5ccaa25245ed7ea981dc179c7f19\") 1 (SD_Id ($str \"mi_version\"))) (IK_definition)))) ($map) ($map) ($list) ($list) ($list) ($list) ($list) ($map)))"

#guard (FrontendAil cText).toOption.map Silmaril.Project.CompilesTo.Probe.ailText ==
  some (Silmaril.Project.CompilesTo.Probe.ailText ail)

set_option maxRecDepth 100000 in
def doc : Silmaril.Cerberus.Codec.Document := core_document% "($document 1 ($str \"silmaril-lean Lean Cerberus port (Project.Shapes.C.ElabAil)\") ($str \"TargetCoherence.linuxLP64; ParameterCallReturn.Example.runtime (constructed)\") (generic_file ($none) (Normal_callconv) ($map) ($map ($tuple (Symbol ($str \"\") 2 (SD_Id ($str \"conv_loaded_int\"))) (Fun (BTy_loaded (OTy_integer)) ($list ($tuple (Symbol ($str \"\") 10 (SD_Id ($str \"type\"))) (BTy_ctype)) ($tuple (Symbol ($str \"\") 11 (SD_Id ($str \"value\"))) (BTy_loaded (OTy_integer)))) (Pexpr ($list) ($unit) (PEcase (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 11 (SD_Id ($str \"value\"))))) ($list ($tuple (Pattern ($list) (CaseCtor (Cspecified) ($list (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 12 (SD_Id ($str \"number\")))) (BTy_object (OTy_integer)))))))) (Pexpr ($list) ($unit) (PEctor (Cspecified) ($list (Pexpr ($list) ($unit) (PEcall (Sym (Symbol ($str \"\") 3 (SD_Id ($str \"conv_int\")))) ($list (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 10 (SD_Id ($str \"type\"))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))))))))))))))))) ($tuple (Symbol ($str \"\") 3 (SD_Id ($str \"conv_int\"))) (Fun (BTy_object (OTy_integer)) ($list ($tuple (Symbol ($str \"\") 10 (SD_Id ($str \"type\"))) (BTy_ctype)) ($tuple (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))) (BTy_object (OTy_integer)))) (Pexpr ($list) ($unit) (PEif (Pexpr ($list) ($unit) (PEop (OpEq) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 10 (SD_Id ($str \"type\"))))) (Pexpr ($list) ($unit) (PEval (Vctype (Ctype ($list) (Basic (Integer (Bool))))))))) (Pexpr ($list) ($unit) (PEval (Vobject (OVinteger ($iv 0))))) (Pexpr ($list) ($unit) (PEif (Pexpr ($list) ($unit) (PEcall (Sym (Symbol ($str \"\") 4 (SD_Id ($str \"is_representable_integer\")))) ($list (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 10 (SD_Id ($str \"type\")))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))))) (Pexpr ($list) ($unit) (PEval (Vobject (OVinteger ($iv 0))))))))))) ($tuple (Symbol ($str \"\") 4 (SD_Id ($str \"is_representable_integer\"))) (Fun (BTy_boolean) ($list ($tuple (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))) (BTy_object (OTy_integer))) ($tuple (Symbol ($str \"\") 10 (SD_Id ($str \"type\"))) (BTy_ctype))) (Pexpr ($list) ($unit) (PEop (OpAnd) (Pexpr ($list) ($unit) (PEop (OpLe) (Pexpr ($list) ($unit) (PEctor (Civmin) ($list (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 10 (SD_Id ($str \"type\")))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))))))) (Pexpr ($list) ($unit) (PEop (OpLe) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 12 (SD_Id ($str \"number\"))))) (Pexpr ($list) ($unit) (PEctor (Civmax) ($list (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 10 (SD_Id ($str \"type\")))))))))))))) ($tuple (Symbol ($str \"\") 30 (SD_Id ($str \"params_length\"))) (Fun (BTy_object (OTy_integer)) ($list ($tuple (Symbol ($str \"\") 32 (SD_Id ($str \"cs\"))) (BTy_list (BTy_ctype)))) (Pexpr ($list) ($unit) (PEcall (Sym (Symbol ($str \"\") 31 (SD_Id ($str \"params_length_aux\")))) ($list (Pexpr ($list) ($unit) (PEval (Vobject (OVinteger ($iv 0))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 32 (SD_Id ($str \"cs\")))))))))) ($tuple (Symbol ($str \"\") 31 (SD_Id ($str \"params_length_aux\"))) (Fun (BTy_object (OTy_integer)) ($list ($tuple (Symbol ($str \"\") 33 (SD_Id ($str \"acc\"))) (BTy_object (OTy_integer))) ($tuple (Symbol ($str \"\") 34 (SD_Id ($str \"cs_aux\"))) (BTy_list (BTy_ctype)))) (Pexpr ($list) ($unit) (PEcase (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 34 (SD_Id ($str \"cs_aux\"))))) ($list ($tuple (Pattern ($list) (CaseCtor (Cnil (BTy_ctype)) ($list))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 33 (SD_Id ($str \"acc\")))))) ($tuple (Pattern ($list) (CaseCtor (Ccons) ($list (Pattern ($list) (CaseBase ($tuple ($none) (BTy_ctype)))) (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 35 (SD_Id ($str \"xs\")))) (BTy_list (BTy_ctype)))))))) (Pexpr ($list) ($unit) (PEcall (Sym (Symbol ($str \"\") 31 (SD_Id ($str \"params_length_aux\")))) ($list (Pexpr ($list) ($unit) (PEop (OpAdd) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 33 (SD_Id ($str \"acc\"))))) (Pexpr ($list) ($unit) (PEval (Vobject (OVinteger ($iv 1))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 35 (SD_Id ($str \"xs\")))))))))))))) ($tuple (Symbol ($str \"\") 36 (SD_Id ($str \"params_nth\"))) (Fun (BTy_ctype) ($list ($tuple (Symbol ($str \"\") 37 (SD_Id ($str \"cs_nth\"))) (BTy_list (BTy_ctype))) ($tuple (Symbol ($str \"\") 38 (SD_Id ($str \"n\"))) (BTy_object (OTy_integer)))) (Pexpr ($list) ($unit) (PEcase (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 37 (SD_Id ($str \"cs_nth\"))))) ($list ($tuple (Pattern ($list) (CaseCtor (Cnil (BTy_ctype)) ($list))) (Pexpr ($list) ($unit) (PEundef ($loc_unknown) (UB038_number_of_args)))) ($tuple (Pattern ($list) (CaseCtor (Ccons) ($list (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 39 (SD_Id ($str \"head\")))) (BTy_ctype)))) (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 40 (SD_Id ($str \"tail\")))) (BTy_list (BTy_ctype)))))))) (Pexpr ($list) ($unit) (PEif (Pexpr ($list) ($unit) (PEop (OpEq) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 38 (SD_Id ($str \"n\"))))) (Pexpr ($list) ($unit) (PEval (Vobject (OVinteger ($iv 0))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 39 (SD_Id ($str \"head\"))))) (Pexpr ($list) ($unit) (PEundef ($loc_unknown) (UB038_number_of_args)))))))))))) ($map) ($list) ($map ($tuple (Symbol ($str \"b4cc5ccaa25245ed7ea981dc179c7f19\") 1 (SD_Id ($str \"mi_version\"))) (Proc ($loc_region ($str \"\") 1 1 ($str \"\") 3 2) ($some 2) (BTy_loaded (OTy_integer)) ($list) (Expr ($list) (Esseq (Pattern ($list) (CaseBase ($tuple ($none) (BTy_unit)))) (Expr ($list (Aloc ($loc_region ($str \"\") 1 22 ($str \"\") 3 2)) (Astmt)) (Esseq (Pattern ($list) (CaseBase ($tuple ($none) (BTy_unit)))) (Expr ($list (Aloc ($loc_region ($str \"\") 2 3 ($str \"\") 2 14)) (Astmt)) (Esseq (Pattern ($list) (CaseBase ($tuple ($some (Symbol ($str \"\") 101 (SD_None))) (BTy_loaded (OTy_integer))))) (Expr ($list (Astd ($str \"§6.5#2\"))) (Ebound (Expr ($list (Aloc ($loc_region ($str \"\") 2 10 ($str \"\") 2 13)) (Aexpr) (Avalue (Ainteger (Signed (Int_))))) (Epure (Pexpr ($list) ($unit) (PEval (Vloaded (LVspecified (OVinteger ($iv 219)))))))))) (Expr ($list) (Erun ($unit) (Symbol ($str \"\") 100 (SD_Id ($str \"ret_100\"))) ($list (Pexpr ($list) ($unit) (PEcall (Sym (Symbol ($str \"\") 2 (SD_Id ($str \"conv_loaded_int\")))) ($list (Pexpr ($list) ($unit) (PEval (Vctype (Ctype ($list (Aloc ($loc_region ($str \"\") 1 1 ($str \"\") 1 4))) (Basic (Integer (Signed (Int_)))))))) (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 101 (SD_None)))))))))))) (Expr ($list) (Epure (Pexpr ($list) ($unit) (PEval (Vunit))))))) (Expr ($list (Alabel (LAreturn)) (Aloc ($loc_region ($str \"\") 1 1 ($str \"\") 3 2))) (Esave ($tuple (Symbol ($str \"\") 100 (SD_Id ($str \"ret_100\"))) (BTy_loaded (OTy_integer))) ($list ($tuple (Symbol ($str \"\") 102 (SD_None)) ($tuple ($tuple (BTy_loaded (OTy_integer)) ($some ($tuple (Ctype ($list (Aloc ($loc_region ($str \"\") 1 1 ($str \"\") 1 4))) (Basic (Integer (Signed (Int_))))) (By_value)))) (Pexpr ($list (Astd ($str \"§6.9.1#12\"))) ($unit) (PEundef ($loc_region ($str \"\") 1 1 ($str \"\") 3 2) (UB088_reached_end_of_function)))))) (Expr ($list) (Epure (Pexpr ($list) ($unit) (PEsym (Symbol ($str \"\") 102 (SD_None))))))))))))) ($map ($tuple (Identifier ($loc_region ($str \"\") 1 5 ($str \"\") 1 15) ($str \"mi_version\")) ($tuple ($list (Symbol ($str \"b4cc5ccaa25245ed7ea981dc179c7f19\") 1 (SD_Id ($str \"mi_version\")))) (LK_normal (Symbol ($str \"b4cc5ccaa25245ed7ea981dc179c7f19\") 1 (SD_Id ($str \"mi_version\"))))))) ($map ($tuple (Symbol ($str \"b4cc5ccaa25245ed7ea981dc179c7f19\") 1 (SD_Id ($str \"mi_version\"))) ($tuple ($loc_region ($str \"\") 1 1 ($str \"\") 3 2) (Attrs ($list)) (Ctype ($list (Aloc ($loc_region ($str \"\") 1 1 ($str \"\") 1 4))) (Basic (Integer (Signed (Int_))))) ($list) ($false) ($false)))) ($map) ($map)))\n"

def core : Silmaril.Cerberus.Codec.FileBindings := fixRet doc.bindings

def sourceFn : CFn signature where
  file := core.toFile
  params := paramsOf core "mi_version"
  body := (procParts core "mi_version").2

def Task.elaborates : Prop := ElaboratesTo ail "mi_version" sourceFn

def canonicalPlacement : Silmaril.Project.Shapes.Placement := ⟨0xe2b0, codeO3, 0⟩

/-- The actual source function's Core must implement its canonical delivered ELF function.
The source-to-Core condition is independently checked; the machine contract is unproved. -/
@[problem "silmaril.corpus.mimalloc.mi_version.c_to_elf"
  (title := "Pinned closed mimalloc C definition implements its canonical ELF function")]
def Task.compiles_to : Prop :=
  ElaboratesTo ail "mi_version" sourceFn ∧
  CompilesTo Silmaril.X86.Open.isa canonicalPlacement 0 sourceFn

end Silmaril.Elf.Corpus.MimallocVersion.Source.Core
