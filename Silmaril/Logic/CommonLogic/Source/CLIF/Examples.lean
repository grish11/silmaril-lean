module

public import Silmaril.Logic.CommonLogic.Source.CLIF.Thms

@[expose] public section
namespace Silmaril.Logic.CommonLogic.Source.CLIF.Examples
open CategoryTheory
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

def signature : Core.Signature := ⟨String, String, String⟩

def names : Names signature where
  discourse := ["P", "Q", "Cat", "Mat", "On", "Pet", "Happy", "Attr", "x", "y",
    "p", "f", "a;b"].map (fun s => (s,s))
  nondiscourse := [("n","n")]
  marker := [("...free","...free")]

theorem names_valid : names.Valid := by simp [Names.Valid, names]

/-- Complete unchanged Hets TestData/Cat.clif at the pinned source revision. -/
def catSource : String := "(cl-text Cat\n  (P x)\n  (and (P x) (Q y))\n  (or (Cat x) (Mat y))\n  (not (On x y))\n  (if (P x) (Q x))\n  (exists (z) (and (Pet x) (Happy z) (Attr x z)))\n)\n"

def cat : Text names := (readText? names names_valid 128 catSource).get (by rfl)

theorem cat_all_sentences : cat.raw.length = 6 := rfl

theorem cat_source_bound : cat.source = catSource := rfl

/-- Every represented Boolean/binder family, computed function/predicate heads,
nullary application, multiple splices and independently shadowed sequence names. -/
def generalSource : String := "(forall (x ...xs) (exists (y ...ys) (and (= (f) (f y ...xs)) (and) (or) (not (= x y)) (if (p x) (iff ((f x) y ...ys) (n ...xs ...ys ...free))))))"

def general : Text names := (readText? names names_valid 256 generalSource).get (by rfl)

theorem quantified_head :
    (readText? names names_valid 64 "(forall (p) (p p))").isSome = true := rfl

theorem lexical_shadowing :
    (readText? names names_valid 64 "(forall (x ...s) (exists (x ...s) (p x ...s)))").isSome = true := rfl

/-- A semantic signature map may identify symbols without changing a binder's spelling. -/
def identify : signature ⟶ signature := ⟨fun _ => "one", fun _ => "other", fun _ => "...one"⟩

theorem arbitrary_map_preserves_source : (cat.map identify).source = catSource := rfl

theorem arbitrary_map_adequacy (M : Core.Model signature) :
    (CLIF.room (names.map identify)).Sat M (cat.map identify) ↔
      (CLIF.room names).Sat ((Core.Model.reduct identify).obj M) cat :=
  (CLIF.corridor names identify).sat M cat

theorem empty_bare_text_rejected : read 64 "" = none := rfl

theorem empty_named_text_accepted : (read 64 "(cl-text Empty)").isSome = true := rfl

theorem unknown_name_rejected :
    (readText? names names_valid 64 "(p unknown)").isNone = true := rfl

theorem nondiscourse_argument_rejected :
    (readText? names names_valid 64 "(p n)").isNone = true := rfl

theorem nondiscourse_equality_rejected :
    (readText? names names_valid 64 "(= n n)").isNone = true := rfl

theorem sequence_head_rejected : read 64 "(...free x)" = none := rfl

theorem malformed_binder_rejected : read 64 "(forall ((x p)) (p x))" = none := rfl

theorem module_rejected : read 64 "(cl-module A (p x))" = none := rfl

theorem quotation_rejected : forms "(p \"x\")" = none := rfl

/-- The complete real full-CL fixture is outside the represented Core, not silently normalized. -/
def outsideCore : String := "(forall (P ...Q) (and (P x) (...Q x)))\n"

theorem outside_core_rejected : read 64 outsideCore = none := rfl

end Silmaril.Logic.CommonLogic.Source.CLIF.Examples
