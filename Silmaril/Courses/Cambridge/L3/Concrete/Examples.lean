module

import Silmaril.Courses.Cambridge.L3.Concrete.Grammar
meta import Silmaril.Courses.Cambridge.L3.Concrete.Grammar
import Silmaril.Courses.Cambridge.L2.Concrete.Grammar
meta import Silmaril.Courses.Cambridge.L2.Concrete.Grammar

/-! Executable UTF-8 regressions checked by the Courses library glob. -/

namespace Silmaril.Courses.Cambridge.L3.Concrete

#guard match parseType "(int ref) * (bool + unit)".toUTF8 with
  | some (.prod (.ref .int) (.sum .bool .unit)) => true
  | _ => false

#guard match parseType "{q:bool,p:(int→int)}".toUTF8 with
  | some (.record labels fields) =>
    labels.names == ["q", "p"] &&
      (match List.ofFn fields with | [.bool, .arr .int .int] => true | _ => false)
  | _ => false

#guard match parse "{q=true,p=7}".toUTF8 with
  | some (.record labels fields) =>
    labels.names == ["q", "p"] &&
      (match List.ofFn fields with | [.bool true, .int 7] => true | _ => false)
  | _ => false

#guard match parse "{p={q=1},r=2}.p".toUTF8 with
  | some (.project (.record labels fields) "p") =>
    labels.names == ["p", "r"] &&
      (match List.ofFn fields with | [.record inner _, .int 2] => inner.names == ["q"] | _ => false)
  | _ => false

#guard match parse "{}".toUTF8, parseType "{}".toUTF8 with
  | some (.record labels _), some (.record types _) => labels.names.isEmpty && types.names.isEmpty
  | _, _ => false

#guard match parse "fun p:(int∗bool)→fst p".toUTF8 with
  | some (.lam "p" (.prod .int .bool) (.fst (.var "p"))) => true
  | _ => false

#guard match parse "fst (1, snd (2,3))".toUTF8 with
  | some (.fst (.pair (.int 1) (.snd (.pair (.int 2) (.int 3))))) => true
  | _ => false

#guard match parse "(ref 0,ref 0)".toUTF8 with
  | some (.pair (.ref (.int 0)) (.ref (.int 0))) => true
  | _ => false

#guard match parse "l := !l0".toUTF8 with
  | some (.assign (.loc 0) (.deref (.loc 1))) => true
  | _ => false

#guard match parse "(!r := ref −5)".toUTF8 with
  | some (.assign (.deref (.var "r")) (.ref (.int n))) => n == -5
  | _ => false

#guard match parseResolved "let r:(int ref)=ref 0 in !r".toUTF8 with
  | some (.letE (.ref .int) (.ref (.int 0)) (.deref (.bvar 0))) => true
  | _ => false

#guard match parse "while (!l>=0) do ((l:=(!l + -1));skip) done".toUTF8 with
  | some (.loop (.binary (.deref (.loc 0)) .ge (.int 0))
        (.seq (.assign (.loc 0) (.binary (.deref (.loc 0)) .add (.int _))) .skip)) => true
  | _ => false

#guard match parse "if true then (inl 3:(int+bool)) else (inr false:(int+bool))".toUTF8 with
  | some (.cond (.bool true) (.inl (.int 3) (.sum .int .bool))
        (.inr (.bool false) (.sum .int .bool))) => true
  | _ => false

#guard match parseResolved
    "match (inl 2:(int+bool)) with inl (x:int)->(x+y) | inr (y:bool)->x".toUTF8 with
  | some (.matchSum (.inl (.int 2) _) .int (.binary (.bvar 0) .add (.fvar "y"))
      .bool (.fvar "x")) => true
  | _ => false

#guard match parseResolved "let rec f:int→int=(fun x:int→(f x)) in (f 0)".toUTF8 with
  | some (.letRecFun .int .int (.app (.bvar 1) (.bvar 0)) (.app (.bvar 0) (.int 0))) => true
  | _ => false

#guard match parse "let rec f:{p:int}→int=(fun x:({p:int})→(x.p)) in (f {p=7})".toUTF8 with
  | some (.letRecFun "f" "x" (.record _ _) .int (.project (.var "x") "p")
      (.app (.var "f") (.record _ _))) => true
  | _ => false

def sampleLabels : RecordLabels := ⟨["p", "q"], by decide⟩

private theorem sampleName (i : sampleLabels.Index) : IsName (sampleLabels.label i) := by
  obtain ⟨n, hi⟩ := i
  change n < 2 at hi
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl
  · change IsName "p"
    decide
  · change IsName "q"
    decide

private def sampleTerm : SourceExpr :=
  ⟨.record sampleLabels (fun _ => .ref (.loc 3)), fun i => ⟨sampleName i, trivial⟩⟩

private def sampleType : SourceType :=
  ⟨.record sampleLabels (fun _ => .ref .bool), fun i => ⟨sampleName i, trivial⟩⟩

#guard String.fromUTF8? (print sampleTerm) == some "{ p = ref l2 , q = ref l2 }"
#guard (parse (print sampleTerm)).map termTokens == some (termTokens sampleTerm.val)
#guard String.fromUTF8? (printType sampleType) == some "{ p : ( bool ref ) , q : ( bool ref ) }"
#guard (parseType (printType sampleType)).map typeTokens == some (typeTokens sampleType.val)

#guard (parse (ByteArray.mk #[0x31, 0xc0, 0xaf])).isNone
#guard (parseType (ByteArray.mk #[0xe2, 0x88])).isNone
#guard (parse "{p=0,p=1}".toUTF8).isNone
#guard (parseType "{p:int,p:bool}".toUTF8).isNone
#guard (parse "{p={q=0,q=1}}".toUTF8).isNone
#guard (parse "{p=0,}".toUTF8).isNone
#guard (parseType "{p:int,}".toUTF8).isNone
#guard (parse "{p:0}".toUTF8).isNone
#guard (parseType "{p=int}".toUTF8).isNone
#guard (parse "{0=1}".toUTF8).isNone
#guard (parse "({p=0}.p) )".toUTF8).isNone
#guard (parse "(1,)".toUTF8).isNone
#guard (parse "fst".toUTF8).isNone
#guard (parse "ref".toUTF8).isNone
#guard (parse "!".toUTF8).isNone
#guard (parse "inl 2".toUTF8).isNone
#guard (parse "inr : (int+bool)".toUTF8).isNone
#guard (parse "match x with inl (y:int)->y | inl (z:int)->z".toUTF8).isNone
#guard (parse "match x with inl (y:int)->y | inr (z)->z".toUTF8).isNone
#guard (parse "let rec f:{p:int,q:bool}→int=(fun x:{q:bool,p:int}→0) in 0".toUTF8).isNone
#guard (parse "fun ref:int→skip".toUTF8).isNone
#guard (parse "#0".toUTF8).isNone
#guard (parse "l00".toUTF8).isNone

-- L3-only words remain ordinary L2 names.
#guard L2.Concrete.parse "fun ref:int→ref".toUTF8 = some (.lam "ref" .int (.var "ref"))

-- Sewell pp. 69–71, explicitly paired products and ascribed sums.
#guard (parseType "int ∗ int ∗ int".toUTF8).isNone
#guard match parseType "int ∗ (int ∗ int)".toUTF8, parseType "(int ∗ int) ∗ int".toUTF8 with
  | some (.prod .int (.prod .int .int)), some (.prod (.prod .int .int) .int) => true
  | _, _ => false
#guard (parse "1, 2".toUTF8).isNone
#guard (parse "(1, 2, 3)".toUTF8).isNone
#guard match parse "(1+2, 3≥4)".toUTF8 with
  | some (.pair (.binary (.int 1) .add (.int 2)) (.binary (.int 3) .ge (.int 4))) => true
  | _ => false
#guard match parse "inl 3:int + bool".toUTF8, parse "inl 3:int + int".toUTF8 with
  | some (.inl (.int 3) (.sum .int .bool)), some (.inl (.int 3) (.sum .int .int)) => true
  | _, _ => false

#guard match parseResolved
    "match inl 3:int+bool with inl (x:int) → x+1 | inr (y:bool) → if y then 2 else 0".toUTF8 with
  | some (.matchSum (.inl (.int 3) (.sum .int .bool)) .int (.binary (.bvar 0) .add (.int 1))
      .bool (.cond (.bvar 0) (.int 2) (.int 0))) => true
  | _ => false
#guard match parseResolved
    ("match a with inl (x:int) → match b with inl (y:int) → x + y | inr (z:int) → z" ++
      " | inr (w:int) → w").toUTF8 with
  | some (.matchSum (.fvar "a") .int
      (.matchSum (.fvar "b") .int (.binary (.bvar 1) .add (.bvar 0)) .int (.bvar 0))
      .int (.bvar 0)) => true
  | _ => false
#guard (parse "match x with inl (y:int) → y + 1 | inr (z:int) z".toUTF8).isNone

-- Sewell pp. 73–74, projection of a literal and a ref parameter.
#guard match parse "{p=17,q=true}.p".toUTF8 with
  | some (.project (.record labels _) "p") => labels.names == ["p", "q"]
  | _ => false
#guard match parse "fun x:int ref → !x".toUTF8 with
  | some (.lam "x" (.ref .int) (.deref (.var "x"))) => true
  | _ => false

-- Sewell p. 75, storing a function that calls through its own reference.
#guard match parse
    ("let x:(int → int) ref = ref(fun z:int → z) in " ++
      "(x := (fun z:int → if z ≥ 1 then z + ((!x) (z + −1)) else 0); (!x) 3)").toUTF8 with
  | some (.letE "x" (.ref (.arr .int .int)) (.ref (.lam "z" .int (.var "z")))
      (.seq (.assign (.var "x") (.lam "z" .int (.cond (.binary (.var "z") .ge (.int 1))
        (.binary (.var "z") .add (.app (.deref (.var "x")) (.binary (.var "z") .add (.int (-1)))))
        (.int 0)))) (.app (.deref (.var "x")) (.int 3)))) => true
  | _ => false

#guard match parseType "int ref ∗ bool + unit → int → bool".toUTF8 with
  | some (.arr (.sum (.prod (.ref .int) .bool) .unit) (.arr .int .bool)) => true
  | _ => false
#guard match parse "f r.p.q (ref 0)".toUTF8 with
  | some (.app (.app (.var "f") (.project (.project (.var "r") "p") "q")) (.ref (.int 0))) => true
  | _ => false
#guard match parse "fst r.p".toUTF8 with
  | some (.project (.fst (.var "r")) "p") => true
  | _ => false
#guard match parse "r := !r + 1; !r".toUTF8 with
  | some (.seq (.assign (.var "r") (.binary (.deref (.var "r")) .add (.int 1))) (.deref (.var "r"))) =>
    true
  | _ => false
#guard (parse "r := s := 1".toUTF8).isNone
#guard (parseType "int + bool + unit".toUTF8).isNone
#guard (parse "{p=1+2,p=3}".toUTF8).isNone
#guard (parse "{p=1+2}.l0".toUTF8).isNone
#guard (parse "r.if".toUTF8).isNone

end Silmaril.Courses.Cambridge.L3.Concrete
