import Cjr
open Cjr Cjr.Cangjie
open Cjr.Examples (int)

private def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError ("Printer regression failed: " ++ name))
private def eq (name got expected : String) : IO Unit := do
  unless got == expected do
    throw (IO.userError s!"{name}\nEXPECTED:\n{expected}\nGOT:\n{got}")
private def rejects (name : String) (p : Prog) : IO Unit :=
  check name (match emit p with | .error _ => true | .ok _ => false)
private def withoutBanner (s : String) : String := String.intercalate "\n" ((s.splitOn "\n").drop 1)

def main (args : List String) : IO Unit := do
  let outDir := args.headD ".lake/printer-output"
  IO.FS.createDirAll outDir
  for (name, p) in Cjr.Cangjie.Examples.upstream do
    let golden ← IO.FS.readFile ("tests/golden/" ++ name ++ ".cj")
    eq ("upstream golden: " ++ name) (withoutBanner (printProg p)) (withoutBanner golden)
  for (name, p) in Cjr.Cangjie.Examples.programs do
    let source ← match emit p with
      | .ok s => pure s
      | .error es => throw (IO.userError s!"{name}: {es}")
    IO.FS.writeFile (outDir ++ "/" ++ name ++ ".cj") source
  let env : Env := {}
  eq "Int64 minimum" (lit (.int (-9223372036854775808))) "-9223372036854775808"
  eq "Int64 maximum" (lit (.int 9223372036854775807)) "9223372036854775807"
  eq "float" (lit (.float (-4))) "-4.0"
  eq "null" (lit .null) "CPointer<Int64>()"
  eq "keyword" (ex env "" (.var "this")) "self"
  eq "keyword let" (ex env "" (.var "let")) "let_"
  eq "receiver" (ex {env with this := some "self"} "" (.var "self")) "this"
  eq "anonymous closure" (ex env "" (.recE none (some "x") (.binOp .plus (.var "x") (int 1)))) "{ x => x + 1 }"
  eq "closure value" (exv env "" (.recE none none (int 2))) "{ _ => 2 }"
  eq "binop parentheses" (ex env "" (.binOp .mul (.binOp .plus (int 1) (int 2)) (int 3))) "(1 + 2) * 3"
  eq "compact conditional" (ex env "" (.ifE (.val (.lit (.bool true))) (int 1) (int 2))) "if (true) { 1 } else { 2 }"
  eq "offset load" (ex env "" (.load (.offset (.var "p") (.binOp .plus (int 1) (int 2))))) "unsafe { (p + (1 + 2)).read() }"
  eq "offset store" (ex env "" (.store (.offset (.var "p") (int 2)) (int 7))) "unsafe { (p + 2).write(7) }"
  eq "tuple fallback" (exv env "" (.struct [.lit (.int 1), .lit (.int 2)])) "(1, 2)"
  eq "indexed struct" (ex env "" (.structLoad (.var "p") 2)) "p[2]"
  eq "fallback object field" (ex env "" (.fieldLoad (.var "o") 2)) "o.f2"
  eq "anonymous let" (ex env "" (.letE none (int 1) (int 2))) "1\n2"
  let statements := .letE (some "x") (int 1) (.var "x")
  eq "block argument" (ex env "" (.app (.var "f") statements)) "f({ =>\n    let x = 1\n    x\n}())"
  for (name, term) in [
    ("raw literal", Expr.val (.lit (.ptr 5))),
    ("object literal", .val (.lit (.obj 5))),
    ("slot literal", .val (.lit (.stack 5))),
    ("pop", .pop ⟨0⟩ (int 1)), ("stack load", .stackLoad (.var "x")),
    ("stack assign", .stackAssign (.var "x") (int 1)),
    ("stack field", .stackFieldStore (.var "x") 0 (int 1)),
    ("unknown layout", .new [] []),
    ("recursive closure", .recE (some "f") (some "x") (.var "x")),
    ("recursive closure value", .val (.recE (some "f") (some "x") (.var "x")))] do
    rejects name {main := term}
  rejects "signature arity" {fns := [{name := "f", arg := some "x", body := .var "x"}]}
  rejects "duplicate layout" {classes := [Cjr.Cangjie.Examples.boxC, Cjr.Cangjie.Examples.boxC]}
  rejects "unknown owner" {fns := [{name := "f", owner := some "Missing", arg := some "x", body := int 1}]}
  rejects "invalid function name" {fns := [{name := "main", body := int 1}]}
  rejects "invalid field" {classes := [⟨"Box", [("let", "Int64")]⟩]}
  -- Structural equality drives named-function recognition, not just constructor tags.
  check "structural inequality" (!(Cjr.Cangjie.Examples.binaryBody .mul == Cjr.Cangjie.Examples.binaryBody .div))
  let renamed := renamePtr 4 "p" (.store (.val (.lit (.ptr 4))) (int 2))
  eq "placeholder rename" (ex env "" renamed) "unsafe { p.write(2) }"
  check "rename leaves aggregate values intact"
    (renamePtr 4 "p" (.val (.struct [.lit (.ptr 4)])) == .val (.struct [.lit (.ptr 4)]))
  let copyLoop : Expr := .whileE (.var "cond") (.var "body")
  let copyBody : Expr := .varBind "i" (int 0) copyLoop
  let rules : CopyRules := {methods := [copyBody], loop := some copyLoop}
  let copyProg : Prog := {fns := [{name := "copy", body := copyBody}]}
  check "copy disabled by default" (!((printProg copyProg).splitOn "memmove").length > 1)
  check "copy exact opt-in" (((printProgWith rules copyProg).splitOn "memmove").length == 3)
  check "copy body match required" (!((printProgWith {rules with methods := []} copyProg).splitOn "memmove").length > 1)
  IO.println "Printer checks passed: 8 upstream goldens, 14 emitted programs, literals, layouts, calls, unsupported forms, metadata, and opt-in copy policy."
