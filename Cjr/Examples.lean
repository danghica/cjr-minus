import Cjr.Properties
namespace Cjr.Examples

def int (n : Int) : Expr := .val (.lit (.int n))
def bool (b : Bool) : Expr := .val (.lit (.bool b))
def ptr (l : Loc) : Expr := .val (.lit (.ptr l))
def slot (l : Loc) : Expr := .val (.lit (.stack l))
def obj (l : Loc) : Expr := .val (.lit (.obj l))
def resultInt : RunResult → Option Int
  | .done (.lit (.int n)) _ => some n
  | _ => none
def isStuck : RunResult → Bool
  | .stuck _ _ => true
  | _ => false

/-- Recursive factorial exercises recursive and argument substitution under closures. -/
def factorial : Expr :=
  .recE (some "fact") (some "n")
    (.ifE (.binOp .le (.var "n") (int 1)) (int 1)
      (.binOp .mul (.var "n")
        (.app (.var "fact") (.binOp .minus (.var "n") (int 1)))))

/-- Mutable variables are stack slots; leaving the binding pops the slot. -/
def counter : Expr :=
  .varBind "x" (int 0)
    (.seq (.whileE (.binOp .le (.var "x") (int 4))
      (.assign "x" (.binOp .plus (.var "x") (int 1)))) (.var "x"))

def rawRoundTrip : Expr :=
  .letE (some "p") (.alloc (int 3))
    (.seq (.store (.offset (.var "p") (int 2)) (int 42))
      (.letE (some "answer") (.load (.offset (.var "p") (int 2)))
        (.seq (.free (.var "p")) (.var "answer"))))

def objectRoundTrip : Expr :=
  .letE (some "o") (.new [] [int 1, int 2])
    (.seq (.fieldStore (.var "o") 1 (int 9)) (.fieldLoad (.var "o") 1))

def structRoundTrip : Expr :=
  .varBind "s" (.struct [] [int 1, int 2])
    (.seq (.structStore "s" 0 (int 7)) (.structLoad (.var "s") 0))

-- These equalities are checked by Lean's kernel (no native_decide or external oracle).
example : resultInt (run 200 (.app factorial (int 5)) stateInit) = some 120 := by rfl
example : resultInt (run 200 counter stateInit) = some 5 := by rfl
example : (match run 200 counter stateInit with | .done _ s => s.stack | _ => []) = [] := by rfl
example : resultInt (run 100 rawRoundTrip stateInit) = some 42 := by rfl
example : (match run 100 rawRoundTrip stateInit with | .done _ s => (s.raw.length, s.blocks.length, s.next) | _ => (99,99,99)) = (0,0,3) := by rfl
example : resultInt (run 100 objectRoundTrip stateInit) = some 9 := by rfl
example : resultInt (run 100 structRoundTrip stateInit) = some 7 := by rfl

-- Shadowing, anonymous binders, substitution inside stored closures and aggregates.
example : resultInt (run 100 (.letE (some "x") (int 2)
    (.letE (some "x") (int 8) (.var "x"))) stateInit) = some 8 := by rfl
example : resultInt (run 100 (.varBind "x" (int 1)
    (.seq (.varBind "x" (int 2) (.assign "x" (int 3))) (.var "x"))) stateInit) = some 1 := by rfl
example : resultInt (run 100 (.varBind "x" (int 1)
    (.letE (some "f") (.recE none none (.assign "x" (int 6)))
      (.seq (.app (.var "f") unitExpr) (.var "x")))) stateInit) = some 6 := by rfl
example : resultInt (run 100 (.letE (some "x") (int 4)
    (.structLoad (.val (.struct [.recE none none (.var "x"), .lit (.int 3)])) 1)) stateInit) = some 3 := by rfl
example : resultInt (run 100 (.app (.letE (some "x") (int 4)
    (.val (.recE none none (.var "x")))) unitExpr) stateInit) = some 4 := by rfl
example : resultInt (run 100 (.letE none (int 4) (int 7)) stateInit) = some 7 := by rfl

-- Both binary operands have effects; the final slot records left-to-right order.
def order : Expr := .varBind "x" (int 0)
  (.seq (.binOp .plus (.seq (.assign "x" (int 1)) (int 10))
                         (.seq (.assign "x" (int 2)) (int 20))) (.var "x"))
example : resultInt (run 100 order stateInit) = some 2 := by rfl
-- Boolean and is strict, exactly as in upstream contexts.
example : isStuck (run 20 (.binOp .and (bool false) (.load (ptr 99))) stateInit) = true := by rfl

-- Truncation toward zero, division by zero, and infinite two's-complement bits.
example : binOpEval .div (.lit (.int (-7))) (.lit (.int 3)) = some (.lit (.int (-2))) := by rfl
example : binOpEval .rem (.lit (.int (-7))) (.lit (.int 3)) = some (.lit (.int (-1))) := by rfl
example : binOpEval .div (.lit (.int 7)) (.lit (.int (-3))) = some (.lit (.int (-2))) := by rfl
example : binOpEval .rem (.lit (.int 7)) (.lit (.int (-3))) = some (.lit (.int 1)) := by rfl
example : binOpEval .div (.lit (.int 1)) (.lit (.int 0)) = none := by rfl
example : binOpEval .rem (.lit (.int 1)) (.lit (.int 0)) = none := by rfl
example : intXor (-1) 5 = -6 := by rfl
example : intXor (-3) (-6) = 7 := by rfl
example : intAnd (-1) 5 = 5 := by rfl
example : intAnd (-3) (-6) = -8 := by rfl
example : intAnd 5 (-3) = 5 := by rfl

-- Invalid operations stay stuck. Pointer offset itself is intentionally unchecked.
example : isStuck (run 10 (.alloc (int 0)) stateInit) = true := by rfl
example : isStuck (run 10 (.alloc (int (-1))) stateInit) = true := by rfl
example : isStuck (run 10 (.free (ptr 0)) stateInit) = true := by rfl
example : isStuck (run 10 (.load (ptr 0)) stateInit) = true := by rfl
example : isStuck (run 10 (.store (ptr 0) (int 1)) stateInit) = true := by rfl
example : isStuck (run 10 (.stackLoad (slot 0)) stateInit) = true := by rfl
example : isStuck (run 10 (.stackAssign (slot 0) (int 1)) stateInit) = true := by rfl
example : isStuck (run 10 (.fieldLoad (obj 0) 0) stateInit) = true := by rfl
example : isStuck (run 10 (.fieldStore (obj 0) 0 (int 1)) stateInit) = true := by rfl
example : isStuck (run 10 (.structLoad (.val (.struct [])) 0) stateInit) = true := by rfl
example : isStuck (run 10 (.assign "unbound" (int 1)) stateInit) = true := by rfl
example : isStuck (run 10 (.structStore "unbound" 0 (int 1)) stateInit) = true := by rfl
example : isStuck (run 100 (.letE (some "p") (.alloc (int 2))
    (.free (.offset (.var "p") (int 1)))) stateInit) = true := by rfl
example : isStuck (run 100 (.letE (some "p") (.alloc (int 2))
    (.seq (.free (.var "p")) (.load (.var "p")))) stateInit) = true := by rfl
example : isStuck (run 100 (.letE (some "p") (.alloc (int 1))
    (.seq (.free (.var "p")) (.free (.var "p")))) stateInit) = true := by rfl
example : baseStep (.offset (ptr 0) (int (-8))) stateInit = some (ptr (-8), stateInit) := by rfl
example : baseStep (.pop ⟨9⟩ (int 3)) stateInit = some (int 3, stateInit) := by rfl
example : resultInt (run 0 (int 8) stateInit) = some 8 := by rfl
example : (match run 3 (.whileE (bool true) unitExpr) stateInit with | .timeout _ _ => true | _ => false) = true := by rfl

-- Empty objects still consume an identifier; captured slots do not escape their lifetime.
example : (match run 10 (.new [] []) stateInit with | .done _ s => s.next | _ => -1) = 1 := by rfl
example : isStuck (run 100 (.app (.varBind "x" (int 1)
    (.recE none none (.var "x"))) unitExpr) stateInit) = true := by rfl

/-- A concrete semantic derivation obtained from the proved evaluator soundness theorem. -/
theorem factorial_five : ∃ s, Steps (.app factorial (int 5)) stateInit (int 120) s := by
  exact ⟨stateInit, run_done_steps (fuel := 200) rfl⟩
end Cjr.Examples
