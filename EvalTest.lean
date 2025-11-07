import «DTypeChecker».Basic

open Expr Value

-- Helper function to run eval with empty environment
def testEval (e : Expr) : Except ErrMsg Value :=
  ReaderT.run (eval e) []

-- Helper to display test results

def displayTest (_name : String) (expr : Expr) : IO Unit := do
  IO.println <| Expr.toFormatPrec expr 0
  let ex := do
    let val <- testEval expr
    readBackValue initCtx val
  match ex with
  | .error e => IO.println s!"Error: {e}"
  | .ok o => IO.println "Evaluated: "; IO.print $ Expr.toFormatPrec o 0

-- Test 1: Natural number type
#eval displayTest "Natural type" Natural

-- Test 2: Zero
#eval displayTest "Zero" Zero

-- Test 3: Successor
#eval displayTest "Succ of Zero" (Succ Zero)
#eval displayTest "Succ of Succ of Zero" (Succ (Succ Zero))

-- Test 4: Unit type and sole
#eval displayTest "Unit type" Unit
#eval displayTest "sole value" sole

-- Test 5: Empty type
#eval displayTest "Empty type" Empty

-- Test 6: Universe
#eval displayTest "Universe" U

-- Test 7: Refl
#eval displayTest "Refl" Refl

-- Test 8: Lambda with free variable (should error)
#eval displayTest "Lambda with free var" (Lambda "x" (Var "y"))

-- Test 9: Simple lambda application with Let
#eval displayTest "Let binding"
  (Let "x" Zero (Var "x"))

-- Test 10: Let with substitution
#eval displayTest "Let with substitution in body"
  (Let "x" (Succ Zero) (Succ (Var "x")))

-- Test 11: Nested Let bindings
#eval displayTest "Nested Let bindings"
  (Let "x" Zero (Let "y" (Succ (Var "x")) (Var "y")))

-- Test 12: Shadowing test
#eval displayTest "Shadowing - inner x shadows outer x"
  (Let "x" Zero
    (Let "x" (Succ Zero)
      (Var "x")))

-- Test 13: Pi type
#eval displayTest "Pi type: Nat -> Nat"
  (Pi "x" Natural Natural)

-- Test 14: Dependent Pi type
#eval displayTest "Dependent Pi type"
  (Pi "x" Natural (Pi "y" Natural Natural))

-- Test 15: Lambda expression
#eval displayTest "Lambda identity on Nat"
  (Lambda "x" (Var "x"))

-- Test 16: Lambda application via Let
#eval displayTest "Lambda application"
  (Let "f" (Lambda "x" (Succ (Var "x")))
    (Let "arg" Zero
      (App (Var "f") (Var "arg"))))

-- Test 17: Sigma type
#eval displayTest "Sigma type: Σ(x:Nat) × Nat"
  (Sigma "x" Natural Natural)

-- Test 18: Dependent Sigma type
#eval displayTest "Dependent Sigma type"
  (Sigma "x" Natural (Pi "y" Natural Natural))

-- Test 19: Equality type
#eval displayTest "Equality: 0 = 0 : Nat"
  (Equal Natural Zero Zero)

-- Test 20: Complex equality
#eval displayTest "Equality: succ 0 = succ 0 : Nat"
  (Equal Natural (Succ Zero) (Succ Zero))

-- Test 21: The annotation
#eval displayTest "The Natural Zero"
  (The Natural Zero)

-- Test 22: IndNat with Zero
#eval displayTest "IndNat on Zero (should return base)"
  (Let "motive" (Lambda "n" Natural)
    (Let "base" Zero
      (Let "step" (Lambda "pred" (Lambda "ih" (Succ (Var "ih"))))
        (IndNat Zero (Var "motive") (Var "base") (Var "step")))))

-- Test 23: IndNat with Succ
#eval displayTest "IndNat on (Succ Zero)"
  (Let "motive" (Lambda "n" Natural)
    (Let "base" (Succ Zero)
      (Let "step" (Lambda "pred" (Lambda "ih" (Succ (Var "ih"))))
        (IndNat (Succ Zero) (Var "motive") (Var "base") (Var "step")))))

-- Test 24: Replace with Refl
#eval displayTest "Replace with Refl target"
  (Let "motive" (Lambda "x" Natural)
    (Let "base" Zero
      (Replace Refl (Var "motive") (Var "base"))))

-- Test 25: Complex substitution test
#eval displayTest "Complex substitution"
  (Let "a" Zero
    (Let "b" (Succ (Var "a"))
      (Let "c" (Succ (Var "b"))
        (Let "a" (Succ (Succ Zero))  -- Shadow 'a'
          (Succ (Var "c"))))))  -- Should use original 'a' through 'c'

-- Test 26: Multiple shadowing
#eval displayTest "Multiple shadowing levels"
  (Let "x" Zero
    (Let "x" (Succ (Var "x"))
      (Let "x" (Succ (Var "x"))
        (Var "x"))))

-- Test 27: Closure captures environment
#eval displayTest "Closure captures environment"
  (Let "y" (Succ Zero)
    (Let "f" (Lambda "x" (Succ (Var "y")))
      (Let "y" Zero  -- Shadow y
        (App (Var "f") Zero))))  -- f should use original y

-- Test 28: Nested lambda application
#eval displayTest "Nested lambda application"
  (Let "f" (Lambda "x" (Lambda "y" (Var "x")))
    (App (App (Var "f") Zero) (Succ Zero)))

-- Test 29: Lambda with complex body
#eval displayTest "Lambda with Let in body"
  (Let "f" (Lambda "x" (Let "y" (Var "x") (Succ (Var "y"))))
    (App (Var "f") Zero))

-- Test 30: Error case - unbound variable
#eval displayTest "Error: Unbound variable" (Var "unbound")
