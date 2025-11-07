
import «DTypeChecker».Basic

open Expr

-- ========================================
-- Test Suite: Well-formed Dependent Type Lambda Expressions
-- ========================================

-- Test 1: Identity function on natural numbers
-- id_ℕ : ℕ → ℕ
-- id_ℕ = λ x. x
def test1 := Lambda "x" (Var "x")
#eval test1.toFormatPrec 0

-- Test 2: Polymorphic identity function
-- id : Π (A : 𝒰) → A → A
-- id = λ A. λ x. x
def test2 := Lambda "A" (Lambda "x" (Var "x"))
#eval test2.toFormatPrec 0

-- Test 3: Constant function returning zero
-- const_zero : ℕ → ℕ
-- const_zero = λ x. zero
def test3 := Lambda "x" Zero
#eval test3.toFormatPrec 0

-- Test 4: Successor function
-- succ_fn : ℕ → ℕ
-- succ_fn = λ n. succ n
def test4 := Lambda "n" (Succ (Var "n"))
#eval test4.toFormatPrec 0

-- Test 5: Function that returns a type (type-level function)
-- const_type : 𝒰 → 𝒰
-- const_type = λ A. ℕ
def test5 := Lambda "A" Natural
#eval test5.toFormatPrec 0

-- Test 6: Dependent function type (Pi type)
-- The type: Π (n : ℕ) → ℕ
def test6 := Pi "n" Natural Natural
#eval test6.toFormatPrec 0

-- Test 7: Polymorphic function type
-- The type: Π (A : 𝒰) → A → A
def test7 := Pi "A" U (Pi "_" (Var "A") (Var "A"))
#eval test7.toFormatPrec 0

-- Test 8: Function application - applying identity to zero
-- (λ x. x) zero
def test8 := App (Lambda "x" (Var "x")) Zero
#eval test8.toFormatPrec 0

-- Test 9: Function application - applying succ to zero
-- succ zero
def test9 := App (Lambda "n" (Succ (Var "n"))) Zero
#eval test9.toFormatPrec 0

-- Test 10: Dependent pair type (Sigma type)
-- Σ (n : ℕ) × ℕ
def test10 := Sigma "n" Natural Natural
#eval test10.toFormatPrec 0

-- Test 11: Let binding with natural number
-- let x := zero in succ x
def test11 := Let "x" Zero (Succ (Var "x"))
#eval test11.toFormatPrec 0

-- Test 12: Nested let bindings
-- let x := zero in let y := succ x in succ y
def test12 := Let "x" Zero (Let "y" (Succ (Var "x")) (Succ (Var "y")))
#eval test12.toFormatPrec 0

-- Test 13: Lambda returning a lambda (curried function)
-- λ x. λ y. x
def test13 := Lambda "x" (Lambda "y" (Var "x"))
#eval test13.toFormatPrec 0

-- Test 14: Equality type
-- zero ≡ zero : ℕ
def test14 := Equal Natural Zero Zero
#eval test14.toFormatPrec 0

-- Test 15: Reflexivity proof
def test15 := Refl
#eval test15.toFormatPrec 0

-- Test 16: Type annotation with The
-- the ℕ zero
def test16 := The Natural Zero
#eval test16.toFormatPrec 0

-- Test 17: Unit type and its inhabitant
def test17_type := Expr.Unit
def test17_term := sole
#eval test17_type.toFormatPrec 0
#eval test17_term.toFormatPrec 0

-- Test 18: Empty type (bottom)
def test18 := Expr.Empty
#eval test18.toFormatPrec 0

-- Test 19: Universe type
def test19 := U
#eval test19.toFormatPrec 0

-- Test 20: Function that takes a function as argument
-- λ f. λ x. f (f x)
def test20 := Lambda "f" (Lambda "x" (App (Var "f") (App (Var "f") (Var "x"))))
#eval test20.toFormatPrec 0

-- Test 21: Dependent function with equality
-- λ n. λ p. p  where p : n ≡ n : ℕ
def test21 := Lambda "n" (Lambda "p" (Var "p"))
#eval test21.toFormatPrec 0

-- Test 22: Natural number induction expression
-- ind-ℕ zero (λ n. ℕ) zero (λ n. λ ih. succ ih)
def test22 := IndNat Zero
                     (Lambda "n" Natural)
                     Zero
                     (Lambda "n" (Lambda "ih" (Succ (Var "ih"))))
#eval test22.toFormatPrec 0

-- Test 23: Replace (substitution along equality)
-- replace refl (λ x. ℕ) zero
def test23 := Replace Refl (Lambda "x" Natural) Zero
#eval test23.toFormatPrec 0

-- Test 24: Absurd elimination
-- absurd x ℕ  where x : ⊥
def test24 := Absurd (Var "x") Natural
#eval test24.toFormatPrec 0

-- Test 25: Complex nested expression
-- let add1 := λ n. succ n in
-- the (ℕ → ℕ) add1
def test25 := Let "add1"
                  (Lambda "n" (Succ (Var "n")))
                  (The (Pi "x" Natural Natural) (Var "add1"))
#eval test25.toFormatPrec 0

-- Test 26: Dependent pair type with dependency
-- Σ (A : 𝒰) × A
def test26 := Sigma "A" U (Var "A")
#eval test26.toFormatPrec 0

-- Test 27: Type-level lambda returning a Pi type
-- λ A. (A → A)
def test27 := Lambda "A" (Pi "x" (Var "A") (Var "A"))
#eval test27.toFormatPrec 0

-- Test 28: Church numeral style encoding (partial)
-- λ s. λ z. s (s z)
def test28 := Lambda "s" (Lambda "z" (App (Var "s") (App (Var "s") (Var "z"))))
#eval test28.toFormatPrec 0

-- Test 29: Function composition structure
-- λ f. λ g. λ x. f (g x)
def test29 := Lambda "f" (Lambda "g" (Lambda "x" (App (Var "f") (App (Var "g") (Var "x")))))
#eval test29.toFormatPrec 0

-- Test 30: Equality with successor
-- succ zero ≡ succ zero : ℕ
def test30 := Equal Natural (Succ Zero) (Succ Zero)
#eval test30.toFormatPrec 0


-- Tests
#guard αEquiv (Expr.Lambda "x" (Expr.Var "x")) (Expr.Lambda "y" (Expr.Var "y")) == true
#guard αEquiv (Expr.Lambda "x" (Expr.Var "x")) (Expr.Lambda "x" (Expr.Var "y")) == false
#guard αEquiv (Expr.Pi "x" Expr.Natural (Expr.Var "x")) (Expr.Pi "y" Expr.Natural (Expr.Var "y")) == true
#guard αEquiv (Expr.App (Expr.Lambda "x" (Expr.Var "x")) Expr.Zero) (Expr.App (Expr.Lambda "y" (Expr.Var "y")) Expr.Zero) == true
#guard αEquiv (Expr.Lambda "x" (Expr.Lambda "y" (Expr.Var "x"))) (Expr.Lambda "a" (Expr.Lambda "b" (Expr.Var "a"))) == true
#guard αEquiv (Expr.Lambda "x" (Expr.Lambda "y" (Expr.Var "x"))) (Expr.Lambda "a" (Expr.Lambda "b" (Expr.Var "b"))) == false
#guard αEquiv (Expr.Sigma "x" Expr.Natural (Expr.Var "x")) (Expr.Sigma "y" Expr.Natural (Expr.Var "y")) == true
#guard αEquiv (Expr.Let "x" Expr.Zero (Expr.Var "x")) (Expr.Let "y" Expr.Zero (Expr.Var "y")) == true
#guard αEquiv Expr.Natural Expr.Natural == true
#guard αEquiv Expr.Natural Expr.U == false
#guard αEquiv (Expr.Equal Expr.Natural Expr.Zero Expr.Zero) (Expr.Equal Expr.Natural Expr.Zero Expr.Zero) == true
-- Test shadowing: (λ x. λ x. x) should be α-equivalent to (λ y. λ z. z)
#guard αEquiv (Expr.Lambda "x" (Expr.Lambda "x" (Expr.Var "x"))) (Expr.Lambda "y" (Expr.Lambda "z" (Expr.Var "z"))) == true

-- Test shadowing with different structure: (λ x. λ x. x) should NOT be α-equivalent to (λ y. λ z. y)
#guard αEquiv (Expr.Lambda "x" (Expr.Lambda "x" (Expr.Var "x"))) (Expr.Lambda "y" (Expr.Lambda "z" (Expr.Var "y"))) == false

-- Test shadowing in Pi types: (Π (x : ℕ) → Π (x : ℕ) → x) ≡ (Π (a : ℕ) → Π (b : ℕ) → b)
#guard αEquiv (Expr.Pi "x" Expr.Natural (Expr.Pi "x" Expr.Natural (Expr.Var "x"))) (Expr.Pi "a" Expr.Natural (Expr.Pi "b" Expr.Natural (Expr.Var "b"))) == true

-- Test shadowing with Let: (let x := 0 in let x := succ x in x) should handle shadowing correctly
#guard αEquiv (Expr.Let "x" Expr.Zero (Expr.Let "x" (Expr.Succ (Expr.Var "x")) (Expr.Var "x"))) (Expr.Let "y" Expr.Zero (Expr.Let "z" (Expr.Succ (Expr.Var "y")) (Expr.Var "z"))) == true

-- Test shadowing in Sigma: (Σ (x : ℕ) × Σ (x : ℕ) × x)
#guard αEquiv (Expr.Sigma "x" Expr.Natural (Expr.Sigma "x" Expr.Natural (Expr.Var "x"))) (Expr.Sigma "a" Expr.Natural (Expr.Sigma "b" Expr.Natural (Expr.Var "b"))) == true

-- Test complex shadowing: outer variable should not be confused with shadowed inner variable
#guard αEquiv (Expr.Lambda "x" (Expr.App (Expr.Lambda "x" (Expr.Var "x")) (Expr.Var "x"))) (Expr.Lambda "y" (Expr.App (Expr.Lambda "z" (Expr.Var "z")) (Expr.Var "y"))) == true
