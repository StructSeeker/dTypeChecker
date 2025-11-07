-- This module serves as the root of the `DTypeChecker` library.
-- Import modules here that should be built as part of the library.

-- The Implementation of the type checker is located at `DTypeChecker/Basic.lean`
-- This file is mainly for testing and display purpose

import «DTypeChecker».Basic


-- Derive BEq instances for comparison in tests
deriving instance BEq for Value
deriving instance BEq for Neutral
deriving instance BEq for ErrMsg

instance : Repr Expr where
  reprPrec := Expr.toFormatPrec

-- Derive Repr instances for #eval
deriving instance Repr for Value
deriving instance Repr for Neutral
deriving instance Repr for ErrMsg

-- Derive BEq instance for Except
instance [BEq α] [BEq β] : BEq (Except α β) where
  beq
    | Except.ok a, Except.ok b => a == b
    | Except.error a, Except.error b => a == b
    | _, _ => false

-- Helper function to run type synthesis
def testSynth (e : Expr) : Except ErrMsg Value :=
  ReaderT.run (synth e) initCtx

-- Helper function to run type checking
def testCheck (e : Expr) (ty : Value) : Except ErrMsg Unit :=
  ReaderT.run (check e ty) initCtx

-- Helper to evaluate and read back
def testEvalReadBack (e : Expr) : Except ErrMsg Expr :=
  match ReaderT.run (eval e) [] with
  | Except.ok v => readBackValue initCtx v
  | Except.error err => Except.error err

namespace Tests


section BasicTypes

/-- Test: Universe type -/
def testUniverse : Expr := Expr.U

#eval s!"Universe: {Expr.toFormatPrec testUniverse 0}"
#guard testSynth testUniverse == Except.ok Value.VU

/-- Test: Natural number type -/
def testNatType : Expr := Expr.Natural

#eval s!"Natural Type: {Expr.toFormatPrec testNatType 0}"
#guard testSynth testNatType == Except.ok Value.VU

/-- Test: Zero -/
def testZero : Expr := Expr.Zero

#eval s!"Zero: {Expr.toFormatPrec testZero 0}"
#guard testSynth testZero == Except.ok Value.VNatural

/-- Test: Successor -/
def testSucc : Expr := Expr.Succ Expr.Zero

#eval s!"Succ Zero: {Expr.toFormatPrec testSucc 0}"
#guard testSynth testSucc == Except.ok Value.VNatural

/-- Test: Multiple successors -/
def testThree : Expr := Expr.Succ (Expr.Succ (Expr.Succ Expr.Zero))

#eval s!"Three: {Expr.toFormatPrec testThree 0}"
#guard testSynth testThree == Except.ok Value.VNatural

/-- Test: Unit type -/
def testUnitType : Expr := Expr.Unit

#eval s!"Unit Type: {Expr.toFormatPrec testUnitType 0}"
#guard testSynth testUnitType == Except.ok Value.VU

/-- Test: sole value -/
def testSole : Expr := Expr.sole

#eval s!"Sole: {Expr.toFormatPrec testSole 0}"
#guard testSynth testSole == Except.ok Value.VUnit

/-- Test: Empty type -/
def testEmptyType : Expr := Expr.Empty

#eval s!"Empty Type: {Expr.toFormatPrec testEmptyType 0}"
#guard testSynth testEmptyType == Except.ok Value.VU

end BasicTypes


section FunctionTypes

/-- Test: Simple function type (ℕ → ℕ) -/
def testNatToNat : Expr := Expr.Pi "x" Expr.Natural Expr.Natural

#eval s!"Nat -> Nat: {Expr.toFormatPrec testNatToNat 0}"
#guard testSynth testNatToNat == Except.ok Value.VU

/-- Test: Identity function type -/
def testIdType : Expr := Expr.Pi "A" Expr.U (Expr.Pi "x" (Expr.Var "A") (Expr.Var "A"))

#eval s!"Id Type: {Expr.toFormatPrec testIdType 0}"
#guard testSynth testIdType == Except.ok Value.VU

/-- Test: Identity function implementation -/
def testIdImpl : Expr :=
  Expr.The testIdType
    (Expr.Lambda "A" (Expr.Lambda "x" (Expr.Var "x")))

#eval s!"Id Implementation: {Expr.toFormatPrec testIdImpl 0}"
#guard testSynth testIdImpl matches Except.ok _

/-- Test: Const function (A → B → A) -/
def testConstType : Expr :=
  Expr.Pi "A" Expr.U (Expr.Pi "B" Expr.U
    (Expr.Pi "x" (Expr.Var "A") (Expr.Pi "y" (Expr.Var "B") (Expr.Var "A"))))

#eval s!"Const Type: {Expr.toFormatPrec testConstType 0}"
#guard testSynth testConstType == Except.ok Value.VU

/-- Test: Application -/
def testApp : Expr :=
  Expr.The Expr.Natural
    (Expr.App
      (Expr.The (Expr.Pi "x" Expr.Natural Expr.Natural)
        (Expr.Lambda "x" (Expr.Succ (Expr.Var "x"))))
      Expr.Zero)

#eval s!"Application: {Expr.toFormatPrec testApp 0}"
#guard testSynth testApp == Except.ok Value.VNatural

end FunctionTypes


section SigmaTypes

/-- Test: Simple sigma type (Σ(x : ℕ) × ℕ) -/
def testSimpleSigma : Expr := Expr.Sigma "x" Expr.Natural Expr.Natural

#eval s!"Simple Sigma: {Expr.toFormatPrec testSimpleSigma 0}"
#guard testSynth testSimpleSigma == Except.ok Value.VU

/-- Test: Dependent sigma type (Σ(n : ℕ) × Vec ℕ n) - just the type part -/
def testDepSigmaType : Expr :=
  Expr.Sigma "n" Expr.Natural (Expr.Pi "i" Expr.Natural Expr.Natural)

#eval s!"Dependent Sigma: {Expr.toFormatPrec testDepSigmaType 0}"
#guard testSynth testDepSigmaType == Except.ok Value.VU

end SigmaTypes


section EqualityTypes

/-- Test: Equality type -/
def testEqType : Expr := Expr.Equal Expr.Natural Expr.Zero Expr.Zero

#eval s!"Equality Type: {Expr.toFormatPrec testEqType 0}"
#guard testSynth testEqType == Except.ok Value.VU

/-- Test: Reflexivity with annotation -/
def testReflAnnotated : Expr :=
  Expr.The (Expr.Equal Expr.Natural Expr.Zero Expr.Zero) Expr.Refl

#eval s!"Refl: {Expr.toFormatPrec testReflAnnotated 0}"
#guard testSynth testReflAnnotated matches Except.ok _

def x := testSynth testReflAnnotated
#eval x


/-- Test: Replace (equality elimination) -/
def testReplace : Expr :=
  Expr.The Expr.Natural
    (Expr.Replace
      (Expr.The (Expr.Equal Expr.Natural Expr.Zero Expr.Zero) Expr.Refl)
      (Expr.Lambda "n" Expr.Natural)
      Expr.Zero)

#eval s!"Replace: {Expr.toFormatPrec testReplace 0}"
#guard testSynth testReplace == Except.ok Value.VNatural

end EqualityTypes


section Induction

/-- Test: Addition using ind-Nat -/
def testAddType : Expr := Expr.Pi "m" Expr.Natural (Expr.Pi "n" Expr.Natural Expr.Natural)

def testAdd : Expr :=
  Expr.The testAddType
    (Expr.Lambda "m"
      (Expr.Lambda "n"
        (Expr.IndNat
          (Expr.Var "m")
          (Expr.Lambda "k" Expr.Natural)
          (Expr.Var "n")
          (Expr.Lambda "k" (Expr.Lambda "acc" (Expr.Succ (Expr.Var "acc")))))))

#eval s!"Addition: {Expr.toFormatPrec testAdd 0}"
#guard testSynth testAdd matches Except.ok _

#eval testSynth testAdd


/-- Test: Multiplication using ind-Nat -/
def testMulType : Expr := Expr.Pi "m" Expr.Natural (Expr.Pi "n" Expr.Natural Expr.Natural)

def testMul : Expr :=
  Expr.The testMulType
    (Expr.Lambda "m"
      (Expr.Lambda "n"
        (Expr.IndNat
          (Expr.Var "m")
          (Expr.Lambda "k" Expr.Natural)
          Expr.Zero
          (Expr.Lambda "k" (Expr.Lambda "acc"
            (Expr.App (Expr.App testAdd (Expr.Var "n")) (Expr.Var "acc")))))))

#eval s!"Multiplication Type: {Expr.toFormatPrec testMulType 0}"

end Induction


section LetBindings

/-- Test: Simple let binding -/
def testSimpleLet : Expr :=
  Expr.The Expr.Natural
    (Expr.Let "x" Expr.Zero (Expr.Succ (Expr.Var "x")))

#eval s!"Simple Let: {Expr.toFormatPrec testSimpleLet 0}"
#guard testSynth testSimpleLet == Except.ok Value.VNatural

/-- Test: Nested let bindings -/
def testNestedLet : Expr :=
  Expr.The Expr.Natural
    (Expr.Let "x" Expr.Zero
      (Expr.Let "y" (Expr.Succ (Expr.Var "x"))
        (Expr.Succ (Expr.Var "y"))))

#eval s!"Nested Let: {Expr.toFormatPrec testNestedLet 0}"
#guard testSynth testNestedLet == Except.ok Value.VNatural

end LetBindings

section ComplexExpressions

/-- Test: Nested function application -/
def testNestedApp : Expr :=
  Expr.The Expr.Natural
    (Expr.App
      (Expr.App
        (Expr.The (Expr.Pi "x" Expr.Natural (Expr.Pi "y" Expr.Natural Expr.Natural))
          (Expr.Lambda "x" (Expr.Lambda "y" (Expr.Var "x"))))
        (Expr.Succ Expr.Zero))
      (Expr.Succ (Expr.Succ Expr.Zero)))

#eval s!"Nested Application: {Expr.toFormatPrec testNestedApp 0}"
#guard testSynth testNestedApp == Except.ok Value.VNatural

/-- Test: Complex dependent type -/
def testComplexDep : Expr :=
  Expr.Pi "n" Expr.Natural
    (Expr.Pi "f" (Expr.Pi "i" Expr.Natural Expr.Natural)
      (Expr.Pi "x" Expr.Natural Expr.Natural))

#eval s!"Complex Dependent Type: {Expr.toFormatPrec testComplexDep 0}"
#guard testSynth testComplexDep == Except.ok Value.VU

end ComplexExpressions


section DependentVectors

/-- Vec type: (n : ℕ) → Type -/
def VecType : Expr :=
  Expr.Pi "n" Expr.Natural Expr.U

/-- Vec definition: Vec A n = (i : ℕ) → i < n → A
    For simplicity, we use: Vec A n = (Fin n) → A
    Where Fin n is represented as a natural number with proof it's less than n
-/
def Vec (A : Expr) : Expr :=
  Expr.Lambda "n"
    (Expr.Pi "i" Expr.Natural A)

#eval s!"Vec Type Constructor: {Expr.toFormatPrec (Vec Expr.Natural) 0}"

/-- Empty vector: Vec A 0 -/
def vecNil (A : Expr) : Expr :=
  Expr.The (Expr.App (Vec A) Expr.Zero)
    (Expr.Lambda "i"
      (Expr.Absurd (Expr.Var "i") A))

/-- Vector with one element -/
def vecOne (A : Expr) (x : Expr) : Expr :=
  Expr.The (Expr.App (Vec A) (Expr.Succ Expr.Zero))
    (Expr.Lambda "i"
      x)  -- Simplified: just return x for any index

#eval s!"Vec Nil for Nat: {Expr.toFormatPrec (vecNil Expr.Natural) 0}"
#eval s!"Vec One: {Expr.toFormatPrec (vecOne Expr.Natural Expr.Zero) 0}"

/-- Vector length function type: ∀A. ∀n. Vec A n → ℕ -/
def vecLengthType : Expr :=
  Expr.Pi "A" Expr.U
    (Expr.Pi "n" Expr.Natural
      (Expr.Pi "v" (Expr.App (Vec (Expr.Var "A")) (Expr.Var "n"))
        Expr.Natural))


end DependentVectors


section GirardParadox

/-- Girard's Paradox demonstrates that Type : Type leads to inconsistency.
  We encode a simplified version using our type system.

  The key idea:
  - U' = ∀(X : U), (X → U) → U  (a "large" type)
  - Define a self-applicable term that leads to non-termination
  - This would allow deriving False in a system with Type : Type
-/

/- Type of "large" types: (X : U) → (X → U) → U -/
def UPrime : Expr :=
  Expr.Pi "X" Expr.U (Expr.Pi "f" (Expr.Pi "x" (Expr.Var "X") Expr.U) Expr.U)

#eval s!"U': {Expr.toFormatPrec UPrime 0}"
#guard testSynth UPrime == Except.ok Value.VU

/-- Tau: a function that takes a type operator and returns a type
  tau = λX. λf. ∀(y : U'). (∀(x : X). f x → y X f) → y X f
-/
def tau : Expr :=
  Expr.Lambda "X"
  (Expr.Lambda "f"
    (Expr.Pi "y" UPrime
    (Expr.Pi "_"
      (Expr.Pi "x" (Expr.Var "X")
      (Expr.Pi "_" (Expr.App (Expr.Var "f") (Expr.Var "x"))
        (Expr.App (Expr.App (Expr.Var "y") (Expr.Var "X")) (Expr.Var "f"))))
      (Expr.App (Expr.App (Expr.Var "y") (Expr.Var "X")) (Expr.Var "f")))))

#eval s!"tau: {Expr.toFormatPrec tau 0}"

/-- The type of tau should be U' -/
def tauTyped : Expr := Expr.The UPrime tau

#eval s!"tau typed: {Expr.toFormatPrec tauTyped 0}"
#guard testSynth tauTyped matches Except.ok _

/-- Self-application: tau applied to U and tau itself
  This represents the problematic self-reference
-/
def tauSelfApp : Expr :=
  Expr.App (Expr.App tau Expr.U) tau

#eval s!"tau(U, tau): {Expr.toFormatPrec tauSelfApp 0}"

/- Test that the self-application type-checks
  In a consistent system, this should either Fail to type-check
-/

#eval match testSynth tauSelfApp with
  | Except.ok ty => s!"Self-application type-checks with type: {repr ty}"
  | Except.error msg => s!"Self-application fails (expected in consistent system): {msg}"

/-- Delta combinator using tau: Δ = λx. x U tau x
  This is the classic looping combinator in the paradox
-/
def delta : Expr :=
  Expr.Lambda "x"
  (Expr.App
    (Expr.App (Expr.App (Expr.Var "x") Expr.U) tau)
    (Expr.Var "x"))

def omega : Expr :=
  Expr.App delta delta

#eval s!"Ω = ΔΔ: {Expr.toFormatPrec omega 0}"


#eval match testSynth omega with
  | Except.ok ty => s!"Ω type-checks with type: {repr ty} (demonstrates potential inconsistency)"
  | Except.error msg => s!"Ω fails to type-check: {msg}"

end GirardParadox


section ErrorCases

/-- Test: Type mismatch -/
def testTypeMismatch : Except ErrMsg Unit :=
  testCheck Expr.Zero Value.VUnit

#eval match testTypeMismatch with
  | Except.ok _ => "Should have failed"
  | Except.error msg => s!"Expected error: {msg}"

#guard testTypeMismatch matches Except.error _

/-- Test: Unbound variable -/
def testUnboundVar : Except ErrMsg Value :=
  testSynth (Expr.Var "nonexistent")

#eval match testUnboundVar with
  | Except.ok _ => "Should have failed"
  | Except.error msg => s!"Expected error: {msg}"

#guard testUnboundVar matches Except.error _

/-- Test: Lambda without annotation -/
def testLambdaNoAnnot : Except ErrMsg Value :=
  testSynth (Expr.Lambda "x" (Expr.Var "x"))

#eval match testLambdaNoAnnot with
  | Except.ok _ => "Should have failed"
  | Except.error msg => s!"Expected error: {msg}"

#guard testLambdaNoAnnot matches Except.error _

/-- Test: Application of non-function -/
def testNonFunctionApp : Except ErrMsg Value :=
  testSynth (Expr.App Expr.Zero Expr.Zero)

#eval match testNonFunctionApp with
  | Except.ok _ => "Should have failed"
  | Except.error msg => s!"Expected error: {msg}"

#guard testNonFunctionApp matches Except.error _

end ErrorCases

end Tests
