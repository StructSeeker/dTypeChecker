-- A Toy Implementation of Dependent Type Checker by NbE (Normalization by Evaluation method)


abbrev Name := String

def nextName (x : Name) : Name := x ++ "'"

partial def freshen (used : List Name) (x : Name) : Name :=
  if used.elem x then
    freshen used (nextName x)
  else x

-- Lean std doesn't implement this, i don't know is it by design or an omission
instance [MonadExcept ε m] : MonadExcept ε (ReaderT ρ m) where
  throw e := fun _ => throw e
  tryCatch body handler := fun x => tryCatch (body x) (handler · x)


/--
  Inducitve Type for Lambda Expression, note it's not necessary well-formed
-/
inductive Expr : Type where
    | Let : Name -> Expr -> Expr -> Expr -- (let x := e1 in e2)
    | Var : Name -> Expr --  x
    | Pi : Name -> Expr -> Expr -> Expr  -- (Π ((x A)) B)
    | Lambda : Name -> Expr -> Expr -- (λ (x) b)
    | App : Expr -> Expr -> Expr -- (rator rand)
    | Sigma : Name -> Expr -> Expr -> Expr -- (Σ ((x A)) D)
    | Natural : Expr -- Nat
    | Zero : Expr -- Empty
    | Succ : Expr -> Expr -- (add1 e)
    | IndNat : Expr -> Expr -> Expr -> Expr -> Expr -- (ind-Nat target motive base step)
    | Equal : Expr -> Expr -> Expr -> Expr -- (= A left right)
    | Refl : Expr  -- same
    | Replace : Expr -> Expr -> Expr -> Expr -- (replace tgt mot base)
    | Unit : Expr -- Unit
    | sole : Expr  -- sole
    | Empty : Expr -- Absurd
    | Absurd : Expr -> Expr -> Expr -- (ind-Absurd tgt mot)
    | U : Expr -- Universe
    | The : Expr -> Expr -> Expr -- (the type expr)
deriving BEq, Nonempty


/-- return a Formated String for dependent type lambda expression-/
def Expr.toFormatPrec (e : Expr) (prec : Nat) : Std.Format :=
  let paren (s : String) := if prec > 0 then "(" ++ s ++ ")" else s
    match e with
    | Expr.Let name e1 e2 => s!"let {name} := {Expr.toFormatPrec e1 0} in \n\t {Expr.toFormatPrec e2 0}"
    | Expr.Var x => x
    | Expr.Pi x a b => paren s!"Π ({x} : {Expr.toFormatPrec a 0}) → {Expr.toFormatPrec b 0}"
    | Expr.Lambda x body => paren s!"λ {x}. {Expr.toFormatPrec body 0}"
    | Expr.App f arg => paren s!"{Expr.toFormatPrec f 1} {Expr.toFormatPrec arg 2}"
    | Expr.Sigma x a d => paren s!"Σ ({x} : {Expr.toFormatPrec a 0}) × {Expr.toFormatPrec d 0}"
    | Expr.Natural => "ℕ"
    | Expr.Zero => "zero"
    | Expr.Succ n => paren s!"succ {Expr.toFormatPrec n 1}"
    | Expr.IndNat target motive base step =>
        paren s!"ind-ℕ {Expr.toFormatPrec target 1} {Expr.toFormatPrec motive 1} {Expr.toFormatPrec base 1} {Expr.toFormatPrec step 1}"
    | Expr.Equal ty left right =>
        paren s!"{Expr.toFormatPrec left 1} ≡ {Expr.toFormatPrec right 1} : {Expr.toFormatPrec ty 1}"
    | Expr.Refl => "refl"
    | Expr.Replace tgt mot base =>
        paren s!"replace {Expr.toFormatPrec tgt 1} {Expr.toFormatPrec mot 1} {Expr.toFormatPrec base 1}"
    | Expr.Unit => "⊤"
    | Expr.sole => "⋆"
    | Expr.Empty => "⊥"
    | Expr.Absurd tgt mot => paren s!"absurd {Expr.toFormatPrec tgt 1} {Expr.toFormatPrec mot 1}"
    | Expr.U => "𝒰"
    | Expr.The ty expr => paren s!"the {Expr.toFormatPrec ty 1} {Expr.toFormatPrec expr 1}"

def αEquiv.Aux : Nat -> List (Name × Nat) -> Expr -> List (Name × Nat) -> Expr -> Bool
  | _, ctx1, Expr.Var x, ctx2, Expr.Var y =>
      match ctx1.lookup x, ctx2.lookup y with
      | some i, some j => i == j
      | none, none => x == y
      | _, _ => false
  | depth, ctx1, Expr.Pi x a1 b1, ctx2, Expr.Pi y a2 b2 =>
      αEquiv.Aux depth ctx1 a1 ctx2 a2 &&
      αEquiv.Aux (depth + 1) ((x, depth) :: ctx1) b1 ((y, depth) :: ctx2) b2
  | depth, ctx1, Expr.Lambda x b1, ctx2, Expr.Lambda y b2 =>
      αEquiv.Aux (depth + 1) ((x, depth) :: ctx1) b1 ((y, depth) :: ctx2) b2
  | depth, ctx1, Expr.App f1 a1, ctx2, Expr.App f2 a2 =>
      αEquiv.Aux depth ctx1 f1 ctx2 f2 && αEquiv.Aux depth ctx1 a1 ctx2 a2
  | depth, ctx1, Expr.Sigma x a1 d1, ctx2, Expr.Sigma y a2 d2 =>
      αEquiv.Aux depth ctx1 a1 ctx2 a2 &&
      αEquiv.Aux (depth + 1) ((x, depth) :: ctx1) d1 ((y, depth) :: ctx2) d2
  | depth, ctx1, Expr.Let x e1 b1, ctx2, Expr.Let y e2 b2 =>
      αEquiv.Aux depth ctx1 e1 ctx2 e2 &&
      αEquiv.Aux (depth + 1) ((x, depth) :: ctx1) b1 ((y, depth) :: ctx2) b2
  | depth, ctx1, Expr.Succ n1, ctx2, Expr.Succ n2 =>
      αEquiv.Aux depth ctx1 n1 ctx2 n2
  | depth, ctx1, Expr.IndNat t1 m1 b1 s1, ctx2, Expr.IndNat t2 m2 b2 s2 =>
      αEquiv.Aux depth ctx1 t1 ctx2 t2 &&
      αEquiv.Aux depth ctx1 m1 ctx2 m2 &&
      αEquiv.Aux depth ctx1 b1 ctx2 b2 &&
      αEquiv.Aux depth ctx1 s1 ctx2 s2
  | depth, ctx1, Expr.Equal ty1 l1 r1, ctx2, Expr.Equal ty2 l2 r2 =>
      αEquiv.Aux depth ctx1 ty1 ctx2 ty2 &&
      αEquiv.Aux depth ctx1 l1 ctx2 l2 &&
      αEquiv.Aux depth ctx1 r1 ctx2 r2
  | depth, ctx1, Expr.Replace t1 m1 b1, ctx2, Expr.Replace t2 m2 b2 =>
      αEquiv.Aux depth ctx1 t1 ctx2 t2 &&
      αEquiv.Aux depth ctx1 m1 ctx2 m2 &&
      αEquiv.Aux depth ctx1 b1 ctx2 b2
  | depth, ctx1, Expr.Absurd t1 m1, ctx2, Expr.Absurd t2 m2 =>
      αEquiv.Aux depth ctx1 t1 ctx2 t2 &&
      αEquiv.Aux depth ctx1 m1 ctx2 m2
  | depth, ctx1, Expr.The ty1 e1, ctx2, Expr.The ty2 e2 =>
      αEquiv.Aux depth ctx1 ty1 ctx2 ty2 &&
      αEquiv.Aux depth ctx1 e1 ctx2 e2
  | _, _, Expr.Natural, _, Expr.Natural => true
  | _, _, Expr.Zero, _, Expr.Zero => true
  | _, _, Expr.Refl, _, Expr.Refl => true
  | _, _, Expr.Unit, _, Expr.Unit => true
  | _, _, Expr.sole, _, Expr.sole => true
  | _, _, Expr.Empty, _, Expr.Empty => true
  | _, _, Expr.U, _, Expr.U => true
  | _, _, _, _, _ => false


def αEquiv (e1 : Expr) (e2 : Expr) : Bool := αEquiv.Aux 0 [] e1 [] e2


mutual
  inductive Value where
    | VU : Value
    | VPi : Value -> Closure  -> Value
    | VLambda : Closure -> Value
    | VSigma :Value -> Closure -> Value
    | VNatural : Value
    | VZero : Value
    | VSucc : Value -> Value
    | VEq : Value -> Value -> Value -> Value
    | VRefl : Value
    | VUnit :  Value
    | VSole : Value
    | VAbsurd : Value
    | VNeutral : Value -> Neutral  -> Value
  deriving Nonempty


  inductive Neutral where
    | NVar : Name -> Neutral
    | NApp : Neutral -> Normal -> Neutral
    | NIndNat : Neutral -> Normal -> Normal ->  Normal -> Neutral
    | NReplace : Neutral -> Normal -> Normal -> Neutral
    | NIndAbsurd : Neutral -> Normal -> Neutral
  deriving Nonempty

  structure Normal where
    ty : Value
    val : Value

  structure Closure where
    name : Name
    env : List (Name × Value)
    body : Expr
  deriving Nonempty

end
abbrev Env := List (Name × Value)

inductive CtxEntry where
  | valOfTy: (val: Value) -> (ty: Value) -> CtxEntry -- Define a name to be a value of Particular Type,
  | IsOf: (ty: Value) -> CtxEntry -- declare a name to be of Particular Type

abbrev Ctx := List (Name × CtxEntry)

/-- Init an empty Context-/
def initCtx : Ctx := []

/-- Return a list containing all names from the context-/
def ctxNames (ctx : Ctx) : List Name  := ctx.map (·.1)

/-- Extend Context with new definition or bounded variable-/
def extendCtx (ctx: Ctx) (name: Name) (entry : CtxEntry) : Ctx := (name, entry) :: ctx

abbrev ErrMsg := String

/-- Look up the type of a variable during type checking
An alternative type would be:
Ctx → Name → Option Message Ty
-/
def lookupType [Monad m] [MonadReader Ctx m] [MonadExcept ErrMsg m]: Name -> m Value := fun name => do
  let ctx ← read
  match ctx.lookup name with
  | none => throw s!"Variable '{name}' not found in context"
  | some (CtxEntry.valOfTy _ ty) => return ty
  | some (CtxEntry.IsOf ty) => return ty

/-- Convert Context to environment where each variable declaration maps to a variable (neutral term)-/
def mkEnv : Ctx -> Env
| [] => []
| (name, e)::ctx =>
  let rest := mkEnv ctx
  match e with
  | CtxEntry.valOfTy val _ => (name, val) :: rest
  | CtxEntry.IsOf ty => (name, Value.VNeutral ty (Neutral.NVar name)) :: rest


mutual
/--
Alternative Signature
def eval: Env -> Expr -> Except ErrMsg Value
expected monad m:= ReaderT r (Except e) = λa. r -> Either e a
-/
partial def eval [Monad m] [MonadReader Env m] [MonadWithReader Env m] [MonadExcept ErrMsg m]: Expr -> m Value
| Expr.Var x => do
    let env ← read
    match env.lookup x with
    | some v => return v
    | none => throw s!"Unbound variable: {x}"
| Expr.Lambda x body => do
    let env ← read
    return Value.VLambda { env := env, name := x, body := body }
| Expr.Pi x a b => do
    let aVal ← eval a
    let env ← read
    return Value.VPi aVal { env := env, name := x, body := b }
| Expr.App rator rand => do
    let ratorVal ← eval rator
    let randVal ← eval rand
    match ratorVal with
    | Value.VLambda closure => evalClosure closure randVal
    | Value.VNeutral ty neu =>
        let randNorm := Normal.mk ty randVal
        return Value.VNeutral ty (Neutral.NApp neu randNorm)
    | _ => throw "Application of non-function"
| Expr.Let x e body => do
    let eVal ← eval e
    let env ← read
    let newEnv := (x, eVal) :: env
    withReader (fun _ => newEnv) (eval body)
| Expr.Sigma x a d => do
    let aVal ← eval a
    let env ← read
    return Value.VSigma aVal { env := env, name := x, body := d }
| Expr.Natural => return Value.VNatural
| Expr.Zero => return Value.VZero
| Expr.Succ n => do
    let nVal ← eval n
    return Value.VSucc nVal
| Expr.IndNat target motive base step => do
    let targetVal ← eval target
    let motiveVal ← eval motive
    let baseVal ← eval base
    let stepVal ← eval step
    match targetVal with
    | Value.VZero => return baseVal
    | Value.VSucc n =>
        let ihVal ← evalIndNat n motiveVal baseVal stepVal
        let stepApp1 ← doApply stepVal n
        doApply stepApp1 ihVal
    | Value.VNeutral ty neu =>
        let motiveNorm := Normal.mk Value.VU motiveVal
        let baseNorm := Normal.mk Value.VU baseVal
        let stepNorm := Normal.mk Value.VU stepVal
        return Value.VNeutral ty (Neutral.NIndNat neu motiveNorm baseNorm stepNorm)
    | _ => throw "ind-Nat target must be a natural number"
| Expr.Equal ty left right => do
    let tyVal ← eval ty
    let leftVal ← eval left
    let rightVal ← eval right
    return Value.VEq tyVal leftVal rightVal
| Expr.Refl => return Value.VRefl
| Expr.Replace tgt mot base => do
    let tgtVal ← eval tgt
    let motVal ← eval mot
    let baseVal ← eval base
    match tgtVal with
    | Value.VRefl => return baseVal
    | Value.VNeutral ty neu =>
        let motNorm := Normal.mk Value.VU motVal
        let baseNorm := Normal.mk Value.VU baseVal
        return Value.VNeutral ty (Neutral.NReplace neu motNorm baseNorm)
    | _ => throw "replace target must be an equality proof"
| Expr.Unit => return Value.VUnit
| Expr.sole => return Value.VSole
| Expr.Empty => return Value.VAbsurd
| Expr.Absurd tgt mot => do
    let tgtVal ← eval tgt
    let motVal ← eval mot
    match tgtVal with
    | Value.VNeutral ty neu =>
        let motNorm := Normal.mk Value.VU motVal
        return Value.VNeutral ty (Neutral.NIndAbsurd neu motNorm)
    | _ => throw "absurd target must be absurd"
| Expr.U => return Value.VU
| Expr.The _ e => eval e

partial
def evalClosure [Monad m] [MonadReader Env m] [MonadWithReader Env m] [MonadExcept ErrMsg m]: Closure -> Value -> m Value
| closure, arg =>
    let newEnv := (closure.name, arg) :: closure.env
    withReader (fun _ => newEnv) (eval closure.body)

-- Helper function for ind-Nat recursion
partial
def evalIndNat [Monad m] [MonadReader Env m] [MonadWithReader Env m] [MonadExcept ErrMsg m]:
    Value -> Value -> Value -> Value -> m Value
| Value.VZero, _, base, _ => return base
| Value.VSucc n, motive, base, step => do
    let ihVal ← evalIndNat n motive base step
    let stepApp1 ← doApply step n
    doApply stepApp1 ihVal
| Value.VNeutral ty neu, motive, base, step =>
    let motiveNorm := Normal.mk Value.VU motive
    let baseNorm := Normal.mk Value.VU base
    let stepNorm := Normal.mk Value.VU step
    return Value.VNeutral ty (Neutral.NIndNat neu motiveNorm baseNorm stepNorm)
| _, _, _, _ => throw "evalIndNat: invalid natural number"

-- Helper function for application
partial
def doApply [Monad m] [MonadReader Env m] [MonadWithReader Env m] [MonadExcept ErrMsg m]:
    Value -> Value -> m Value
| Value.VLambda closure, arg => evalClosure closure arg
| Value.VNeutral ty neu, arg =>
    let argNorm := Normal.mk ty arg
    return Value.VNeutral ty (Neutral.NApp neu argNorm)
| _, _ => throw "doApply: not a function"

end



mutual
-- Read Back a normal form back to an expression
-- It's expected that `m:= ExceptM`
partial def readBackNormal [Monad m] [MonadExcept ErrMsg m]: Ctx → Normal → m Expr
| ctx, norm => readBackTyped ctx norm.ty norm.val

-- Read back a neutral form back to an expression
-- It's expected that `m:= ExceptM`
partial def readBackNeutral [Monad m] [MonadExcept ErrMsg m]: Ctx -> Neutral -> m Expr
| _ctx, Neutral.NVar x => return Expr.Var x
| ctx, Neutral.NApp neu arg => do
  let neuExpr ← readBackNeutral ctx neu
  let argExpr ← readBackNormal ctx arg
  return Expr.App neuExpr argExpr
| ctx, Neutral.NIndNat target motive base step => do
  let targetExpr ← readBackNeutral ctx target
  let motiveExpr ← readBackNormal ctx motive
  let baseExpr ← readBackNormal ctx base
  let stepExpr ← readBackNormal ctx step
  return Expr.IndNat targetExpr motiveExpr baseExpr stepExpr
| ctx, Neutral.NReplace target motive base => do
  let targetExpr ← readBackNeutral ctx target
  let motiveExpr ← readBackNormal ctx motive
  let baseExpr ← readBackNormal ctx base
  return Expr.Replace targetExpr motiveExpr baseExpr
| ctx, Neutral.NIndAbsurd target motive => do
  let targetExpr ← readBackNeutral ctx target
  let motiveExpr ← readBackNormal ctx motive
  return Expr.Absurd targetExpr motiveExpr

-- To Ask about adding effect Call!!!
-- Read back a value given its type back to an expression
-- It's expected that `m:= ExceptM`
partial def readBackTyped [Monad m] [MonadExcept ErrMsg m] : Ctx → (ty: Value) → Value → m Expr
| _, Value.VU, Value.VU => return Expr.U
| _, Value.VU, Value.VNatural => return Expr.Natural
| _, Value.VU, Value.VUnit => return Expr.Unit
| _, Value.VU, Value.VAbsurd => return Expr.Empty
| ctx, Value.VU, Value.VPi a closure => do
  let aExpr ← readBackTyped ctx Value.VU a
  let used := ctxNames ctx
  let x := freshen used closure.name
  let xVal := Value.VNeutral a (Neutral.NVar x)
  let env := mkEnv ctx
  let bVal ← match ReaderT.run (evalClosure closure xVal) env with
    | Except.ok v => pure v
    | Except.error e => throw e
  let ctx' := extendCtx ctx x (CtxEntry.IsOf a)
  let bExpr ← readBackTyped ctx' Value.VU bVal
  return Expr.Pi x aExpr bExpr
| ctx, Value.VU, Value.VSigma a closure => do
  let aExpr ← readBackTyped ctx Value.VU a
  let used := ctxNames ctx
  let x := freshen used closure.name
  let xVal := Value.VNeutral a (Neutral.NVar x)
  let env := mkEnv ctx
  let dVal ← match ReaderT.run (evalClosure closure xVal) env with
    | Except.ok v => pure v
    | Except.error e => throw e
  let ctx' := extendCtx ctx x (CtxEntry.IsOf a)
  let dExpr ← readBackTyped ctx' Value.VU dVal
  return Expr.Sigma x aExpr dExpr
| ctx, Value.VU, Value.VEq ty left right => do
  let tyExpr ← readBackTyped ctx Value.VU ty
  let leftExpr ← readBackTyped ctx ty left
  let rightExpr ← readBackTyped ctx ty right
  return Expr.Equal tyExpr leftExpr rightExpr
| ctx, Value.VPi a closure, Value.VLambda bodyClosure => do
  let used := ctxNames ctx
  let x := freshen used bodyClosure.name
  let xVal := Value.VNeutral a (Neutral.NVar x)
  let env := mkEnv ctx
  let bodyVal ← match ReaderT.run (evalClosure bodyClosure xVal) env with
    | Except.ok v => pure v
    | Except.error e => throw e
  let bVal ← match ReaderT.run (evalClosure closure xVal) env with
    | Except.ok v => pure v
    | Except.error e => throw e
  let ctx' := extendCtx ctx x (CtxEntry.IsOf a)
  let bodyExpr ← readBackTyped ctx' bVal bodyVal
  return Expr.Lambda x bodyExpr
| _, Value.VNatural, Value.VZero => return Expr.Zero
| ctx, Value.VNatural, Value.VSucc n => do
  let nExpr ← readBackTyped ctx Value.VNatural n
  return Expr.Succ nExpr
| _ctx, Value.VUnit, Value.VSole => return Expr.sole
| _ctx, Value.VEq _ _ _, Value.VRefl => return Expr.Refl
| ctx, _ty, Value.VNeutral _ neu => readBackNeutral ctx neu
| _ctx, _, _ => throw "readBackTyped: type mismatch or unsupported value"

end

-- Read back a value to an expression without type information
-- This is a simpler version that doesn't require the type
partial def readBackValue [Monad m] [MonadExcept ErrMsg m] : Ctx → Value → m Expr
| _, Value.VU => return Expr.U
| _, Value.VNatural => return Expr.Natural
| _, Value.VZero => return Expr.Zero
| ctx, Value.VSucc n => do
  let nExpr ← readBackValue ctx n
  return Expr.Succ nExpr
| _, Value.VUnit => return Expr.Unit
| _, Value.VSole => return Expr.sole
| _, Value.VAbsurd => return Expr.Empty
| _, Value.VRefl => return Expr.Refl
| ctx, Value.VPi a closure => do
  let aExpr ← readBackValue ctx a
  let used := ctxNames ctx
  let x := freshen used closure.name
  let xVal := Value.VNeutral a (Neutral.NVar x)
  let env := mkEnv ctx
  let bVal ← match ReaderT.run (evalClosure closure xVal) env with
    | Except.ok v => pure v
    | Except.error e => throw e
  let ctx' := extendCtx ctx x (CtxEntry.IsOf a)
  let bExpr ← readBackValue ctx' bVal
  return Expr.Pi x aExpr bExpr
| ctx, Value.VLambda closure => do
  let used := ctxNames ctx
  let x := freshen used closure.name
  -- We don't know the domain type, so create a placeholder
  let xVal := Value.VNeutral Value.VU (Neutral.NVar x)
  let env := mkEnv ctx
  let bodyVal ← match ReaderT.run (evalClosure closure xVal) env with
    | Except.ok v => pure v
    | Except.error e => throw e
  let ctx' := extendCtx ctx x (CtxEntry.IsOf Value.VU)
  let bodyExpr ← readBackValue ctx' bodyVal
  return Expr.Lambda x bodyExpr
| ctx, Value.VSigma a closure => do
  let aExpr ← readBackValue ctx a
  let used := ctxNames ctx
  let x := freshen used closure.name
  let xVal := Value.VNeutral a (Neutral.NVar x)
  let env := mkEnv ctx
  let dVal ← match ReaderT.run (evalClosure closure xVal) env with
    | Except.ok v => pure v
    | Except.error e => throw e
  let ctx' := extendCtx ctx x (CtxEntry.IsOf a)
  let dExpr ← readBackValue ctx' dVal
  return Expr.Sigma x aExpr dExpr
| ctx, Value.VEq ty left right => do
  let tyExpr ← readBackValue ctx ty
  let leftExpr ← readBackValue ctx left
  let rightExpr ← readBackValue ctx right
  return Expr.Equal tyExpr leftExpr rightExpr
| ctx, Value.VNeutral _ neu => readBackNeutral ctx neu


mutual -- Bi-directional Type Checking

/-- Type Synthesis: Infer the type of an expression -/
partial def synth [Monad m] [MonadReader Ctx m] [MonadWithReader Ctx m] [MonadExceptOf ErrMsg m]: Expr -> m Value
-- Rule: Universe (Synthesis)
-- ─────────────
-- Γ ⊢ U ⇒ U
| Expr.U => return Value.VU

-- Rule: Variable (Synthesis)
-- (x : A) ∈ Γ
-- ─────────────
-- Γ ⊢ x ⇒ A
| Expr.Var x => lookupType x

-- Rule: Π-Formation (Synthesis)
-- Γ ⊢ A ⇐ U    Γ, x : A ⊢ B ⇐ U
-- ──────────────────────────────
-- Γ ⊢ Π(x : A) → B ⇒ U
| Expr.Pi x a b => do
  check a Value.VU
  let ctx ← read
  let aVal ← eval (m := ReaderT Env (ExceptT ErrMsg Id)) a |>.run (mkEnv ctx) |> liftExcept
  withReader (extendCtx · x (CtxEntry.IsOf aVal)) do
    check b Value.VU
  return Value.VU

-- Rule: Σ-Formation (Synthesis)
-- Γ ⊢ A ⇐ U    Γ, x : A ⊢ D ⇐ U
-- ──────────────────────────────
-- Γ ⊢ Σ(x : A) × D ⇒ U
| Expr.Sigma x a d => do
  check a Value.VU
  let ctx ← read
  let aVal ← eval (m := ReaderT Env (ExceptT ErrMsg Id)) a |>.run (mkEnv ctx) |> liftExcept
  withReader (extendCtx · x (CtxEntry.IsOf aVal)) do
    check d Value.VU
  return Value.VU

-- Rule: Application (Synthesis)
-- Γ ⊢ f ⇒ Π(x : A) → B    Γ ⊢ arg ⇐ A
-- ─────────────────────────────────────
-- Γ ⊢ f arg ⇒ B[x := arg]
| Expr.App f arg => do
  let fTy ← synth f
  match fTy with
  | Value.VPi a closure => do
    check arg a
    let ctx ← read
    let argVal ← eval (m := ReaderT Env (ExceptT ErrMsg Id)) arg |>.run (mkEnv ctx) |> liftExcept
    evalClosure (m := ReaderT Env (ExceptT ErrMsg Id)) closure argVal |>.run (mkEnv ctx) |> liftExcept
  | _ => throw "Application requires function type"

-- Rule: Natural Numbers (Synthesis)
-- ───────────────
-- Γ ⊢ ℕ ⇒ U
| Expr.Natural => return Value.VU

-- Rule: Zero (Synthesis)
-- ───────────────
-- Γ ⊢ zero ⇒ ℕ
| Expr.Zero => return Value.VNatural

-- Rule: Successor (Synthesis)
-- Γ ⊢ n ⇐ ℕ
-- ──────────────
-- Γ ⊢ succ n ⇒ ℕ
| Expr.Succ n => do
  check n Value.VNatural
  return Value.VNatural

-- Rule: Natural Number Induction (Synthesis)
-- Γ ⊢ target ⇐ ℕ    Γ ⊢ motive ⇐ Π(n : ℕ) → U
-- Γ ⊢ base ⇐ motive zero    Γ ⊢ step ⇐ Π(k : ℕ) → Π(a : motive k) → motive (succ k)
-- ──────────────────────────────────────────────────────────────────────────
-- Γ ⊢ ind-ℕ target motive base step ⇒ motive target
| Expr.IndNat target motive base step => do
  check target Value.VNatural
  let ctx ← read
  let env := mkEnv ctx

  -- motive : ℕ → U
  let motiveExpectedTy := Value.VPi Value.VNatural ⟨"_", [], Expr.U⟩
  check motive motiveExpectedTy
  let motiveVal ← eval (m := ReaderT Env (ExceptT ErrMsg Id)) motive |>.run env |> liftExcept

  -- base : motive zero
  let baseExpectedTy ← doApply (m := ReaderT Env (ExceptT ErrMsg Id)) motiveVal Value.VZero |>.run env |> liftExcept
  check base baseExpectedTy

  -- step : Π(k : ℕ) → Π(ih : motive k) → motive (succ k)
  -- Build the step type by evaluating motive applications
  let stepExpectedTy := Value.VPi Value.VNatural ⟨"k", env,
    Expr.Pi "ih"
      (Expr.App motive (Expr.Var "k"))
      (Expr.App motive (Expr.Succ (Expr.Var "k")))⟩
  check step stepExpectedTy

  -- Result type: motive target
  let targetVal ← eval (m := ReaderT Env (ExceptT ErrMsg Id)) target |>.run env |> liftExcept
  doApply (m := ReaderT Env (ExceptT ErrMsg Id)) motiveVal targetVal |>.run env |> liftExcept

-- Rule: Equality Type (Synthesis)
-- Γ ⊢ A ⇐ U    Γ ⊢ left ⇐ A    Γ ⊢ right ⇐ A
-- ──────────────────────────────────────────
-- Γ ⊢ (left ≡ right : A) ⇒ U
| Expr.Equal ty left right => do
  check ty Value.VU
  let ctx ← read
  let tyVal ← eval (m := ReaderT Env (ExceptT ErrMsg Id)) ty |>.run (mkEnv ctx) |> liftExcept
  check left tyVal
  check right tyVal
  return Value.VU

-- Rule: Reflexivity (Synthesis)
-- Cannot synthesize without type annotation
| Expr.Refl => throw "Cannot synthesize type for refl; use 'the' annotation"

-- Rule: Replace/J eliminator (Synthesis)
-- Γ ⊢ tgt ⇒ (x ≡ y : A)    Γ ⊢ mot ⇐ A → U    Γ ⊢ base ⇐ mot x
-- ────────────────────────────────────────────────────────────
-- Γ ⊢ replace tgt mot base ⇒ mot y
| Expr.Replace tgt mot base => do
  let tgtTy ← synth tgt
  match tgtTy with
  | Value.VEq ty _left right => do
    let ctx ← read
    let env := mkEnv ctx
    let motExpectedTy := Value.VPi ty ⟨"_", [], Expr.U⟩
    check mot motExpectedTy
    let motVal ← eval (m := ReaderT Env (ExceptT ErrMsg Id)) mot |>.run env |> liftExcept
    let baseExpectedTy ← doApply (m := ReaderT Env (ExceptT ErrMsg Id)) motVal _left |>.run env |> liftExcept
    check base baseExpectedTy
    doApply (m := ReaderT Env (ExceptT ErrMsg Id)) motVal right |>.run env |> liftExcept
  | _ => throw "replace requires equality type"

-- Rule: Unit Type (Synthesis)
-- ───────────────
-- Γ ⊢ ⊤ ⇒ U
| Expr.Unit => return Value.VU

-- Rule: Unit Value (Synthesis)
-- ───────────────
-- Γ ⊢ ⋆ ⇒ ⊤
| Expr.sole => return Value.VUnit

-- Rule: Empty Type (Synthesis)
-- ───────────────
-- Γ ⊢ ⊥ ⇒ U
| Expr.Empty => return Value.VU

-- Rule: Absurd Elimination (Synthesis)
-- Γ ⊢ tgt ⇐ ⊥    Γ ⊢ mot ⇐ U
-- ──────────────────────────
-- Γ ⊢ absurd tgt mot ⇒ mot
| Expr.Absurd tgt mot => do
  check tgt Value.VAbsurd
  check mot Value.VU
  let ctx ← read
  eval (m := ReaderT Env (ExceptT ErrMsg Id)) mot |>.run (mkEnv ctx) |> liftExcept

-- Rule: Type Annotation (Synthesis)
-- Γ ⊢ ty ⇐ U    Γ ⊢ e ⇐ ty
-- ─────────────────────────
-- Γ ⊢ the ty e ⇒ ty
| Expr.The ty e => do
  check ty Value.VU
  let ctx ← read
  let tyVal ← eval (m := ReaderT Env (ExceptT ErrMsg Id)) ty |>.run (mkEnv ctx) |> liftExcept
  check e tyVal
  return tyVal

-- Lambda and Let need type annotations (cannot synthesize)
| Expr.Lambda _ _ => throw "Cannot synthesize type for lambda; use 'the' annotation"
| Expr.Let _ _ _ => throw "Cannot synthesize type for let; use 'the' annotation"

/-- Type Checking: Verify an expression has the expected type -/
partial def check [Monad m] [MonadReader Ctx m] [MonadWithReader Ctx m] [MonadExceptOf ErrMsg m]: Expr -> Value -> m Unit
-- Rule: Lambda Introduction (Checking)
-- Γ, x : A ⊢ body ⇐ B
-- ─────────────────────────────────
-- Γ ⊢ λx. body ⇐ Π(x : A) → B
| Expr.Lambda x body, Value.VPi a closure => do
  let ctx ← read
  let env := mkEnv ctx
  let xVal := Value.VNeutral a (Neutral.NVar x)
  let bVal ← evalClosure (m := ReaderT Env (ExceptT ErrMsg Id)) closure xVal |>.run env |> liftExcept
  withReader (extendCtx · x (CtxEntry.IsOf a)) do
    check body bVal

-- Rule: Let Expression (Checking)
-- Γ ⊢ e ⇒ A    Γ, x : A ⊢ body ⇐ B
-- ─────────────────────────────────
-- Γ ⊢ (let x := e in body) ⇐ B
| Expr.Let x e body, expectedTy => do
  let eTy ← synth e
  let ctx ← read
  let eVal ← eval (m := ReaderT Env (ExceptT ErrMsg Id)) e |>.run (mkEnv ctx) |> liftExcept
  withReader (extendCtx · x (CtxEntry.valOfTy eVal eTy)) do
    check body expectedTy

-- Rule: Reflexivity (Checking)
-- Γ ⊢ A ⇐ U    x : A
-- ──────────────────────────────
-- Γ ⊢ refl ⇐ (x ≡ x : A)
| Expr.Refl, Value.VEq _ left right => do
  let ctx ← read
  let leftExpr ← readBackValue ctx left |> liftExcept
  let rightExpr ← readBackValue ctx right |> liftExcept
  unless αEquiv leftExpr rightExpr do
    throw "refl requires equal terms"

-- Rule: Conversion (Checking)
-- Γ ⊢ e ⇒ A    A ≡ B
-- ──────────────────
-- Γ ⊢ e ⇐ B
| e, expectedTy => do
  let inferredTy ← synth e
  let ctx ← read
  let env := mkEnv ctx
  -- Normalize both types before comparing
  let inferredNorm ← eval (m := ReaderT Env (ExceptT ErrMsg Id)) (← readBackValue ctx inferredTy |> liftExcept) |>.run env |> liftExcept
  let expectedNorm ← eval (m := ReaderT Env (ExceptT ErrMsg Id)) (← readBackValue ctx expectedTy |> liftExcept) |>.run env |> liftExcept
  let inferredExpr ← readBackValue ctx inferredNorm |> liftExcept
  let expectedExpr ← readBackValue ctx expectedNorm |> liftExcept
  unless αEquiv inferredExpr expectedExpr do
    throw s!"Type mismatch: expected {Expr.toFormatPrec expectedExpr 0}, but got {Expr.toFormatPrec inferredExpr 0}"


end
