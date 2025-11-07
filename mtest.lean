-- Lean std doesn't implement this, i don't know is it by design or an omission
instance [MonadExcept ε m] : MonadExcept ε (ReaderT ρ m) where
  throw e := fun _ => throw e
  tryCatch body handler := fun x => tryCatch (body x) (handler · x)


def foo [Monad m] [MonadReader Nat m] [MonadExcept String m]: m Bool := do
  pure ((<- read) > 4)


def bar [Monad m] [MonadExcept String m]: m Bool := do
  let env : Nat := 2
  ReaderT.run (foo (m:= ReaderT Nat m)) env
