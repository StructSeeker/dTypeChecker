# A Type Checker for Dependent Intensional Type Theory 
## Introduction
A toy implementation of a dependent type checker for intensional type theory with Π-types, Σ-types, and only-one universes, based on normalization by evaluation (NbE) and bidirectional type checking. After finishing the first three chapters of _Principles of Dependent Type Theory_, i implement this following the pattern of _Checking Dependent Types with Normalization by Evaluation: A Tutorial_ both as a lean programming exercise and to solidify with dependent type theory.

## Structure

All the code for the syntax, type checker are in `DTypeChecker/Basic.lean`. The three files (i.e. `EvalTest.lean`, `ExprTest.lean` and `DTypeChecker.lean`) contain some test cases.

## Reflections

The journey is quite messy, but it's better to fail fast than stalling.

Hit some Lean4 infrastructure gaps that surprised me. Expected `MonadExcept ε (ReaderT ρ m)` to exist but had to roll my own instances. I don't know it's by-design or simple omission. In the hindsight, maybe without mtl-style monad class would result in cleaner code. Ended up writing more boilerplate than expected just to thread a typing context through.

Type theory, like any theory and field, feels a a rabbit hole, knowing new thing only makes oneself feel ignorant. Also i am not very confident that my messy conversion checking is correct without testing more corner cases. Mine and tutorial implementation uses separate `Value`, `Normal`, and `Neutral` types, but this feels wasteful—should probably use a single `Expr` with propositions asserting well-formedness via dependent types. Performance doesn't matter for a toy, but the conceptual overhead does. Also, `U : U` is a known inconsistency I'm carrying around; moving to a universe hierarchy seems necessary but adds complexity I don't understand yet.

I suppose formally-verifiy a type checker would not be small work. Proving NbE's termination likely requires logical relations and newman theorem for abstract rewriting. There are also some issues important for practical proof assistant: right now bidirectional checking returns exception or unit, but modern proof assistant produce unification constraints for meta-variables. And also i need to implement elaboration.

Another thing i need to dig into is the gap between closure in implementation and substution in theory, it seems to be called typed closure conversion.
