module Kong.Tactic where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Unit using (⊤ ; tt)
open import Function using (_$_ ; _∘_ ; case_of_)
open import Reflection as R using (_>>_ ; _>>=_ ; return)
open import Reflection.AST.Name using () renaming (_≟_ to _≟ⁿ_)
open import Reflection.AST.Term using () renaming (_≟_ to _≟ᵗ_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; cong)
open import Relation.Nullary using (yes ; no)

private
  leftHandSide : R.Term → R.TC R.Term
  leftHandSide rule =
    case rule of λ where
      (R.def name args) →
        case name ≟ⁿ quote _≡_ of λ where
          (yes _) → firstVisible args
          (no  _) → invalid
      _ → invalid
    where
    invalid : R.TC R.Term
    invalid = R.typeError $ R.strErr "bad rule: " ∷ R.termErr rule ∷ []

    firstVisible : List (R.Arg R.Term) → R.TC R.Term
    firstVisible []                                      = invalid
    firstVisible (R.arg (R.arg-info R.visible _) t ∷ _ ) = return t
    firstVisible (_                                ∷ as) = firstVisible as

  markTargets : ℕ → R.Term → R.Term → R.TC R.Term
  markTargets zero    _   _   = R.typeError $ R.strErr "out of fuel" ∷ []
  markTargets (suc n) sub lhs =
    case sub ≟ᵗ lhs of λ where
      (yes _) → return $ R.var 0 []
      (no  _) →
        case sub of λ where
          (R.var x as)  → processArgs as >>= return ∘ R.var (suc x)
          (R.con c as)  → processArgs as >>= return ∘ R.con c
          (R.def f as)  → processArgs as >>= return ∘ R.def f
          (R.lit l)     → return $ R.lit l
          (R.meta x as) → processArgs as >>= return ∘ R.meta x
          _             → R.typeError $ R.strErr "bad subterm in goal: " ∷ R.termErr sub ∷ []
    where
    recurse : List (R.Arg R.Term) → List (R.Arg (R.TC R.Term))
    recurse = map λ { (R.arg i t) → R.arg i (markTargets n t lhs) }

    insideOut : List (R.Arg (R.TC R.Term)) → R.TC (List (R.Arg R.Term))
    insideOut []               = return []
    insideOut (R.arg i t ∷ as) = do
      t′  ← t
      as′ ← insideOut as
      return $ R.arg i t′ ∷ as′

    processArgs : List (R.Arg R.Term) → R.TC (List (R.Arg R.Term))
    processArgs = insideOut ∘ recurse

macro
  kong : R.Term → R.Term → R.TC ⊤
  kong proof hole = do
    rule     ← R.inferType proof
    goal     ← R.inferType hole
    ruleLhs  ← leftHandSide rule
    goalLhs  ← leftHandSide goal
    ruleLhs′ ← R.normalise ruleLhs
    goalLhs′ ← R.normalise goalLhs
    marked   ← markTargets 1000 goalLhs′ ruleLhs′
    lambda   ← return $ R.lam R.visible (R.abs "#" marked)
    result   ← return $ R.def (quote cong) $ makeArg lambda ∷ makeArg proof ∷ []
    R.unify hole result
    where
    makeArg : R.Term → R.Arg R.Term
    makeArg = R.arg $ R.arg-info R.visible $ R.modality R.relevant R.quantity-ω
