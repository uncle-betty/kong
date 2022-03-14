module Kong.Tactic where

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; case_of_)
open import Reflection.AST.Name using () renaming (_≟_ to _≟ⁿ_)
open import Reflection.AST.Term using () renaming (_≟_ to _≟ᵗ_)
open import Reflection.TCM.Syntax using (pure ; _>>=_ ; _<$>_ ; _<*>_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; cong)
open import Relation.Nullary using (yes ; no)

import Reflection as R

private
  pattern visArg m x     = R.arg (R.arg-info R.visible m) x
  pattern irrInstArg q x = R.arg (R.arg-info R.instance′ (R.modality R.irrelevant q)) x

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
    invalid = R.typeError (R.strErr "bad rule: " ∷ R.termErr rule ∷ [])

    firstVisible : List (R.Arg R.Term) → R.TC R.Term
    firstVisible []                = invalid
    firstVisible (visArg _ x ∷ _ ) = pure x
    firstVisible (_          ∷ as) = firstVisible as

  stripIrrelevant : R.Term → R.TC R.Term
  stripIrrelevant sub =
    case sub of λ where
      (R.var x as)  → R.var x  <$> stripArgs as
      (R.con c as)  → R.con c  <$> stripArgs as
      (R.def f as)  → R.def f  <$> stripArgs as
      (R.meta x as) → R.meta x <$> stripArgs as
      (R.lit l)     → pure (R.lit l)
      (R.unknown)   → pure (R.unknown)
      _             → invalid
    where
    invalid : R.TC R.Term
    invalid = R.typeError (R.strErr "bad subterm in goal: " ∷ R.termErr sub ∷ [])

    stripArgs : List (R.Arg R.Term) → R.TC (List (R.Arg R.Term))
    stripArgs []                    = pure []
    stripArgs (irrInstArg q x ∷ as) = stripArgs as
    stripArgs (R.arg i x ∷ as)      = (_∷_ ∘ R.arg i) <$> stripIrrelevant x <*> stripArgs as

  markTargets : R.Term → R.Term → R.TC R.Term
  markTargets sub lhs = do
    sub′ ← stripIrrelevant sub
    case sub′ ≟ᵗ lhs of λ where
      (yes _) → pure (R.var 0 [])
      (no  _) →
        case sub of λ where
          (R.var x as)  → R.var (suc x) <$> markArgs as
          (R.con c as)  → R.con c       <$> markArgs as
          (R.def f as)  → R.def f       <$> markArgs as
          (R.meta x as) → R.meta x      <$> markArgs as
          (R.lit l)     → pure (R.lit l)
          (R.unknown)   → pure (R.unknown)
          _             → invalid
    where
    invalid : R.TC R.Term
    invalid = R.typeError (R.strErr "bad subterm in goal: " ∷ R.termErr sub ∷ [])

    markArgs : List (R.Arg R.Term) → R.TC (List (R.Arg R.Term))
    markArgs []               = pure []
    markArgs (R.arg i x ∷ as) = (_∷_ ∘ R.arg i) <$> markTargets x lhs <*> markArgs as

macro
  kong : R.Term → R.Term → R.TC ⊤
  kong proof hole = do
    rule     ← R.inferType proof
    goal     ← R.inferType hole
    ruleLhs₀ ← leftHandSide rule
    goalLhs₀ ← leftHandSide goal
    ruleLhs₁ ← R.normalise ruleLhs₀
    goalLhs₁ ← R.normalise goalLhs₀
    ruleLhs₂ ← stripIrrelevant ruleLhs₁
    marked   ← markTargets goalLhs₁ ruleLhs₂
    lambda   ← pure (R.lam R.visible (R.abs "#" marked))
    result   ← pure (R.def (quote cong) (makeArg lambda ∷ makeArg proof ∷ []))
    R.unify hole result
    where
    makeArg : R.Term → R.Arg R.Term
    makeArg = R.arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω))
