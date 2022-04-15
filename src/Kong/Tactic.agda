module Kong.Tactic where

open import Data.Bool using (Bool ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc ; _<ᵇ_)
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Unit using (⊤ ; tt)
open import Function using (_∘_ ; case_of_)
open import Reflection.AST.AlphaEquality using (_=α=_)
open import Reflection.AST.DeBruijn using (weaken)
open import Reflection.AST.Show using (showTerm)
open import Reflection.TCM.Syntax using (pure ; _>>=_ ; _>>_ ; _<$>_ ; _<*>_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; cong)

import Reflection as R

private
  pattern visArg m x     = R.arg (R.arg-info R.visible m) x
  pattern irrInstArg q x = R.arg (R.arg-info R.instance′ (R.modality R.irrelevant q)) x

  leftHandSide : R.Term → R.TC R.Term
  leftHandSide rule =
    case rule of λ where
      (R.def (quote _≡_) args) → firstVisible args
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
      (R.lam v t)   → R.lam v  <$> stripAbs t
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

    stripAbs : R.Abs R.Term → R.TC (R.Abs R.Term)
    stripAbs (R.abs s x) = R.abs s <$> stripIrrelevant x

  markTargets : ℕ → R.Term → R.Term → R.TC R.Term
  markTargets off sub lhs = do
    sub′ ← stripIrrelevant sub
    case sub′ =α= lhs of λ where
      true → pure (R.var off [])
      false →
        case sub of λ where
          (R.var x as)  → R.var (fixIndex x) <$> markArgs as
          (R.con c as)  → R.con c            <$> markArgs as
          (R.def f as)  → R.def f            <$> markArgs as
          (R.lam v t)   → R.lam v            <$> markAbs t
          (R.meta x as) → R.meta x           <$> markArgs as
          (R.lit l)     → pure (R.lit l)
          (R.unknown)   → pure (R.unknown)
          _             → invalid
    where
    invalid : R.TC R.Term
    invalid = R.typeError (R.strErr "bad subterm in goal: " ∷ R.termErr sub ∷ [])

    fixIndex : ℕ → ℕ
    fixIndex x =
      case x <ᵇ off of λ where
        true → x
        false → suc x

    markArgs : List (R.Arg R.Term) → R.TC (List (R.Arg R.Term))
    markArgs []               = pure []
    markArgs (R.arg i x ∷ as) = (_∷_ ∘ R.arg i) <$> markTargets off x lhs <*> markArgs as

    markAbs : R.Abs R.Term → R.TC (R.Abs R.Term)
    markAbs (R.abs s x) = R.abs s <$> markTargets (suc off) x (weaken 1 lhs)

macro
  kong : R.Term → R.Term → R.TC ⊤
  kong proof hole = do
    rule     ← R.inferType proof
    goal     ← R.inferType hole
    ruleLhs₀ ← leftHandSide rule
    goalLhs₀ ← leftHandSide goal
    ruleLhs₁ ← R.normalise ruleLhs₀
    goalLhs₁ ← R.normalise goalLhs₀
    R.debugPrint "kong" 5 (R.strErr "goalLhs₁ = " ∷ R.termErr goalLhs₁ ∷ [])
    ruleLhs₂ ← stripIrrelevant ruleLhs₁
    R.debugPrint "kong" 5 (R.strErr "ruleLhs₂ = " ∷ R.termErr ruleLhs₂ ∷ [])
    marked   ← markTargets 0 goalLhs₁ ruleLhs₂
    lambda   ← pure (R.lam R.visible (R.abs "#" marked))
    R.debugPrint "kong" 5 (R.strErr "lambda = " ∷ R.termErr lambda ∷ [])
    result   ← pure (R.def (quote cong) (makeArg lambda ∷ makeArg proof ∷ []))
    R.unify hole result
    where
    makeArg : R.Term → R.Arg R.Term
    makeArg = R.arg (R.arg-info R.visible (R.modality R.relevant R.quantity-ω))
