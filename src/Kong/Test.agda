module Kong.Test where

open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Data.Nat.Properties using (+-comm)
open import Relation.Binary.PropositionalEquality using (_≡_ ; cong ; module ≡-Reasoning)
open import Tactic.Cong using (cong!)

open import Kong.Tactic using (kong)

open ≡-Reasoning

-- without kong :'(

proof′ : ∀ a b c d e f → (a + b) + (c + d) + (e + f) ≡ (a + b) + (d + c) + (e + f)
proof′ a b c d e f =
  begin
    (a + b) + (c + d) + (e + f) ≡⟨ cong (λ # → (a + b) + # + (e + f)) (+-comm c d) ⟩
    (a + b) + (d + c) + (e + f) ∎

-- with kong :-)

proof : ∀ a b c d e f → (a + b) + (c + d) + (e + f) ≡ (a + b) + (d + c) + (e + f)
proof a b c d e f =
  begin
    (a + b) + (c + d) + (e + f) ≡⟨ kong (+-comm c d) ⟩
    (a + b) + (d + c) + (e + f) ∎
