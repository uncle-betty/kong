module Kong.Test where

open import Data.Nat using (ℕ ; zero ; suc)
open import Kong using (kong)
open import Relation.Binary.PropositionalEquality using (_≡_ ; cong ; module ≡-Reasoning)

open ≡-Reasoning

postulate foo : ℕ
postulate foo-is-123 : foo ≡ 123

postulate bar : ℕ → ℕ
postulate bar-is-id : ∀ n → bar n ≡ n

-- without kong :'(

proof′ : bar foo ≡ 123
proof′ = begin
  bar foo ≡⟨ cong bar foo-is-123 ⟩
  bar 123 ≡⟨ bar-is-id 123 ⟩
  123     ∎

-- with kong :-)

proof : bar foo ≡ 123
proof = begin
  bar foo ≡⟨ kong foo-is-123 ⟩
  bar 123 ≡⟨ kong (bar-is-id 123) ⟩
  123     ∎
