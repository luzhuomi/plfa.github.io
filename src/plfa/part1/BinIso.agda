module plfa.part1.BinIso where


import Relation.Binary.PropositionalEquality as Eq

import Data.Nat as Nat
import plfa.part1.Induction as Induction
import plfa.part1.Relations as Relations
import plfa.part1.Isomorphism as Isomorphism
import plfa.part1.Quantifiers as Quantifiers

open Nat using ( ℕ )
open Eq using (_≡_)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open Induction using (Bin; from; to)
open Relations using (One; Can)
open Isomorphism using ( _≃_ ; extensionality ; ∀-extensionality )
open Quantifiers using (∃ ; ∃-syntax ; Σ ; Σ-syntax )
open Σ using ( proj₁ ; proj₂ )

postulate
  ≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
  ≡Can : ∀ {b : Bin} (c c′ : Can b) → c ≡ c′
  proj₁≡→Can≡ : {c c′ : ∃[ b ] Can b} → proj₁ c ≡ proj₁ c′ → c ≡ c′


ℕ≂∃Canb-from∘to : ∀ { n : ℕ} { b : Bin}
                → ( (λ { Quantifiers.⟨ b , canb ⟩ → Induction.from b })
                    Quantifiers.⟨ Induction.to n , Relations.to-nat-is-can n ⟩ )
                  ≡ n
ℕ≂∃Canb-from∘to {n} {b} =
  begin
    ( (λ { Quantifiers.⟨ b , canb ⟩ → Induction.from b }) Quantifiers.⟨ Induction.to n , Relations.to-nat-is-can n ⟩)
  ≡⟨⟩
    Induction.from (Induction.to n)
  ≡⟨ Induction.bin-law-3 n ⟩
    n
  ∎

ℕ≂∃Canb : ℕ ≃ (∃[ b ] Can b)
ℕ≂∃Canb = record
  { to = λ n → Quantifiers.⟨ Induction.to n , Relations.to-nat-is-can n ⟩
  ; from = λ { Quantifiers.⟨ b , canb ⟩ →  Induction.from b } 
  ; from∘to = λ { n →  {!!} }
  ; to∘from = λ { Quantifiers.⟨ b , canb ⟩ → {! !} } }
