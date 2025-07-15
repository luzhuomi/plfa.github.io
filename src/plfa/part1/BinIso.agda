module plfa.part1.BinIso where


import Relation.Binary.PropositionalEquality as Eq

import Data.Nat as Nat
import plfa.part1.Induction as Induction
import plfa.part1.Relations as Relations
import plfa.part1.Isomorphism as Isomorphism
import plfa.part1.Quantifiers as Quantifiers

open Nat using ( ℕ )
open Eq using (_≡_)
open Relations using (Bin; One; Can)
open Isomorphism using ( _≃_ ; extensionality ; ∀-extensionality )
open Quantifiers using (∃ ; ∃-syntax ; Σ ; Σ-syntax )
open Σ using ( proj₁ ; proj₂ )

postulate
  ≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
  ≡Can : ∀ {b : Bin} (c c′ : Can b) → c ≡ c′
  proj₁≡→Can≡ : {c c′ : ∃[ b ] Can b} → proj₁ c ≡ proj₁ c′ → c ≡ c′


ℕ≂∃Canb : ℕ ≃ (∃[ b ] Can b)
ℕ≂∃Canb = record
  { to = λ n → Quantifiers.⟨ Relations.to n , Relations.to-nat-is-can n ⟩
  ; from = λ { Quantifiers.⟨ b , canb ⟩ →  Relations.from b }
  ; from∘to = λ { n → {! !} }
  ; to∘from = λ { Quantifiers.⟨ b , canb ⟩ → {! !} } }
