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
open Quantifiers using (∃ ; ∃-syntax ; Σ ; Σ-syntax ; ⟨_,_⟩ )
open Σ using ( proj₁ ; proj₂ )
open Bin using ( ⟨⟩ ; _I ; _O )
open One using (One-i; One-bi; One-bo)
open Can using (Can-⟨⟩ ; Can-One )

-- postulate
  -- ≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
  -- ≡Can : ∀ {b : Bin} (c c′ : Can b) → c ≡ c′
  -- proj₁≡→Can≡ : {c c′ : ∃[ b ] Can b} → (proj₁ c ≡ proj₁ c′) → (c ≡ c′)




≡One : ∀ {b : Bin} (o o′ : One b) → o ≡ o′
≡One {⟨⟩ I} One-i One-i = Eq.refl
≡One {b I} (One-bi one-b) (One-bi one-b') = Eq.cong One-bi (≡One {b} one-b one-b')
≡One {b O} (One-bo one-b) (One-bo one-b') = Eq.cong One-bo (≡One {b} one-b one-b')

≡Can : ∀ {b : Bin} (c c′ : Can b) → c ≡ c′
≡Can {⟨⟩} Can-⟨⟩ Can-⟨⟩ = Eq.refl
≡Can {b} (Can-One o) (Can-One o') = Eq.cong Can-One (≡One {b} o o')



∃≡ : ∀ { A : Set } { B : A → Set } { x y : A }
   → x ≡ y
   → B x ≡ B y
   --  → ( ∃[ x ] B x ) ≡ ( ∃[ y ] B y  )
   → ( (⟨ x , B x ⟩) ≡ (Quantifiers.⟨ y , B y ⟩  ))
∃≡ = λ x₁ x₂ → Eq.refl

proj₁≡→Can≡ : {c c′ : ∃[ b ] Can b} → (proj₁ c ≡ proj₁ c′) → (c ≡ c′)
proj₁≡→Can≡ { Quantifiers.⟨ b , canb ⟩ } { Quantifiers.⟨ b' , canb' ⟩ } b≡b' = --  ∃≡ b≡b' ?
  ∃≡ b≡b' ( ≡Can canb canb')

ℕ≂∃Canb : ℕ ≃ (∃[ b ] Can b)
ℕ≂∃Canb = record
  { to = λ n → Quantifiers.⟨ Induction.to n , Relations.to-nat-is-can n ⟩
  ; from = λ { Quantifiers.⟨ b , canb ⟩ →  Induction.from b } 
  ; from∘to = λ { n →  Induction.bin-law-3 n }
  ; to∘from = λ { Quantifiers.⟨ b , canb ⟩ →  proj₁≡→Can≡ (Relations.can-b→to-from-biject b canb)  } }
