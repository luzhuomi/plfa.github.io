module plfa.part1.BinDec where


import Relation.Binary.PropositionalEquality as Eq

import Data.Nat as Nat
import plfa.part1.Induction as Induction
import plfa.part1.Relations as Relations
import plfa.part1.Isomorphism as Isomorphism
import plfa.part1.Quantifiers as Quantifiers
import plfa.part1.Decidable as Decidable 

open Nat using ( ℕ )
open Eq using (_≡_)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open Induction using (Bin; from; to)
open Relations using (One; Can)
open Isomorphism using ( _≃_ ; extensionality ; ∀-extensionality )
open Quantifiers using (∃ ; ∃-syntax ; Σ ; Σ-syntax ; ⟨_,_⟩ )
open Decidable using ( Dec )
open Σ using ( proj₁ ; proj₂ )
open Bin using ( ⟨⟩ ; _I ; _O )
open One using (One-i; One-bi; One-bo)
open Can using (Can-⟨⟩ ; Can-One )
open Dec using ( yes ; no )


One? : ∀ (b : Bin) → Dec (One b)
One? ⟨⟩ = no λ()
One? (b O) with One? b
...           | yes one-b = yes (One-bo one-b)
...           | no ¬one-b = no λ { (One-bo one-b) → ¬one-b one-b}
One? (b I) with b
One? (b I)    | ⟨⟩        = yes One-i
One? (b I)    | b' O  with One? (b' O)
One? (b I)    | b' O     | yes one-bo' = yes (One-bi one-bo')
One? (b I)    | b' O     | no ¬one-bo' = no (λ { (One-bi one-bo') → (¬one-bo' one-bo') })
One? (b I)    | b' I  with One? (b' I)
One? (b I)    | b' I     | yes one-bi' = yes (One-bi one-bi')
One? (b I)    | b' I     | no ¬one-bi' = no (λ { (One-bi one-bi') → (¬one-bi' one-bi') })



Can? : ∀ (b : Bin) → Dec (Can b)
Can? ⟨⟩     = yes Can-⟨⟩
Can? (b O) with One? b
...           | yes one-b = yes (Can-One (One-bo one-b))
...           | no ¬one-b = no ( λ { (Can-One (One-bo one-b)) →  ¬one-b one-b } )
Can? (b I) with b    
Can? (b I)    | ⟨⟩        = yes (Can-One (One-i))
Can? (b I)    | b' O   with One? (b' O)
Can? (b I)    | b' O      | yes one-bo' =  yes (Can-One (One-bi one-bo'))
Can? (b I)    | b' O      | no ¬one-bo' =  no (λ { (Can-One (One-bi one-bo')) → (¬one-bo' one-bo') })
Can? (b I)    | b' I   with One? (b' I)
Can? (b I)    | b' I      | yes one-bi' = yes (Can-One (One-bi one-bi'))
Can? (b I)    | b' I      | no ¬one-bi' = no (λ { (Can-One (One-bi one-bi')) → (¬one-bi' one-bi') })
