module plfa.part1.TestNatural where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; step-≡-∣; _∎)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ


{-# BUILTIN NATURAL ℕ #-}


seven = 7

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)


_ : seven ≡ 7
_ = refl


_ : 1 + 2 ≡ 3 + 0
_ = refl


_ : 1 + 2 ≡ 3 + 0
_ =
  begin
    1 + 2
  ≡⟨⟩
    (suc 0) + (suc 1)
  ≡⟨⟩
    suc (0 + (suc 1))
  ≡⟨⟩
    suc (suc 1)
  ≡⟨⟩
    suc 2
  ≡⟨⟩
    3
  ∎


_++_ : ℕ → ℕ → ℕ
zero ++ n = n
suc m ++ n = suc (m ++ n)


