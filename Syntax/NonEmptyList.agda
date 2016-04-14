module NonEmptyList where

infixr 5 _∷_

open import Data.Nat
open import Data.Fin

data NList (A : Set) : Set where
  [_] : A → NList A
  _∷_ : A → NList A → NList A

map : {A B : Set} → (f : A → B) → NList A → NList B
map f [ x ] = [ f x ]
map f (x ∷ l) = f x ∷ map f l

length : ∀ {A} → NList A → ℕ
length [ _ ] = 1
length (_ ∷ l) = suc (length l)

Pos : {A : Set} → NList A → Set
Pos l = Fin (length l)
