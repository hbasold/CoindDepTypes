{- # --without-K # -}

open import Level
open import Data.Unit
open import Data.Empty
open import Data.Nat as Nat hiding (pred)
open import Data.Fin hiding (pred; _<_)
open import Data.Sum as Sum
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary

{-
open import Data.Nat.Properties
open DecTotalOrder Nat.decTotalOrder using () renaming (refl to ≤-refl)
-}

rec-≡ : ∀ {A : Set} {C : A → A → Set} →
        (f : (s : A) → C s s) → (s t : A) → s ≡ t → C s t
rec-≡ f s .s refl = f s

record EN : Set where
  coinductive
  field pred : ⊤ ⊎ EN
open EN

corec-EN : ∀ {C : Set} → (C → ⊤ ⊎ C) → C → EN
pred (corec-EN f x) with f x
pred (corec-EN f x) | inj₁ tt = inj₁ tt
pred (corec-EN f x) | inj₂ y  = inj₂ (corec-EN f y)

prim-corec-EN : ∀ {C : Set} → (C → (⊤ ⊎ C) ⊎ EN) → (C → EN)
pred (prim-corec-EN f x) with f x
pred (prim-corec-EN f x) | inj₁ (inj₁ tt) = inj₁ tt
pred (prim-corec-EN f x) | inj₁ (inj₂ y)  = inj₂ (prim-corec-EN f y)
pred (prim-corec-EN f x) | inj₂ y         = pred y

~EN-data : ⊤ ⊎ EN → ⊤ ⊎ EN → Set

record _~EN_ (m n : EN) : Set where
  coinductive
  field pred~ : ~EN-data (pred m) (pred n)
open _~EN_

~EN-data (inj₁ tt) (inj₁ tt) = ⊤
~EN-data (inj₁ tt) (inj₂ m)  = ⊥
~EN-data (inj₂ n)  (inj₁ tt) = ⊥
~EN-data (inj₂ n)  (inj₂ m)  = n ~EN m

EN-Pred : (ℓ : Level) → Set (Level.suc ℓ)
EN-Pred ℓ = Σ (Pred EN ℓ) λ P → ∀ n m → n ~EN m → P n → P m

0∞ : EN
0∞ = corec-EN inj₁ tt

s∞-inj : EN ⊎ EN → (⊤ ⊎ (EN ⊎ EN)) ⊎ EN
s∞-inj = [ inj₁ ∘ inj₂ ∘ inj₂ , inj₂ ]′

s∞' : EN → EN
s∞' = s∞-aux ∘ inj₁
  where
    s∞-aux : EN ⊎ EN → EN
    s∞-aux = corec-EN [ inj₂ ∘ inj₂ , [ inj₁ , inj₂ ∘ inj₂ ]′ ∘ pred ]′

s∞ : EN → EN
s∞ = s∞-aux ∘ inj₁
  where
    s∞-aux : EN ⊎ EN → EN
    s∞-aux = prim-corec-EN s∞-inj

#∞_ : ℕ → EN
#∞ 0 = 0∞
#∞ (suc n) = s∞ (#∞ n)

inf : EN
inf = corec-EN inj₂ tt

lem : ∀ n → Sum.map id pred (pred (s∞ n)) ≡ inj₂ (pred n)
lem n = refl

lem₂ : ∀ n → ~EN-data (pred (s∞' n)) (inj₂ n)
pred~ (lem₂ n) with pred n
pred~ (lem₂ n) | inj₁ tt = tt
pred~ (lem₂ n) | inj₂ m  = lem₂ m

data ∃ (A : Set) (B : A → Set) : Set where
  in-∃ : (x : A) → B x → ∃ A B

∃-elim : ∀ {A B} {C : Set} → (p : (x : A) → B x → C) → ∃ A B → C
∃-elim p (in-∃ x y) = p x y

_≡s∞[_]  : Rel EN _
n ≡s∞[ k ] = pred n ≡ inj₂ k

is-s∞ : Pred EN _
is-s∞ n = ∃ EN (_≡s∞[_] n)

PStr-step : Set → ⊤ ⊎ EN → Set

record PStr (A : Set) (n : EN) : Set where
  coinductive
  field out-PStr : PStr-step A (pred n)
open PStr

PStr-step A (inj₁ tt) = ⊤
PStr-step A (inj₂ n)  = A × PStr A n

corec-PStr : ∀ {A} {C : EN → Set}
             (fh : (n k : EN) → n ≡s∞[ k ] → C n → A)
             (ft : (n k : EN) → n ≡s∞[ k ] → C n → C k)
             (n : EN) → C n → PStr A n
out-PStr (corec-PStr {A} {C} fh ft n x) = match n (pred n) refl x
  where
    match : (n : EN) → (r : ⊤ ⊎ EN) → pred n ≡ r → C n → PStr-step A r
    match n (inj₁ tt) p x = tt
    match n (inj₂ n') p x =
      (fh n n' p x , corec-PStr fh ft n' (ft n n' p x))

data Fin∞ : EN → Set where
  zero∞ : (n k : EN) → n ≡s∞[ k ] →          Fin∞ n
  suc∞  : (n k : EN) → n ≡s∞[ k ] → Fin∞ k → Fin∞ n

rec-Fin∞ : ∀ {C : EN → Set} →
           (f : (n k : EN) → n ≡s∞[ k ] → C n)
           (g : (n k : EN) → n ≡s∞[ k ] → C k → C n)
           (n : EN) → Fin∞ n → C n
rec-Fin∞ f g n (zero∞ .n k p)   = f n k p
rec-Fin∞ f g n (suc∞  .n k p x) = g n k p (rec-Fin∞ f g k x)

data ≤0 : EN → Set where
  is-zero : (n : EN) → pred n ≡ inj₁ tt → ≤0 n

rec-≤0 : ∀ {C : EN → Set}
            (f : (n : EN) → pred n ≡ inj₁ tt → C n)
            (n : EN) → ≤0 n → C n
rec-≤0 f n (is-zero .n p) = f n p

data ≤1 : EN → Set where
  is-zero' : (n : EN) → ≤0 n → ≤1 n
  is-one : (n n' : EN) → pred n ≡ inj₂ n' → ≤0 n' → ≤1 n

rec-≤1 : ∀ {C : EN → Set}
            (f : (n : EN) → pred n ≡ inj₁ tt → C n)
            (g : (n n' : EN) → pred n ≡ inj₂ n' → ≤0 n' → C n)
            (n : EN) → ≤1 n → C n
rec-≤1 f g n (is-zero' .n (is-zero .n p)) = f n p
rec-≤1 f g n (is-one .n n' p x) = g n n' p x

sum-injective : ∀{A B : Set} → (a : A) (b : B) → ¬ inj₁ a ≡ inj₂ b
sum-injective a b ()

singleton-PStr : ∀{A} → (a : A) → PStr A (#∞ 1)
singleton-PStr {A} a =
  corec-PStr {C = ≤1} h t' (#∞ 1)
             (is-one (#∞ 1) (prim-corec-EN s∞-inj (inj₂ (#∞ 0))) refl
               (is-zero _ refl))
  where
    h : (n k : EN) → n ≡s∞[ k ] → ≤1 n → A
    h n k p = rec-≤1 f g n
      where
        f : (n₁ : EN) → pred n₁ ≡ inj₁ tt → A
        f n₁ x = a

        g : (n₁ n' : EN) → pred n₁ ≡ inj₂ n' → ≤0 n' → A
        g n₁ n' p = rec-≤0 (λ n₂ x → a) n'

    t' : (n k : EN) → n ≡s∞[ k ] → ≤1 n → ≤1 k
    t' n k p q = rec-≤1 u₀ u₁ n q p
      where
        u₀ : (n₁ : EN) → pred n₁ ≡ inj₁ tt → n₁ ≡s∞[ k ] → ≤1 k
        u₀ n₁ r p₁ with pred n
        u₀ n₁ r p₁ | inj₁ tt =
          ⊥-elim (sum-injective tt k (trans (sym r) p₁))
        u₀ n₁ r p₁ | inj₂ y =
          ⊥-elim (sum-injective tt k (trans (sym r) p₁))

        u₁ : (n₁ n' : EN) → pred n₁ ≡ inj₂ n' → ≤0 n' → n₁ ≡s∞[ k ] → ≤1 k
        u₁ n₁ n' r x p₁ with pred n₁
        u₁ n₁ n' r x p₁ | inj₁ tt =
          ⊥-elim (sum-injective tt k p₁)
        u₁ n₁ .k refl x refl | inj₂ .k = is-zero' k x

test₁ : ∀{A} → (a : A) → proj₁ (out-PStr (singleton-PStr a)) ≡ a
test₁ a = refl

test₂ : ∀{A} → (a : A) → out-PStr (proj₂ (out-PStr (singleton-PStr a))) ≡ tt
test₂ a = refl

{-
data isNat : ℕ → EN → Set where
  is-zero : (n : EN) → pred n ≡ inj₁ tt → isNat 0 n
  is-suc  : (k : ℕ) (n n' : EN) → -- pred n ≡ inj₂ n' →
            isNat k n' → isNat (suc k) n

rec-isNat : ∀ {C : ℕ → EN → Set}
            (fz : (n : EN) → pred n ≡ inj₁ tt → C 0 n)
            (fs : (k : ℕ) (n n' : EN) → -- pred n ≡ inj₂ n' →
                  C k n' → C (suc k) n) →
            (k : ℕ) (n : EN) → isNat k n → C k n
rec-isNat fz fs .0 n (is-zero .n p) = fz n p
rec-isNat fz fs .(suc k) n (is-suc k .n n' x) =
  fs k n n' (rec-isNat fz fs k n' x)

fin-map : ∀{A : Set} → ((k : ℕ) (n : EN) → isNat k n → (Fin (suc k) → A) → A)
fin-map {A} = rec-isNat b s
  where
    b : (n : EN) → pred n ≡ inj₁ tt → (Fin (suc 0) → A) → A
    b n p f = f zero

    s : (k : ℕ) (n n' : EN) → -- pred n ≡ inj₂ n' →
        ((Fin (suc k) → A) → A) → (Fin (suc (suc k)) → A) → A
    s k n n' φ f' = φ (f' ∘ suc)

fin-map' : ∀ {A : Set} {k} → (Fin (suc k) → A) → (n : EN) → isNat k n → A
fin-map' f n x = fin-map _ n x f

#∞-isNat : (k : ℕ) → isNat k (#∞ k)
#∞-isNat zero = is-zero (#∞ zero) refl
#∞-isNat (suc k) = is-suc k (#∞ suc k) (#∞ k) (#∞-isNat k)

ext : ∀{A : Set} {k} → A → (Fin k → A) → (Fin (suc k) → A)
ext {k = zero} a f zero = a
ext {k = zero} a f (suc x) = f x
ext {k = suc k} a f zero = f zero
ext {k = suc k} a f (suc x) = ext {k = k} a (f ∘ suc) x

lem₁ : ∀{A : Set} (k : ℕ) (a : A) → (f : Fin k → A) →
       ∀{n} → (p : n < k) → ext a f (fromℕ≤ (≤-step p)) ≡ f (fromℕ≤ p)
lem₁ zero     a f ()
lem₁ (suc k)  a f (s≤s z≤n)     = refl
lem₁ (suc ._) a f (s≤s (s≤s p)) = lem₁ _ a (f ∘ suc) (s≤s p)

lem₂ : ∀{A : Set} (k : ℕ) (a : A) → (f : Fin k → A) →
       ext a f (fromℕ≤ ≤-refl) ≡ a
lem₂ zero    a f = refl
lem₂ (suc k) a f = lem₂ k a (f ∘ suc)

pred-isNat : (k : ℕ) (n m : EN) → n ≡s∞[ m ] → isNat k n → isNat k m
pred-isNat k n m p = rec-isNat {C = C} {!!} {!!} k n
  where
    C : ℕ → EN → Set
    C k' n' with pred n'
    C k' n' | inj₁ tt = isNat k' 0∞
    C k' n' | inj₂ n'' = isNat k' n''

fin-PStr : ∀{A} {k} → A → (Fin k → A) → PStr A (#∞ k)
fin-PStr {A} {k} a f = corec-PStr {C = isNat k} {!!} {!!} (#∞ k) (#∞-isNat k)
  where
    g : (n : EN) → isNat k n → A
    g = fin-map' (ext a f)

    h : (n k₁ : EN) → n ≡s∞[ k₁ ] → isNat k n → A
    h n k₁ p x = g n x

    t : (n k₁ : EN) → n ≡s∞[ k₁ ] → isNat k n → isNat k k₁
    t n k₁ p q = {!!}

      -- rec-≡ {C = λ x x₁ → isNat k k₁} {!!} (pred n) (inj₂ k₁) p
-}

-- Implement Str A → (n : EN) → PStr n and
-- NonEmpty A → (l : List A) → PStr (length l)

{-
foo : ∀ {A : Set} → (s : A) → inj₁ s ≡ inj₂ s → ⊥
foo s = rec-≡ {!!} (inj₁ s) (inj₂ s)

empty : Fin∞ 0∞ → ⊥
empty = rec-Fin∞ {λ n → ⊥} {!!} (λ n k p x → x) 0∞
-}

