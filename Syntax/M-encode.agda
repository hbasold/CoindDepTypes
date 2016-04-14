{- # --without-K # -}

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Sum as Sum
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Unary
open import Relation.Binary
open import Relation.Binary using (module IsEquivalence; Setoid; module Setoid)
open ≡-Reasoning
import Relation.Binary.HeterogeneousEquality as HE
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

-- | Polynomials
data Poly : Set₁ where
  _▹_ : (A : Set) (B : A → Set) → Poly

-- | Interpretation of polynomials as functor, object part.
⟦_⟧ : Poly → Set → Set
⟦ A ▹ B ⟧ X = Σ[ a ∈ A ] (B a → X)

-- | Interpretation of polynomials as functor, morphism part.
⟦_⟧₁ : (P : Poly) → ∀{X Y} → (X → Y) → (⟦ P ⟧ X → ⟦ P ⟧ Y)
⟦ A ▹ B ⟧₁ f (a , α) = (a , (λ x → f (α x)))

-- | Finite trees over the signature determined by P with one free variable.
data _* (P : Poly) : Set where
  sup : ⟦ P ⟧ (P *) ⊎ ⊤ → P *

-- | Inverse of sup.
sup⁻¹ : ∀{P} → P * → ⟦ P ⟧ (P *) ⊎ ⊤
sup⁻¹ (sup x) = x

_extends_ : ∀{P} → P * → P * → Set
_extends_ {A ▹ B} (sup (inj₁ (a' , β))) (sup (inj₁ (a , α)))
  = Σ[ e ∈ a' ≡ a ] (∀ (b : B a') → (β b) extends α (subst B e b))
sup (inj₂ _) extends sup (inj₁ _) = ⊥
sup (inj₁ x) extends sup (inj₂ _) = ⊤
sup (inj₂ _) extends sup (inj₂ _) = ⊥

PreApprox : Poly → Set
PreApprox P = ℕ → P *

converges : ∀{P} → PreApprox P → Set
converges u = ∀ n → u (1 + n) extends u n

non-empty : ∀{P} → P * → Set
non-empty (sup (inj₁ x)) = ⊤
non-empty (sup (inj₂ _)) = ⊥

root : ∀{A B} → (t : (A ▹ B) *) → non-empty t → A
root (sup (inj₁ x)) p = proj₁ x
root (sup (inj₂ y)) ()

branch : ∀{A B} → (t : (A ▹ B) *) → (p : non-empty t) → B (root t p) → (A ▹ B) *
branch (sup (inj₁ x)) p  b = proj₂ x b
branch (sup (inj₂ y)) () b

_∞ : Poly → Set
P ∞ = Σ[ u ∈ PreApprox P ] (non-empty (u 0) × converges u)

-- | If u₀ is non-empty and u converges, then uₙ is non-empty for every n.
ne₀→all-ne : ∀{P} →
  (u : PreApprox P) → non-empty (u 0) → converges u →
  ∀ n → non-empty (u n)
ne₀→all-ne u ne₀ conv zero = ne₀
ne₀→all-ne {A ▹ B} u ne₀ conv (suc n)
  with u (suc n)   | u n          | conv n
... | sup (inj₁ x) | y            | z       = tt
... | sup (inj₂ x) | sup (inj₁ y) | ()
... | sup (inj₂ x) | sup (inj₂ y) | ()

-- | If t₂ extends t₁ and they are both non-empty, then they have the same
-- root labels.
ext→root≡ : ∀{A B} →
            (t₁ t₂ : (A ▹ B) *)
            (ne₁ : non-empty t₁)
            (ne₂ : non-empty t₂)
            (e : t₂ extends t₁) →
            root t₁ ne₁ ≡ root t₂ ne₂
ext→root≡ (sup (inj₁ (a , α))) (sup (inj₁ (b , β))) ne₁ ne₂ e = sym (proj₁ e)
ext→root≡ (sup (inj₁ x))       (sup (inj₂ tt))      ne₁ ()  e
ext→root≡ (sup (inj₂ tt))      (sup (inj₁ y))       ()  ne₂ e
ext→root≡ (sup (inj₂ tt))      (sup (inj₂ tt))      ne₁ ne₂ ()

-- | The roots of the first two trees in a converging sequence have the same
-- label. This is used as base case in conv→suc-roots≡.
conv→roots-0-1≡ : ∀{A B} →
  (u : PreApprox (A ▹ B))
  (ne : non-empty (u 0))
  (c : converges u) →
  root (u 0) ne ≡ root (u 1) (ne₀→all-ne u ne c 1)
conv→roots-0-1≡ {A} {B} u ne c
  = ext→root≡ (u 0) (u 1) ne (ne₀→all-ne u ne c 1) (c 0)

-- | The roots of two successive trees in a converging sequence have the same
-- label. We use this in the induction step in conv→roots≡.
conv→suc-roots≡ : ∀{A B} →
  (u : PreApprox (A ▹ B))
  (ne : non-empty (u 0))
  (c : converges u) →
  ∀ n → root (u n) (ne₀→all-ne u ne c n)
        ≡ root (u (1 + n)) (ne₀→all-ne u ne c (1 + n))
conv→suc-roots≡ u ne c zero = conv→roots-0-1≡ u ne c
conv→suc-roots≡ u ne c (suc n)
  = ext→root≡ (u (1 + n))
              (u (2 + n))
              (ne₀→all-ne u ne c (1 + n))
              (ne₀→all-ne u ne c (2 + n))
              (c (suc n))

-- | The root of any tree in a converging sequence has the same label as
-- the root of the first tree.
conv→roots≡ : ∀{A B} →
  (u : PreApprox (A ▹ B))
  (ne : non-empty (u 0))
  (c : converges u) →
  ∀ n → root (u 0) ne ≡ root (u n) (ne₀→all-ne u ne c n)
conv→roots≡ u ne c zero = refl
conv→roots≡ u ne c (suc n)
  = trans (conv→roots≡ u ne c n) (conv→suc-roots≡ u ne c n)

-- | All trees in a converging sequence have the same root label.
conv→all-roots≡ : ∀{A B} →
  (u : PreApprox (A ▹ B))
  (ne : non-empty (u 0))
  (c : converges u) →
  ∀ n m → root (u n) (ne₀→all-ne u ne c n) ≡ root (u m) (ne₀→all-ne u ne c m)
conv→all-roots≡ u ne c n m =
  begin
    root (u n) (ne₀→all-ne u ne c n)
  ≡⟨ sym (conv→roots≡ u ne c n) ⟩
    root (u 0) ne
  ≡⟨ conv→roots≡ u ne c m ⟩
    root (u m) (ne₀→all-ne u ne c m)
  ∎

-- | If t₁ is non-empty and t₂ extends t₁, then all branches of t₂ are
-- non-empty. This shows that _extends_ defines a strict order.
conv+ne₀→ne-branch : ∀{A B} →
  (t₁ t₂ : (A ▹ B)*)
  (ne₁ : non-empty t₁)
  (ne₂ : non-empty t₂)
  (e : t₂ extends t₁) →
  ∀ b → non-empty (branch t₂ ne₂ b)
conv+ne₀→ne-branch (sup (inj₁ (a , α))) (sup (inj₁ (.a , β))) ne₁ ne₂ (refl , q) b
  with α b          | β b           | q b
... | sup (inj₁ x)  | sup (inj₁ y)  | z  = tt
... | sup (inj₁ x)  | sup (inj₂ tt) | ()
... | sup (inj₂ tt) | sup (inj₁ y)  | z  = tt
... | sup (inj₂ tt) | sup (inj₂ tt) | ()
conv+ne₀→ne-branch (sup (inj₁ x)) (sup (inj₂ tt)) ne₁ () e b
conv+ne₀→ne-branch (sup (inj₂ tt)) t₂             () ne₂ e b

-- | If t₂ extends t₂, then all branches of t₂ extend the corresponding one
-- of t₁.
conv→branch-conv : ∀{A B} →
  (t₁ t₂ : (A ▹ B)*)
  (ne₁ : non-empty t₁)
  (ne₂ : non-empty t₂)
  (e : t₂ extends t₁) →
  ∀ b b' → b ≅ b' →
  (branch t₂ ne₂ b) extends
  (branch t₁ ne₁ b')
conv→branch-conv (sup (inj₁ (a'' , α)))
                 (sup (inj₁ (.a'' , β))) ne₁ ne₂ (refl , t) b .b refl = t b
conv→branch-conv (sup (inj₁ x)) (sup (inj₂ tt)) ne₁ () e b b' p
conv→branch-conv (sup (inj₂ tt)) (sup y) () ne₂ e b b' p

-- | Technical lemma:
-- The equality proofs for substitution by root equality are the same.
root-conv≡ : ∀ {A B} →
  (u : PreApprox (A ▹ B))
  (ne : non-empty (u 0))
  (c : converges u) →
  ∀ b n → (subst B (conv→roots≡ u ne c (1 + n)) b)
          ≅ (subst B (conv→roots≡ u ne c n) b)
root-conv≡ {A} {B} u ne c b n =
  HE.trans (HE.≡-subst-removable B (conv→roots≡ u ne c (1 + n)) b)
           (HE.sym (HE.≡-subst-removable B (conv→roots≡ u ne c n) b))

-- | Coalgebra structure on P∞.
out : ∀{P} → P ∞ → ⟦ P ⟧ (P ∞)
out {A ▹ B} (u , ne , conv) = (a , α)
  where
    a : A
    a = root (u 0) ne

    u' : B a → PreApprox (A ▹ B)
    u' b n = branch (u (1 + n))
                    (ne₀→all-ne u ne conv (1 + n))
                    (subst B (conv→roots≡ u ne conv (1 + n)) b)

    ne' : (b : B a) → non-empty (u' b 0)
    ne' b =
      conv+ne₀→ne-branch (u 0) (u 1) ne
                            (ne₀→all-ne u ne conv 1)
                            (conv 0)
                            (subst B (conv→roots≡ u ne conv 1) b)

    conv' : (b : B a) → converges (u' b)
    conv' b n = conv→branch-conv (u (1 + n)) (u (2 + n))
                                  (ne₀→all-ne u ne conv (1 + n))
                                  (ne₀→all-ne u ne conv (2 + n))
                                  (conv (1 + n))
                                  (subst B (conv→roots≡ u ne conv (2 + n)) b)
                                  (subst B (conv→roots≡ u ne conv (1 + n)) b)
                                  (root-conv≡ u ne conv b (suc n))

    α : B a → (A ▹ B) ∞
    α b = (u' b , ne' b , conv' b)

-- | Get root label.
root∞ : ∀{A B} → (A ▹ B) ∞ → A
root∞ t = proj₁ (out t)

-- | Get branches below root.
branch∞ : ∀{A B} → (t : (A ▹ B) ∞) → B (root∞ t) → (A ▹ B) ∞
branch∞ t = proj₂ (out t)

-- | Corecursion principle for P∞.
corec : ∀{P} {C : Set} → (C → ⟦ P ⟧ C) → (C → P ∞)
corec {A ▹ B} {C} f c = (u , ne , conv)
  where
    u-aux : C → PreApprox (A ▹ B)
    u-aux c zero =
      let (a , α) = f c
      in sup (inj₁ (a , (λ x → sup (inj₂ tt))))
    u-aux c (suc n) =
      let (a , α) = f c
      in sup (inj₁ (a , (λ b → u-aux (α b) n)))

    u : PreApprox (A ▹ B)
    u = u-aux c

    ne : non-empty (u 0)
    ne = tt

    conv-aux : (c : C) → converges (u-aux c)
    conv-aux c zero    = (refl , (λ b → tt))
    conv-aux c (suc n) = (refl , (λ b → conv-aux (proj₂ (f c) b) n))

    conv : converges u
    conv = conv-aux c

-- | That's the best we can get....
conv-root∞ : ∀{A B C} → (f : C → ⟦ A ▹ B ⟧ C) (c : C) →
             root∞ (corec f c) ≡ proj₁ (⟦ A ▹ B ⟧₁ (corec f) (f c))
conv-root∞ {A} {B} {C} f c =
  begin
    root∞ (corec f c)
  ≡⟨ refl ⟩
    proj₁ (out (corec f c))
  ≡⟨ refl ⟩
    proj₁ (f c)
  ≡⟨ refl ⟩
    proj₁ (⟦ A ▹ B ⟧₁ (corec f) (f c))
  ∎

ext-Σ : ∀{A : Set} {B : A → Set} →
        {a a' : A} → (b : B a) (b' : B a') →
        a ≡ a' → b ≅ b' → (a , b) ≡ (a' , b')
ext-Σ b .b refl refl = refl

conv-branch∞ : ∀{A B C} → (f : C → ⟦ A ▹ B ⟧ C) (c : C) →
               branch∞ (corec f c) ≅ proj₂ (⟦ A ▹ B ⟧₁ (corec f) (f c))
conv-branch∞ {A} {B} f c =
  q (branch∞ (corec f c))
    (proj₂ (⟦ A ▹ B ⟧₁ (corec f) (f c)))
    (conv-root∞ f c)
    refl refl
  where
    q : ∀ {a} (α : B a → (A ▹ B)∞) (β : B (proj₁ (f c)) → (A ▹ B)∞) →
        a ≡ proj₁ (f c) →
        α ≅ branch∞ (corec f c) →
        β ≅ proj₂ (⟦ A ▹ B ⟧₁ (corec f) (f c)) →
        α ≅ β
    q .(branch∞ (corec f c)) .(proj₂ (⟦ A ▹ B ⟧₁ (corec f) (f c))) refl refl refl
      = {!!}

-- | ... because the full conversion rule fails due to missing extensionality.
conv∞ : ∀{P C f} → (c : C) → out (corec f c) ≡ ⟦ P ⟧₁ (corec f) (f c)
conv∞ {A ▹ B} {C} {f} c =
  let (a , α) = f c
      (a₁ , α₁) = out (corec f c)
      (a₂ , α₂) = ⟦ A ▹ B ⟧₁ (corec f) (f c)
  in ext-Σ α₁ α₂ (conv-root∞ f c) (conv-branch∞ f c)
