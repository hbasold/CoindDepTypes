module Common.Context  where

import Level
open import Data.Nat as Nat
open import Data.List as List
import Level
open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Relation.Binary -- using (Setoid; Rel; IsEquivalence)
open ≡-Reasoning
open import Function as Fun hiding (_∘′_)
open import Data.Sum as Sum hiding ([_,_])
-- open import Categories.Category using (Category)

-- open import Common.SumProperties

-------------------------
---- Type contexts

Ctx : Set → Set
Ctx Ty = List Ty

_↑_ : ∀{U} → Ctx U → U → Ctx U
Γ ↑ a = Γ ++ a ∷ []

-- | De Bruijn variable indexing
data Var {Ty : Set} : (Γ : Ctx Ty) (a : Ty) → Set where
  zero : ∀{Γ a}                          → Var (a ∷ Γ) a
  succ : ∀{Γ b} (a : Ty) → (x : Var Γ a) → Var (b ∷ Γ) a

data _≅V_ {Ty} : ∀ {Γ Γ' : Ctx Ty} {a a' : Ty} → Var Γ a → Var Γ' a' → Set where
  zero : ∀ {Γ Γ'} {a a'}
         → zero {Γ = Γ} {a} ≅V zero {Γ = Γ'} {a'}

  succ  : ∀ {Γ Γ'} {a a'}
          → ∀ {x : Var Γ a} {x' : Var Γ' a'} {b b' : Ty}
          → x ≅V x'
          → succ {b = b} a x ≅V succ {b = b'} a' x'

Vrefl : ∀ {Ty} {Γ} {a : Ty} {x : Var Γ a} → x ≅V x
Vrefl {x = zero}  = zero
Vrefl {x = succ _ t} = succ Vrefl

Vsym : ∀ {Ty} {Γ Γ'} {a a' : Ty} {x : Var Γ a} {x' : Var Γ' a'}
       → x ≅V x' → x' ≅V x
Vsym zero      = zero
Vsym {Ty} (succ [x]) = succ (Vsym [x])

Vtrans : ∀ {Ty} {Γ Γ' Γ''} {a a' a'' : Ty}
           {x : Var Γ a} {x' : Var Γ' a'} {x'' : Var Γ'' a''}
         → x ≅V x' → x' ≅V x'' → x ≅V x''
Vtrans zero     zero      = zero
Vtrans (succ eq) (succ eq') = succ (Vtrans eq eq')

-- Note: makes the equality homogeneous in Γ and a
≅V-setoid : ∀ {Ty} {Γ} {a : Ty} → Setoid _ _
≅V-setoid {Ty} {Γ} {a} = record
  { Carrier = Var Γ a
  ; _≈_ = _≅V_
  ; isEquivalence = record
    { refl = Vrefl ; sym = Vsym ; trans = Vtrans }
  }

arr : ∀ {Ty} → (Γ Δ : Ctx Ty) → Set
arr {Ty} Γ Δ = ∀ (a : Ty) → Var Γ a → Var Δ a

_►_ = arr
-- _▹_ = arr

infix 4 _≡C_

record _≡C_ {Ty} {Γ Δ : Ctx Ty} (ρ : arr Γ Δ) (γ : arr Γ Δ) : Set where
  field
    ≡C-proof : ∀ {a} {x} → ρ a x ≡ γ a x
open _≡C_

_≈_ = _≡C_

Crefl : ∀ {Ty} {Γ Δ : Ctx Ty} → Reflexive (_≡C_ {Γ = Γ} {Δ})
Crefl = record { ≡C-proof = PE.refl }
Csym : ∀ {Ty} {Γ Δ : Ctx Ty} → Symmetric (_≡C_ {Γ = Γ} {Δ})
Csym p = record { ≡C-proof = PE.sym (≡C-proof p) }
Ctrans : ∀ {Ty} {Γ Δ : Ctx Ty} → Transitive (_≡C_ {Γ = Γ} {Δ})
Ctrans p₁ p₂ = record { ≡C-proof = PE.trans (≡C-proof p₁) (≡C-proof p₂) }

≡C-equiv : ∀ {Ty} {Γ Δ : Ctx Ty} → IsEquivalence (_≡C_ {Γ = Γ} {Δ})
≡C-equiv =
  record
  { refl = Crefl
  ; sym = Csym
  ; trans = Ctrans
  }

≡C-setoid : ∀ {Ty} {Γ Δ : Ctx Ty} → Setoid _ _
≡C-setoid {_} {Γ} {Δ} = record
  { Carrier = arr Γ Δ
  ; _≈_ = _≡C_
  ; isEquivalence = ≡C-equiv
  }

_∘′_ : ∀ {Ty} {Γ Δ Ξ : Ctx Ty} (ρ : Δ ► Ξ) (γ : Γ ► Δ) → Γ ► Ξ
_∘′_ ρ γ = λ a x → ρ a (γ a x)

_●_ = _∘′_

ctx-id : ∀ {Ty} {Γ : Ctx Ty} →  arr Γ Γ
ctx-id = λ _ x → x

comp-resp-≡C : ∀ {Ty} {Γ Δ Ξ : Ctx Ty} {ρ ρ' : arr Δ Ξ} {γ γ' : arr Γ Δ} →
               ρ ≡C ρ' → γ ≡C γ' → ρ ∘′ γ ≡C ρ' ∘′ γ'
comp-resp-≡C {_} {Γ} {Δ} {Ξ} {ρ} {ρ'} {γ} {γ'} ρ≡ρ' γ≡γ'
  = record { ≡C-proof = p }
  where
    p : ∀ {a} {x} → (ρ ∘′ γ) a x ≡ (ρ' ∘′ γ') a x
    p {a} {x} =
      begin
        (ρ ∘′ γ) a x
      ≡⟨ refl ⟩
        ρ a (γ a x)
      ≡⟨ cong (λ u → ρ a u) (≡C-proof γ≡γ') ⟩
        ρ a (γ' a x)
      ≡⟨ ≡C-proof ρ≡ρ' ⟩
        ρ' a (γ' a x)
      ≡⟨ refl ⟩
        (ρ' ∘′ γ') a x
      ∎

{-
-- | Contexts form a category
ctx-cat : Set → Category Level.zero Level.zero Level.zero
ctx-cat Ty = record
   { Obj = Ctx Ty
   ; _⇒_ = arr
   ; _≡_ = _≡C_
   ; _∘_ = _∘′_
   ; id = ctx-id
   ; assoc = record { ≡C-proof = refl }
   ; identityˡ = record { ≡C-proof = refl }
   ; identityʳ = record { ≡C-proof = refl }
   ; equiv = ≡C-equiv
   ; ∘-resp-≡ = comp-resp-≡C
   }
-}

-------------------------
---- Coproduct structure on contexts

{-
_⊕_ : Ctx → Ctx → Ctx
Γ₁ ⊕ Γ₂ = Γ₁ ++ Γ₂

in₁ : {Γ₁ Γ₂ : Ctx} → Γ₁ ▹ (Γ₁ ⊕ Γ₂)
in₁ _ zero     = zero
in₁ a (succ .a x) = succ a (in₁ a x)

in₂ : {{Γ₁ Γ₂ : Ctx}} → Γ₂ ▹ (Γ₁ ⊕ Γ₂)
in₂ {{[]}}     _ x = x
in₂ {{b ∷ Γ₁}} a x = succ a (in₂ a x)

split : {Γ₁ Γ₂ : Ctx} {a : Ty} → Var (Γ₁ ⊕ Γ₂) a → Var Γ₁ a ⊎ Var Γ₂ a
split {[]}      {Γ₂}     x        = inj₂ x
split {a ∷ Γ₁'} {Γ₂}     zero     = inj₁ zero
split {b ∷ Γ₁'} {Γ₂} {a} (succ .a y) = (Sum.map (succ a) (ctx-id a)) (split {Γ₁'} y)

[_,_] : {Γ₁ Γ₂ Δ : Ctx} (f : Γ₁ ▹ Δ) (g : Γ₂ ▹ Δ)
      → ((Γ₁ ⊕ Γ₂) ▹ Δ)
[_,_] {Γ} {Γ₂} f g a x = ([ f a , g a ]′) (split x)

_-⊕-_ : {Γ Γ₂ Γ' Γ₂' : Ctx} (f : Γ ▹ Γ') (g : Γ₂ ▹ Γ₂')
      → ((Γ ⊕ Γ₂) ▹ (Γ' ⊕ Γ₂'))
_-⊕-_ {Γ} {Γ₂} {Γ'} {Γ₂'} f g = [ in₁ ● f , in₂ {{Γ'}} {{Γ₂'}} ● g ]


succ-distr-lemma : {Γ : Ctx} {a b : Ty} (Γ₂ : Ctx) (x : Var Γ a) →
                   (in₁ {b ∷ Γ} ● succ {Γ}) a x
                   ≡ (succ {Γ ⊕ Γ₂} ● in₁ {Γ} {Γ₂}) a x
succ-distr-lemma Γ₂ x = refl

split-lemma₁ : {a : Ty} (Γ₁ Γ₂ : Ctx) (x : Var Γ₁ a) →
               split {Γ₁} {Γ₂} (in₁ {Γ₁} a x) ≡ inj₁ x
split-lemma₁ (tt ∷ Γ₁) Γ₂ zero       = refl
split-lemma₁ (tt ∷ Γ₁) Γ₂ (succ a x) =
  begin
    split {tt ∷ Γ₁} (in₁ {tt ∷ Γ₁} a (succ a x))
  ≡⟨ refl ⟩
    (Sum.map (succ a) id) (split (in₁ a x))
  ≡⟨ cong (Sum.map (succ a) id) (split-lemma₁ Γ₁ Γ₂ x) ⟩
    (Sum.map (succ a) id) (inj₁ x)
  ≡⟨ refl ⟩
    inj₁ (succ a x)
  ∎

split-lemma₂ : {a : Ty} (Γ₁ Γ₂ : Ctx) (x : Var Γ₂ a) →
               split {Γ₁} {Γ₂} (in₂ a x) ≡ inj₂ x
split-lemma₂ [] Γ₂ x = refl
split-lemma₂ {a} (tt ∷ Γ₁) Γ₂ x =
  begin
    split {tt ∷ Γ₁} {Γ₂} (in₂ {{tt ∷ Γ₁}} a x)
  ≡⟨ refl ⟩
    Sum.map (succ a) id (split (in₂ {{Γ₁}} a x))
  ≡⟨ cong (λ u → Sum.map (succ a) id u) (split-lemma₂ Γ₁ Γ₂ x) ⟩
    Sum.map (succ a) id (inj₂ x)
  ≡⟨ refl ⟩
    inj₂ x
  ∎

split-lemma : (Γ₁ Γ₂ : Ctx) (a : Ty) (x : Var (Γ₁ ⊕ Γ₂) a) →
             [ in₁ {Γ₁} {Γ₂} a , in₂ a ]′ (split x) ≡ x
split-lemma []       Γ₂ _  x           = refl
split-lemma (a ∷ Γ₁) Γ₂ .a zero        = refl
split-lemma (b ∷ Γ₁) Γ₂ a  (succ .a x) =
  begin
    [ in₁ {b ∷ Γ₁} a , in₂ {{b ∷ Γ₁}} a ]′ (split (succ a x))
  ≡⟨ refl ⟩
    [ in₁ {b ∷ Γ₁} a , (succ {Γ₁ ⊕ Γ₂} ● in₂ {{Γ₁}} ) a ]′
      (Sum.map (succ {Γ₁} a) id (split x))
  ≡⟨ copair-sum-map-merge {f₁ = Var.succ {Γ₁} {b} a} (split x) ⟩
    [ (in₁ {b ∷ Γ₁} ● succ {Γ₁}) a , (succ {Γ₁ ⊕ Γ₂} ● in₂) a ]′ (split x)
  ≡⟨ copair-cong {f = (in₁ {b ∷ Γ₁} ● succ {Γ₁}) a}
                 (succ-distr-lemma Γ₂)
                 (split x) ⟩
    [ (succ {Γ₁ ⊕ Γ₂} ● in₁ {Γ₁}) a , (succ {Γ₁ ⊕ Γ₂} ● in₂) a ]′ (split x)
  ≡⟨ copair-distr {f = in₁ {Γ₁} {Γ₂} a} {h = succ {Γ₁ ⊕ Γ₂} a} (split x)⟩
    (Var.succ {Γ₁ ⊕ Γ₂} {b} a ∘ [ in₁ {Γ₁} a , in₂ a ]′) (split x)
  ≡⟨ cong (succ {Γ₁ ⊕ Γ₂} {b} a) (split-lemma Γ₁ Γ₂ a x) ⟩
     succ {Γ₁ ⊕ Γ₂} a x
  ∎

⊕-is-coprod-arg : ∀{Γ₁ Γ₂ : Ctx} (a : Ty) (x : Var (Γ₁ ⊕ Γ₂) a) →
                  [ in₁ {Γ₁} {Γ₂} , in₂ ] a x ≡ ctx-id a x
⊕-is-coprod-arg {Γ₁} {Γ₂} = split-lemma Γ₁ Γ₂

⊕-is-coprod : ∀{Γ₁ Γ₂ : Ctx} → [ in₁ {Γ₁} {Γ₂} , in₂ ] ≡C ctx-id
⊕-is-coprod {Γ₁} = {!!}
{-
  η-≡ {f₁ = [ in₁ {Γ₁} , in₂ ]}
      {f₂ = ctx-id}
      (λ (a : Ty) →
        η-≡ {f₁ = [ in₁ {Γ₁}, in₂ ] a}
            {f₂ = ctx-id a}
            (⊕-is-coprod-arg {Γ₁} a)
       )
-}

●-distr-copair₁ˡ : ∀{Γ₁ Γ₂ Δ : Ctx}
                   (h : (Γ₁ ⊕ Γ₂) ▹ Δ) (a : Ty) (x : Var (Γ₁ ⊕ Γ₂) a) →
                   [ h ● in₁ {Γ₁} {Γ₂} , h ● in₂ {{Γ₁}} {{Γ₂}} ] a x
                   ≡ (h ● [ in₁ {Γ₁} {Γ₂} , in₂ ]) a x
●-distr-copair₁ˡ {Γ₁} {Γ₂} {Δ} h a x =
  begin
    [ h ● in₁ {Γ₁} , h ● in₂ ] a x
  ≡⟨ refl ⟩
    ([ (h ● in₁ {Γ₁}) a , (h ● in₂) a ]′) (split x)
  ≡⟨ copair-distr {f = in₁ {Γ₁} a} {g = in₂ a} {h = h a} (split x) ⟩
    (h ● [ in₁ {Γ₁} , in₂ ]) a x
  ∎

●-distr-copairˡ : ∀{Γ₁ Γ₂ Δ : Ctx} (h : (Γ₁ ⊕ Γ₂) ▹ Δ) →
                 [ h ● in₁ {Γ₁} {Γ₂} , h ● in₂ {{Γ₁}} {{Γ₂}} ]
                 ≡ h ● [ in₁ {Γ₁} {Γ₂} , in₂ ]
●-distr-copairˡ {Γ₁} h = {!!}
  -- η-≡ (λ a → η-≡ (●-distr-copair₁ˡ {Γ₁} h a))

⊕-is-coprod₁ : ∀{Γ₁ Γ₂ Δ : Ctx} {f : Γ₁ ▹ Δ} {g : Γ₂ ▹ Δ} {h : (Γ₁ ⊕ Γ₂) ▹ Δ} →
               h ● in₁ ≡C f → h ● in₂ ≡C g → [ f , g ] ≡C h
⊕-is-coprod₁ {Γ₁} {Γ₂} {Δ} {f} {g} {h} h●in₁≡f h●in₂≡g
  = record { ≡C-proof = p }
  where
    p : ∀ {a} {x} → [ f , g ] a x ≡ h a x
    p {a} {x} =
      begin
        [ f , g ] a x
      ≡⟨ refl ⟩
        ([ f a , g a ]′) (split x)
      ≡⟨ cong (λ u → [ u , g a ]′ (split x)) {!!} ⟩
        ([ (h ● in₁ {Γ₁}) a , g a ]′) (split x)
      ≡⟨ {!!} ⟩
        h a x
      ∎
{-
        [ h ● in₁ {Γ₁} , g ]
      ≡⟨ cong (λ u → [ h ● in₁ {Γ₁} , u ]) (sym h●in₂≡g) ⟩
        [ h ● in₁ {Γ₁} , h ● in₂ ]
      ≡⟨ ●-distr-copairˡ {Γ₁} h ⟩
        h ● [ in₁ {Γ₁}, in₂ ]
      ≡⟨ cong (λ u → h ● u) (⊕-is-coprod {Γ₁}) ⟩
        h ● ctx-id
      ≡⟨ refl ⟩
        h
  -}

commute-in₁-arg : ∀ {Γ₁ Γ₂ Δ : Ctx} {f : Γ₁ ▹ Δ} {g : Γ₂ ▹ Δ}
                    (a : Ty) (x : Var Γ₁ a) →
                  ([ f , g ] ● in₁) a x ≡ f a x
commute-in₁-arg _ zero = refl
commute-in₁-arg {b ∷ Γ₁} {Γ₂} {Δ} {f} {g} a (succ .a x) =
  begin
    ([ f , g ] ● in₁ {b ∷ Γ₁}) a (succ {Γ₁} a x)
  ≡⟨ refl ⟩
    [ f , g ] a (succ {Γ₁ ⊕ Γ₂} a (in₁ {Γ₁} a x))
  ≡⟨ refl ⟩
    ([ f a , g a ]′) (split (succ {Γ₁ ⊕ Γ₂} a (in₁ {Γ₁} a x)))
  ≡⟨ refl ⟩
    [ f a , g a ]′ ((Sum.map (succ a) id) (split {Γ₁} {Γ₂} (in₁ {Γ₁} a x)))
  ≡⟨ refl ⟩
    (([ f a , g a ]′ ∘ (Sum.map (succ a) id)) (split {Γ₁} {Γ₂} (in₁ {Γ₁} a x)))
  ≡⟨ copair-sum-map-merge {f₁ = succ a} (split {Γ₁} {Γ₂} (in₁ {Γ₁} a x)) ⟩
    ([ (f ● succ) a , g a ]′ (split {Γ₁} {Γ₂} (in₁ {Γ₁} a x)))
  ≡⟨ cong ([ (f ● succ) a , g a ]′) (split-lemma₁ Γ₁ Γ₂ x) ⟩
    f a (succ a x)
  ∎

commute-in₁ : (Γ₁ : Ctx) → (Γ₂ : Ctx) → {Δ : Ctx} {f : Γ₁ ▹ Δ} {g : Γ₂ ▹ Δ}
              → ([ f , g ] ● in₁) ≡C f
commute-in₁ Γ₁ Γ₂ {Δ} {f} {g} =
  record { ≡C-proof = λ {a} {x} → commute-in₁-arg {f = f} {g} a x }

commute-in₂-arg : ∀ {Γ₁ Γ₂ Δ : Ctx} {f : Γ₁ ▹ Δ} {g : Γ₂ ▹ Δ}
                    (a : Ty) (x : Var Γ₂ a) →
                  ([ f , g ] ● in₂) a x ≡ g a x
commute-in₂-arg {[]} _ _ = refl
commute-in₂-arg {tt ∷ Γ₁} {Γ₂} {Δ} {f} {g} a x =
  begin
    ([ f , g ] ● in₂ {{tt ∷ Γ₁}} ) a x
  ≡⟨ refl ⟩
    [ f , g ] a ((succ ● in₂) a x)
  ≡⟨ refl ⟩
    [ f a , g a ]′ (split {tt ∷ Γ₁} (succ a (in₂ a x)))
  ≡⟨ cong (λ u → [ f a , g a ]′ u) {x = split {tt ∷ Γ₁} (succ a (in₂ a x))} refl ⟩
    [ f a , g a ]′ ((Sum.map (succ a) id) (split {Γ₁} (in₂ a x)))
  ≡⟨ cong (λ u → [ f a , g a ]′ (Sum.map (succ a) id u)) (split-lemma₂ Γ₁ Γ₂ x) ⟩
    [ f a , g a ]′ ((Sum.map (succ a) id) (inj₂ x))
  ≡⟨ copair-sum-map-merge {f₁ = succ {Γ₁} a} {f₂ = id} {g₁ = f a} {g₂ = g a} (inj₂ x) ⟩
    [ (f ● succ) a , (g ● ctx-id) a ]′ (inj₂ x)
  ≡⟨ copair-elimʳ {f = (f ● succ) a} {g = (g ● ctx-id) a} x ⟩
    g a x
  ∎

commute-in₂ : (Γ₁ : Ctx) → (Γ₂ : Ctx) → {Δ : Ctx} {f : Γ₁ ▹ Δ} {g : Γ₂ ▹ Δ}
              → ([ f , g ] ● in₂) ≡C g
commute-in₂ Γ₁ Γ₂ {Δ} {f} {g} =
  record { ≡C-proof = λ {a} {x} → commute-in₂-arg {f = f} {g} a x }

open import Categories.Object.Coproduct ctx-cat

ctx-coproduct : ∀{Γ₁ Γ₂ : Ctx} → Coproduct Γ₁ Γ₂
ctx-coproduct {Γ₁} {Γ₂} = record
                  { A+B = Γ₁ ⊕ Γ₂
                  ; i₁ = in₁
                  ; i₂ = in₂
                  ; [_,_] = [_,_]
                  ; commute₁ = commute-in₁ Γ₁ Γ₂
                  ; commute₂ = commute-in₂ Γ₁ Γ₂
                  ; universal = ⊕-is-coprod₁
                  }

open import Categories.Object.BinaryCoproducts ctx-cat

ctx-bin-coproducts : BinaryCoproducts
ctx-bin-coproducts = record { coproduct = ctx-coproduct }

open BinaryCoproducts ctx-bin-coproducts

-}
