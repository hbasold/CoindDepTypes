module SyntaxRaw where

import Level
open import Data.Empty
open import Data.Unit as Unit
open import Data.Nat
open import Data.List as List renaming ([] to Ø; [_] to [_]L)
open import Data.List.Properties using (++-monoid)
open import NonEmptyList as NList
open import Data.Vec as Vec hiding ([_]; _++_)
open import Data.Product as Prod
open import Function

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Relation.Binary using (module IsEquivalence; Setoid; module Setoid)
open ≡-Reasoning

open import Common.Context as Context

open import Algebra
open Monoid {{ ... }} hiding (refl)

data Phantom {A : Set} (a : A) : Set where
  phantom : Phantom a

record Univ (P : Phantom tt) : Set where
  field
    x : ⊤

U : Set
U = Σ (Phantom tt) Univ

∗ : U
∗ = (phantom , record { x = tt })

length' : {A : Set} → List A → ℕ
length' Ø = 0
length' (x ∷ xs) = suc (length' xs)

length'-hom : {A : Set} → (l₁ l₂ : List A) →
             length' (l₁ ++ l₂) ≡ length' l₁ + length' l₂
length'-hom Ø        l₂ = refl
length'-hom (x ∷ l₁) l₂ = cong suc (length'-hom l₁ l₂)

length'ᵣ-1 : {A : Set} (l : List A) (a : A) →
             (length' l) + 1 ≡ length' (l ++ a ∷ Ø)
length'ᵣ-1 Ø a = refl
length'ᵣ-1 (x ∷ l) a = cong suc (length'ᵣ-1 l a)

length'-commute₁ : {A : Set} (l : List A) (a : A) →
                   length' (a ∷ l) ≡ length' (l ++ a ∷ Ø)
length'-commute₁ Ø a = refl
length'-commute₁ (x ∷ l) a = cong suc (length'-commute₁ l a)

mvVar : ∀ {A} (Γ₁ Γ₂ : List A) (x : A) → Γ₂ ++ x ∷ Γ₁ ≡ Γ₂ ↑ x ++ Γ₁
mvVar Γ₁ Ø x = refl
mvVar Γ₁ (y ∷ Γ₂) x = cong (λ u → y ∷ u) (mvVar Γ₁ Γ₂ x)

mvVar-length : ∀ {A} (Γ₁ Γ₂ : List A) (x : A) →
               length' (Γ₂ ++ x ∷ Γ₁) ≡ length' (Γ₂ ↑ x ++ Γ₁)
mvVar-length Γ₁ Γ₂ x = cong length' (mvVar Γ₁ Γ₂ x)

data FP : Set where
  μ : FP
  ν : FP

RawCtx : Set
RawCtx = Ctx U

instance ctx-monoid : Monoid _ _
ctx-monoid = ++-monoid U

RawVar : RawCtx → U → Set
RawVar = Var

TyCtx : Set
TyCtx = Ctx RawCtx

instance tyctx-monoid : Monoid _ _
tyctx-monoid = ++-monoid RawCtx

TyVar : TyCtx → RawCtx → Set
TyVar = Var

CtxMor : (TyCtx → RawCtx → RawCtx → Set) → RawCtx → RawCtx → Set
CtxMor R Γ₁ Γ₂ = Vec (R Ø Γ₁ Ø) (length' Γ₂)

FpData : (TyCtx → RawCtx → RawCtx → Set) → TyCtx → RawCtx → Set
FpData R Θ Γ = NList (Σ RawCtx (λ Γ' → CtxMor R Γ' Γ × R (Γ ∷ Θ) Γ' Ø))

-- | List of types, context morphisms and terms (Aₖ, fₖ, gₖ) such that
--            Γₖ, x : Aₖ[C/X] ⊢ gₖ : C fₖ or
--            Γₖ, x : C fₖ ⊢ gₖ : Aₖ[C/X],
-- which are the premisses of the rule for recursion and corecursion,
-- respectively.
FpMapData : (TyCtx → RawCtx → RawCtx → Set) → RawCtx → Set
FpMapData R Γ = NList (Σ RawCtx λ Γ' →
                         R [ Γ ]L Γ' Ø × CtxMor R Γ' Γ × R Ø (∗ ∷ Γ') Ø)

-- | Types and objects with their corresponding (untyped) type, object
-- variable contexts and parameter contexts.
-- Note that, if Θ | Γ₁ ⊢ M ⊸ Γ₂, i.e., M : Raw Θ Γ₁ Γ₂,
-- then Γ₂ needs to be read in reverse. The reason is that Γ₂ signifies
-- parameters that are instantiated in application-style. Also, variables
-- can be moved for types like in
-- Γ₁, x : A ⊢ B : Γ₂(∗)  → Γ₁ ⊢ λx.B : (x : A) ⊸ Γ₂(∗).
data Raw : TyCtx → RawCtx → RawCtx → Set where
  ----- Common constructors
  instRaw : {Θ : TyCtx} {Γ₁ Γ₂ : RawCtx} {A : U} →
            Raw Θ Γ₁ (Γ₂ ↑ A) → Raw Ø Γ₁ Ø → Raw Θ Γ₁ Γ₂

  ----- Object constructors
  unitRaw : (Γ : RawCtx) → Raw Ø Γ Ø
  objVarRaw : {Γ : RawCtx} {A : U} → RawVar Γ A → Raw Ø Γ Ø
  -- | initial/final dialgebra. dialgRaw ρ k is either αₖ or ξₖ, depending on ρ.
  dialgRaw : (Δ : RawCtx) (Γ : RawCtx) (A : U) → FP → ℕ → Raw Ø Δ (A ∷ Γ)
  recRaw : (Γ Δ : RawCtx) → FpMapData Raw Γ → FP → Raw Ø Δ (∗ ∷ Γ)

  ----- Type constructors
  ⊤-Raw : (Θ : TyCtx) (Γ : RawCtx) → Raw Θ Γ Ø
  tyVarRaw : {Θ : TyCtx} (Γ₁ : RawCtx) {Γ₂ : RawCtx} → TyVar Θ Γ₂ → Raw Θ Γ₁ Γ₂
  paramAbstrRaw : {Θ : TyCtx} {Γ₂ : RawCtx} (Γ₁ : RawCtx) {A : U} →
                  Raw Θ (A ∷ Γ₁) Γ₂ → Raw Θ Γ₁ (Γ₂ ↑ A)
  -- | Constructor for fixed points. The first component is intended to be
  -- the context morphism, the second is the type.
  fpRaw : {Θ : TyCtx} {Γ₂ : RawCtx} (Γ₁ : RawCtx) →
          FP → FpData Raw Θ Γ₂ → Raw Θ Γ₁ Γ₂

weakenObjVar : (Γ₁ : RawCtx) {Γ₂ : RawCtx} →
               (A : U) {B : U} → RawVar (Γ₁ ++ Γ₂) B → RawVar (Γ₁ ++ A ∷ Γ₂) B
weakenObjVar Ø         A x           = succ _ x
weakenObjVar (._ ∷ Γ₁) A zero        = zero
weakenObjVar (B ∷ Γ₁)  A (succ ._ x) = succ _ (weakenObjVar Γ₁ A x)

weaken : {Θ : TyCtx} (Γ₁ : RawCtx) {Γ₂ Γ₃ : RawCtx} →
         (A : U) → Raw Θ (Γ₁ ++ Γ₂) Γ₃ → Raw Θ (Γ₁ ++ A ∷ Γ₂) Γ₃
weaken Γ₁ {Γ₂} A (instRaw t s)                     =
  instRaw (weaken Γ₁ A t) (weaken Γ₁ A s)
weaken Γ₁ {Γ₂} A (unitRaw .(Γ₁ ++ Γ₂))             = unitRaw _
weaken Γ₁ {Γ₂} A (objVarRaw x)         =
  objVarRaw (weakenObjVar Γ₁ A x)
weaken Γ₁ {Γ₂} A (dialgRaw .(Γ₁ ++ Γ₂) Γ B ρ k)    = dialgRaw _ Γ B ρ k
weaken Γ₁ {Γ₂} A (recRaw Γ .(Γ₁ ++ Γ₂) gs ρ)       = recRaw Γ _ gs ρ
weaken Γ₁ {Γ₂} A (⊤-Raw Θ .(Γ₁ ++ Γ₂))             = ⊤-Raw Θ _
weaken Γ₁ {Γ₂} A (tyVarRaw .(Γ₁ ++ Γ₂) X)          = tyVarRaw _ X
weaken Γ₁ {Γ₂} A (paramAbstrRaw .(Γ₁ ++ Γ₂) {B} C) =
  paramAbstrRaw (Γ₁ ++ A ∷ Γ₂) (weaken (B ∷ Γ₁) A C)
weaken Γ₁ {Γ₂} A (fpRaw .(Γ₁ ++ Γ₂) ρ D)           = fpRaw _ ρ D

weaken₁ : ∀ {Θ Γ₁ Γ₂} → (A : U) → Raw Θ Γ₁ Γ₂ → Raw Θ (A ∷ Γ₁) Γ₂
weaken₁ = weaken Ø

ctxid : (Γ : RawCtx) → CtxMor Raw Γ Γ
ctxid Ø = []
ctxid (A ∷ Γ) = (objVarRaw {A ∷ Γ} {A} zero)
                ∷ Vec.map (weaken Ø A) (ctxid Γ)

-- | Build the instantiation "t f" of a raw term t by a context morphism f
instWCtxMor : {Θ : TyCtx} {Γ₁ Γ₂ Γ₃ : RawCtx} →
              Raw Θ Γ₁ (Γ₃ ++ Γ₂) → CtxMor Raw Γ₁ Γ₂ → Raw Θ Γ₁ Γ₃
instWCtxMor {Θ} {Γ₁} {Ø} {Γ₃} t [] = subst (Raw Θ Γ₁) (proj₂ identity Γ₃) t
instWCtxMor {Θ} {Γ₁} {x ∷ Γ₂} {Γ₃} t (s ∷ f) =
  instRaw (instWCtxMor (subst (Raw Θ Γ₁) (mvVar _ Γ₃ x) t) f) s

-- | Retrieve the term to be substituted for a variable from a context morphism
get : {R : TyCtx → RawCtx → RawCtx → Set} {Γ₁ Γ₂ : RawCtx} {A : U} →
      CtxMor R Γ₂ Γ₁ → RawVar Γ₁ A → R Ø Γ₂ Ø
get {R} {Ø}       []     ()
get {R} {_ ∷ Γ₁} (M ∷ f) zero        = M
get {R} {_ ∷ Γ₁} (M ∷ f) (succ ._ x) = get {R} f x

-- | Extends a context morphism to be the identity on a new variable
extend : {Γ₁ Γ₂ : RawCtx} →
         (A : U) → CtxMor Raw Γ₂ Γ₁ → CtxMor Raw (A ∷ Γ₂) (A ∷ Γ₁)
extend {Γ₁} {Γ₂} A f = (objVarRaw {A ∷ Γ₂} {A} zero) ∷ (Vec.map (weaken₁ A) f)

-- | Substitution on raw terms
substRaw : ∀ {Θ Γ₁ Γ Γ₂} → Raw Θ Γ₁ Γ → CtxMor Raw Γ₂ Γ₁ → Raw Θ Γ₂ Γ
substRaw (instRaw M N)         f = instRaw (substRaw M f) (substRaw N f)
substRaw (unitRaw Γ)           f = unitRaw _
substRaw (objVarRaw x)         f = get {Raw} f x
substRaw (dialgRaw Δ Γ A ρ k)  f = dialgRaw _ Γ A ρ k
substRaw (recRaw Γ Δ gs ρ)     f = recRaw Γ _ gs ρ
substRaw (⊤-Raw Θ Γ)           f = ⊤-Raw Θ _
substRaw (tyVarRaw Γ₁ X)       f = tyVarRaw _ X
substRaw (paramAbstrRaw Γ₁ A)  f = paramAbstrRaw _ (substRaw A (extend _ f))
substRaw (fpRaw Γ₁ ρ D)        f = fpRaw _ ρ D

-- | Context morphism that projects on arbitrary prefix of a context
ctxProjRaw : (Γ₁ Γ₂ : RawCtx) → CtxMor Raw (Γ₂ ++ Γ₁) Γ₁
ctxProjRaw Γ₁ Ø = ctxid Γ₁
ctxProjRaw Γ₁ (A ∷ Γ₂) = Vec.map (weaken₁ A) (ctxProjRaw Γ₁ Γ₂)

-- | Extend one step weakening to weakening by arbitrary contexts
weaken' : ∀ {Θ Γ₁ Γ₃} →
          (Γ₂ : RawCtx) → Raw Θ Γ₁ Γ₃ → Raw Θ (Γ₂ ++ Γ₁) Γ₃
weaken' {Γ₁ = Γ₁} Γ₂ t = substRaw t (ctxProjRaw Γ₁ Γ₂)

-----------------------------------------
--- Examples
-----------------------------------------

_︵_ : {A : Set} → A → A → List A
a ︵ b = a ∷ b ∷ Ø

-- | Binary product type
ProdRaw : (Γ : RawCtx) → Raw (Γ ︵ Γ) Ø Γ
ProdRaw Γ = fpRaw Ø ν D
  where
    Δ = Γ ︵ Γ

    A : TyVar (Γ ∷ Δ) Γ
    A = succ Γ zero

    B : TyVar (Γ ∷ Δ) Γ
    B = succ Γ (succ Γ zero)

    D₁ = (Γ , ctxid Γ , instWCtxMor (tyVarRaw Γ A) (ctxid Γ))

    D₂ = (Γ , ctxid Γ , instWCtxMor (tyVarRaw Γ B) (ctxid Γ))

    D : FpData Raw Δ Γ
    D = D₁ ∷ [ D₂ ]
