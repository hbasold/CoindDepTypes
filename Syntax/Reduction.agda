module Reduction where

import Level
open import Data.Empty
open import Data.Unit as Unit
open import Data.Nat
open import Data.List as List renaming ([] to Ø; [_] to [_]L)
open import NonEmptyList as NList
open import Data.Fin hiding (_+_)
open import Data.Vec as Vec renaming ([_] to [_]V; _++_ to _++V_)
open import Data.Product as Prod
open import Function

open import Relation.Binary.PropositionalEquality as PE hiding ([_])
open import Relation.Binary
open ≡-Reasoning

Rel₀ : Set → Set₁
Rel₀ X = Rel X Level.zero

open import Common.Context as Context

open import Algebra
open Monoid {{ ... }} hiding (refl)

open import SyntaxRaw
open import Syntax

-----------------------------------------------------
---- Action of types on terms
-----------------------------------------------------

PreArrow : RawCtx → Set
PreArrow Γ = PreType Ø Γ Ø × PreTerm (∗ ∷ Γ) Ø × PreType Ø Γ Ø

Args : TyCtx → Set
Args Ø = ⊤
Args (Γ ∷ Θ) = PreArrow Γ × (Args Θ)

getArg : ∀ {Θ Γ₁} → TyVar Θ Γ₁ → Args Θ → PreTerm (∗ ∷ Γ₁) Ø
getArg zero        ((_ , t , _) , ts) = t
getArg (succ Γ₁ X) (_           , ts) = getArg X ts

projArgDom : ∀ {Θ} → Args Θ → TyCtxMorP Ø Θ
projArgDom {Ø} a = tt
projArgDom {Γ ∷ Θ} ((A , _) , a) = (Λ A , projArgDom a)

projArgCodom : ∀ {Θ} → Args Θ → TyCtxMorP Ø Θ
projArgCodom {Ø} a = tt
projArgCodom {Γ ∷ Θ} ((_ , _ , B) , a) = (Λ B , projArgDom a)

-- | Extend arguments by the identity on a given type.
extArgs : ∀ {Θ Γ} → Args Θ → PreType Ø Γ Ø → Args (Γ ∷ Θ)
extArgs a A = ((A , varPO zero , A) , a)

-- | Domain of ⟪ A ⟫(φ) for arguments φ : Args Θ.
⟪_⟫₀ : ∀ {Θ Γ₁ Γ₂} →
       PreType Θ Γ₁ Γ₂ → Args Θ → PreType Ø (Γ₂ ++ Γ₁) Ø
⟪_⟫₀ {Γ₁ = Γ₁} {Γ₂} C φ =
  substTy (weakenPT' Γ₂ C) (projArgDom φ) §ₜ ctxProjP' Ø Γ₂ Γ₁

-- | Functorial action of a type A on terms.
-- We are given one term with its types for domain and codomain for each
-- variable in Θ. This is ensured by Args Θ. The result is then a term, which
-- can be thought of as ⟪A⟫(φ) : ⟪A⟫₀(φ) → ⟪A⟫₁(φ).
-- Otherwise, ⟪A⟫ is just defined by induction in A, as in the paper.
-- Note: For now, we have to declare this as non-terminating, as the induction
-- is not obviously terminating for Agda. This should be fixable through sized
-- types.
tyAction : ∀ {Θ Γ₁ Γ₂} →
           (A : Raw Θ Γ₁ Γ₂) → DecentType A → Args Θ → PreTerm (∗ ∷ Γ₂ ++ Γ₁) Ø
tyAction ._ (DT-⊤ Θ Γ)                    ts = varPO zero
tyAction ._ (DT-tyVar Γ₁ X)               ts = weakenPO'' Γ₁ Ø (getArg X ts)
tyAction ._ (DT-inst {Θ} {Γ₁} {Γ₂} {B} A t p q) ts
  = substP (tyAction A p ts) f
  where
    -- | Substitute t for the second variable, i.e., f = (id, t, x).
    f : CtxMorP (∗ ∷ Γ₂ ++ Γ₁) (∗ ∷ Γ₂ ↑ B ++ Γ₁)
    f = subst
        (Vec (PreTerm (∗ ∷ Γ₂ ++ Γ₁) Ø)) -- (CtxMorP (∗ ∷ Γ₂ ++ Γ₁))
        (cong suc r)
        (varPO zero
          ∷ (ctxProjP' [ ∗ ]L Γ₂ Γ₁)
          ++V [ weakenPO' (∗ ∷ Γ₂) (t , q) ]V
          ++V ctxProjP Γ₁ (∗ ∷ Γ₂)
        )
      where
        r : length' Γ₂ + suc (length' Γ₁) ≡ length' (Γ₂ ↑ B ++ Γ₁)
        r =
          begin
            length' Γ₂ + suc (length' Γ₁)
          ≡⟨ refl ⟩
            length' Γ₂ + length' (B ∷ Γ₁)
          ≡⟨ PE.sym (length'-hom Γ₂ (B ∷ Γ₁)) ⟩
            length' (Γ₂ ++ B ∷ Γ₁)
          ≡⟨ mvVar-length Γ₁ Γ₂ B ⟩
            length' (Γ₂ ↑ B ++ Γ₁)
          ∎

tyAction ._ (DT-paramAbstr {Θ} {Γ₂} {B} Γ₁ {A} p) ts =
  subst (λ u → PreTerm u Ø)
        (cong (_∷_ ∗) (mvVar Γ₁ Γ₂ B))
        (tyAction A p ts)

tyAction ._ (DT-fp {Θ} {Γ₂} Γ₁ μ D D-dec) ts
  = weakenPO'' Γ₁ Ø (rec Γ₂ (∗ ∷ Γ₂) (gs D D-dec 0) §ₘ ctxidP (∗ ∷ Γ₂))
  where
    RB : PreType Ø Γ₂ Ø
    RB = subst (λ u → PreType Ø u Ø) (proj₂ identity Γ₂)
               (⟪ fpPT {Θ} {Γ₂} Ø μ (mkFpDataP {D = D} D-dec) ⟫₀ ts)

    -- Construction of gₖ = αₖ id (⟪ Bₖ ⟫ (ts, id))
    mkBase : ∀{Γ'}
             (f : CtxMor Raw Γ' Γ₂) (A : Raw (Γ₂ ∷ Θ) Γ' Ø) →
             DecentCtxMor f →
             DecentType A →
             ℕ →
             Σ RawCtx (λ Γ' →
               PreType [ Γ₂ ]L Γ' Ø
               × CtxMorP Γ' Γ₂
               × PreTerm (∗ ∷ Γ') Ø)
    mkBase {Γ'} g M g-dec M-dec k
      = (Γ' , C , mkCtxMorP g-dec , αₖ §ₘ r)
      where
        A : PreType (Γ₂ ∷ Θ) Γ' Ø
        A = mkPreType M-dec

        αₖ : PreTerm (∗ ∷ Γ') (∗ ∷ Γ')
        αₖ = α _ Γ' ∗ k

        r : CtxMorP (∗ ∷ Γ') (∗ ∷ Γ')
        r = tyAction M M-dec (extArgs ts RB) ∷ ctxProjP Γ' [ ∗ ]L

        C : PreType [ Γ₂ ]L Γ' Ø
        C = substTy A (tyVarPT Ø zero , weakenTyCtxMor₁ Γ₂ (projArgDom ts))

    -- Construct the g₁, ..., gₙ used in the recursion
    gs : (D : FpData Raw Θ Γ₂) → DecentFpData D → ℕ → FpMapDataP Γ₂
    gs [ Γ' , f , M ] (f-dec , M-dec) k
      = [ mkBase f M f-dec M-dec k ]
    gs ((Γ' , f , M) ∷ D) ((f-dec , M-dec) , D-dec) k
      = mkBase f M f-dec M-dec k ∷ gs D D-dec (suc k)

tyAction ._ (DT-fp {Θ} {Γ₂} Γ₁ ν D D-dec) ts
  = weakenPO'' Γ₁ Ø (corec Γ₂ (∗ ∷ Γ₂) (gs D D-dec 0) §ₘ ctxidP (∗ ∷ Γ₂))
  where
    -- Construction of gₖ = αₖ id (⟪ Bₖ ⟫ (ts, id))
    mkBase : ∀{Γ'} (x : CtxMor Raw Γ' Γ₂ × Raw (Γ₂ ∷ Θ) Γ' Ø) →
             (f : DecentCtxMor (proj₁ x)) →
             (q : DecentType (proj₂ x)) →
             ℕ →
             Σ RawCtx (λ Γ' →
               PreType [ Γ₂ ]L Γ' Ø
               × CtxMorP Γ' Γ₂
               × PreTerm (∗ ∷ Γ') Ø)
    mkBase {Γ'} (g , M) g-dec M-dec k = (Γ' , C , mkCtxMorP g-dec , f)
      where
        A : PreType (Γ₂ ∷ Θ) Γ' Ø
        A = mkPreType M-dec

        ξₖ : PreTerm (∗ ∷ Γ') (∗ ∷ Γ')
        ξₖ = ξ _ Γ' ∗ k

        RA : PreType Ø Γ₂ Ø
        RA = subst (λ u → PreType Ø u Ø) (proj₂ identity Γ₂)
             (⟪ fpPT {Θ} {Γ₂} Ø μ (mkFpDataP {D = D} D-dec) ⟫₀ ts)

        f : PreTerm (∗ ∷ Γ') Ø
        f = substPO (tyAction M M-dec (extArgs ts RA))
                    ((ξₖ §ₘ ctxidP (∗ ∷ Γ')) ∷ weakenCtxMorP (ctxidP Γ'))

        C : PreType [ Γ₂ ]L Γ' Ø
        C = substTy A (tyVarPT Ø zero , weakenTyCtxMor₁ Γ₂ (projArgDom ts))

    -- Construct the g₁, ..., gₙ used in the recursion
    gs : (D : FpData Raw Θ Γ₂) → DecentFpData D → ℕ → FpMapDataP Γ₂
    gs [ Γ' , x ] (f , p) k = [ mkBase x f p k ]
    gs ((Γ' , x) ∷ D₁) ((f , q) , p₁) k = mkBase x f q k ∷ gs D₁ p₁ (suc k)


⟪_⟫ : ∀ {Θ Γ₁ Γ₂} →
      PreType Θ Γ₁ Γ₂ → Args Θ → PreTerm (∗ ∷ Γ₂ ++ Γ₁) Ø
⟪ A , A-dec ⟫ = tyAction A A-dec

-----------------------------------------------------
---- Reduction relation on pre-types and pre-terms
-----------------------------------------------------

getRecCtx : ∀{Γ} → (D : FpMapDataP Γ) → Pos D → RawCtx
getRecCtx [ x ]   _       = proj₁ x
getRecCtx (x ∷ D) zero    = proj₁ x
getRecCtx (x ∷ D) (suc p) = getRecCtx D p

getRecMor : ∀{Γ} (D : FpMapDataP Γ) (p : Pos D) →
            PreTerm (∗ ∷ getRecCtx D p) Ø
getRecMor [ Γ' , A , f , t ]      _       = t
getRecMor ((Γ' , A , f , t) ∷ D) zero    = t
getRecMor (x ∷ D)                (suc p) = getRecMor D p

getRecTy : ∀{Γ} (D : FpMapDataP Γ) (p : Pos D) →
           PreType [ Γ ]L (getRecCtx D p) Ø
getRecTy [ x ]   _       = proj₁ (proj₂ x)
getRecTy (x ∷ D) zero    = proj₁ (proj₂ x)
getRecTy (x ∷ D) (suc p) = getRecTy D p

getRecSubst : ∀{Γ} (D : FpMapDataP Γ) (p : Pos D) →
              CtxMorP (getRecCtx D p) Γ
getRecSubst [ Γ' , A , f , t ]     _       = f
getRecSubst ((Γ' , A , f , t) ∷ D) zero    = f
getRecSubst (x ∷ D)                (suc p) = getRecSubst D p


infix 0 _≻_

-- | Contraction for terms
data _≻_  : {Γ₁ Γ₂ : RawCtx} → PreTerm Γ₁ Γ₂ → PreTerm Γ₁ Γ₂ → Set where
  contract-iter : (Γ Δ : RawCtx) (D : FpMapDataP Γ) (C : PreType Ø Ø Γ)
                  (p : Pos D)
                  (τ : CtxMorP Δ (getRecCtx D p))
                  (u : PreTerm Δ Ø) →
                rec Γ Δ D §ₘ
                  (α Δ (getRecCtx D p) ∗ (toℕ p) §ₘ' τ §ₒ u)
                  ∷ getRecSubst D p • τ
                ≻ (getRecMor D p)
                  ↓[ (⟪ getRecTy D p ⟫ (
                        ( fpPT Γ μ (getFpData D) §ₜ ctxidP Γ
                        , rec Γ (∗ ∷ Γ) D §ₘ ctxidP _
                        , (weakenPT'' Γ C) §ₜ ctxidP Γ)
                        , tt))
                     ∷ ctxProjP (getRecCtx D p) [ ∗ ]L ]
                  ↓[ u ∷ τ ]
  contract-coiter : (Γ Δ : RawCtx) (D : FpMapDataP Γ) (C : PreType Ø Ø Γ)
                    (p : Pos D)
                    (τ : CtxMorP Δ (getRecCtx D p))
                    (u : PreTerm Δ Ø) →
                    ξ Δ (getRecCtx D p) ∗ (toℕ p)
                      §ₘ' τ
                      §ₒ corec Γ Δ D §ₘ u ∷ (getRecSubst D p • τ)
                    ≻ (⟪ getRecTy D p ⟫ (
                         (weakenPT'' Γ C §ₜ ctxidP Γ
                         , corec Γ (∗ ∷ Γ) D §ₘ ctxidP _
                         , fpPT Γ ν (getFpData D) §ₜ ctxidP Γ)
                      , tt)
                      ↓[ (getRecMor D p) ∷ ctxProjP (getRecCtx D p) [ ∗ ]L ])
                      ↓[ u ∷ τ ]

-- | Lift term reduction to fixed point data
data _∼>_ : {Γ : RawCtx} → Rel₀ (FpMapDataP Γ)

-- | Compatible closure of contraction
data _⟶_ : {Γ₁ Γ₂ : RawCtx} → Rel₀ (PreTerm Γ₁ Γ₂) where
  contract : {Γ₁ Γ₂ : RawCtx} (t₁ t₂ : PreTerm Γ₁ Γ₂) → t₁ ≻ t₂ → t₁ ⟶ t₂

  inst-clos₁ : ∀ {Γ₁ Γ₂ A} (s₁ s₂ : PreTerm Γ₁ (Γ₂ ↑ A)) (t : PreTerm Γ₁ Ø) →
               s₁ ⟶ s₂ → instPO {Γ₁} {Γ₂} s₁ t ⟶ instPO s₂ t

  inst-clos₂ : ∀ {Γ₁ Γ₂ A} (s : PreTerm Γ₁ (Γ₂ ↑ A)) (t₁ t₂ : PreTerm Γ₁ Ø) →
               t₁ ⟶ t₂ → instPO {Γ₁} {Γ₂} s t₂ ⟶ instPO s t₂

  grec-clos : (Γ : RawCtx) (Δ : RawCtx) (D D' : FpMapDataP Γ) (ρ : FP) →
              D ∼> D' → grec Γ Δ D ρ ⟶ grec Γ Δ D' ρ

data _∼>_ where
  single-clos : {Γ : RawCtx} (Γ' : RawCtx) (A : PreType [ Γ ]L Γ' Ø)
                (f : CtxMorP Γ' Γ) (M₁ M₂ : PreTerm (∗ ∷ Γ') Ø) →
                M₁ ⟶ M₂ → [ Γ' , A , f , M₁ ] ∼> [ Γ' , A , f , M₂ ]

  step-clos₁ : {Γ : RawCtx} (Γ' : RawCtx) (A : PreType [ Γ ]L Γ' Ø)
               (f : CtxMorP Γ' Γ) (M₁ M₂ : PreTerm (∗ ∷ Γ') Ø)
               (D : FpMapDataP Γ) →
               M₁ ⟶ M₂ → ((Γ' , A , f , M₁) ∷ D) ∼> ((Γ' , A , f , M₂) ∷ D)

  step-clos₂ : {Γ : RawCtx} (Γ' : RawCtx) (A : PreType [ Γ ]L Γ' Ø)
               (f : CtxMorP Γ' Γ) (M : PreTerm (∗ ∷ Γ') Ø)
               (D₁ D₂ : FpMapDataP Γ) →
               D₁ ∼> D₂ → ((Γ' , A , f , M) ∷ D₁) ∼> ((Γ' , A , f , M) ∷ D₂)

-- | β-reduction for parameter abstraction/instantiation
data _⟶ₚ_ : {Θ : TyCtx} {Γ₁ Γ₂ : RawCtx} → Rel₀ (PreType Θ Γ₁ Γ₂) where
     β-red : {Θ : TyCtx} {Γ₂ : RawCtx} (Γ₁ : RawCtx) {A : U}
             (B : PreType Θ (A ∷ Γ₁) Γ₂) (t : PreTerm Γ₁ Ø) →
             instPT (paramAbstrPT Γ₁ B) t ⟶ₚ substPT B (t ∷ (ctxidP Γ₁))

-- | Lift type reductions to fixed point data
data _∼>ₜ_ : {Θ : TyCtx} {Γ : RawCtx} → Rel₀ (FpDataP Θ Γ)

-- | Reduction on types. This is either a β-reduction for parameters,
-- a reduction of a term in parameter position, or it happens through
-- the compatible closure.
data _⟶ₜ_ : {Θ : TyCtx} {Γ₁ Γ₂ : RawCtx} → Rel₀ (PreType Θ Γ₁ Γ₂) where
     param-conv : ∀ {Θ Γ₁ Γ₂ A}
                  (B : PreType Θ Γ₁ (Γ₂ ↑ A)) (t₁ t₂ : PreTerm Γ₁ Ø) →
                  t₁ ⟶ t₂ → instPT {Γ₂ = Γ₂} B t₁ ⟶ₜ instPT B t₂

     inst-conv : {Θ : TyCtx} {Γ₁ Γ₂ : RawCtx} → (A₁ A₂ : PreType Θ Γ₁ Γ₂) →
                 A₁ ⟶ₚ A₂ → A₁ ⟶ₜ A₂

     instPT-clos : ∀ {Θ Γ₁ Γ₂ A}
                  (B₁ B₂ : PreType Θ Γ₁ (Γ₂ ↑ A)) (t : PreTerm Γ₁ Ø) →
                  B₁ ⟶ₜ B₂ → instPT {Γ₂ = Γ₂} B₁ t ⟶ₜ instPT B₂ t

     paramAbstr-clos : {Θ : TyCtx} {Γ₂ : RawCtx} (Γ₁ : RawCtx) {A : U} →
                       (B₁ B₂ : PreType Θ (A ∷ Γ₁) Γ₂) →
                       B₁ ⟶ₜ B₂ → paramAbstrPT Γ₁ B₁ ⟶ₜ paramAbstrPT Γ₁ B₂

     fp-clos : {Θ : TyCtx} {Γ₂ : RawCtx} (Γ₁ : RawCtx) →
               (ρ : FP) (D₁ D₂ : FpDataP Θ Γ₂) →
               D₁ ∼>ₜ D₂ → fpPT Γ₁ ρ D₁ ⟶ₜ fpPT Γ₁ ρ D₂

data _∼>ₜ_ where
  singlePT-clos : {Θ : TyCtx} {Γ : RawCtx}
    (Γ' : RawCtx) (f : CtxMorP Γ' Γ) (A₁ A₂ : PreType (Γ ∷ Θ) Γ' Ø) →
    A₁ ⟶ₜ A₂ → [ Γ' , f , A₁ ] ∼>ₜ [ Γ' , f , A₂ ]

  stepPT-clos₁ : {Θ : TyCtx} {Γ : RawCtx}
    (Γ' : RawCtx) (f : CtxMorP Γ' Γ) (A₁ A₂ : PreType (Γ ∷ Θ) Γ' Ø)
    (D : FpDataP Θ Γ) →
    A₁ ⟶ₜ A₂ -> ((Γ' , f , A₁) ∷ D) ∼>ₜ ((Γ' , f , A₂) ∷ D)

  stepPT-clos₂ : {Θ : TyCtx} {Γ : RawCtx}
    (Γ' : RawCtx) (f : CtxMorP Γ' Γ) (A : PreType (Γ ∷ Θ) Γ' Ø)
    (D₁ D₂ : FpDataP Θ Γ) →
    D₁ ∼>ₜ D₂ -> ((Γ' , f , A) ∷ D₁) ∼>ₜ ((Γ' , f , A) ∷ D₂)
