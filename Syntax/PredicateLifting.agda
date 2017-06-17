module PredicateLifting where

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

open import Common.Context as Context

open import Algebra
open Monoid {{ ... }} hiding (refl)

open import SyntaxRaw
open import Syntax

-- | Extend the parameter context of each type variable in the given
-- type context by one extra variable. We need this to specify the new
-- type variable context, in which the predicate lifting of a type lives.
-- See predL below for the correspond typing rule.
liftTyCtx : ∀ {Θ} → TyCtxMorP Ø Θ → TyCtx
liftTyCtx {Ø}     f       = Ø
liftTyCtx {Γ ∷ Θ} (A , f) = (∗ ∷ Γ) ∷ liftTyCtx f

-- | Extend a parameter context by a variable of the given type.
extTyVarParams : (Γ₂ : RawCtx) → PreType Ø Ø Γ₂ → RawCtx
extTyVarParams Γ₂ A = ∗ ∷ Γ₂

-- | Get the Yᵢ : (Γᵢ, xᵢ : Bᵢ) ⊸ ∗ corresponding to Xᵢ : Γᵢ ⊸ ∗ in
-- the lifted context, c.f. the typing rule for predL below.
liftTyVar : ∀{Θ Γ₂} → (f : TyCtxMorP Ø Θ) (X : TyVar Θ Γ₂) →
            TyVar (liftTyCtx f) (extTyVarParams Γ₂ (getTy f X))
liftTyVar f       zero       = zero
liftTyVar (A , f) (succ Γ X) =
  succ (extTyVarParams Γ (getTy f X)) (liftTyVar f X)

-- | Turn an instantiation into a substitution.
instToSubst : ∀{Γ₁} (A : U) (Γ₂ : RawCtx) → PreTerm Γ₁ Ø →
              CtxMorP (∗ ∷ Γ₂ ++ Γ₁) (∗ ∷ (Γ₂ ↑ A) ++ Γ₁)
instToSubst {Γ₁} A Γ₂ t =
  let f = weakenPO' (∗ ∷ Γ₂) t ∷ ctxProjP Γ₁ (∗ ∷ Γ₂)
  in subst (CtxMorP (∗ ∷ Γ₂ ++ Γ₁))
           (PE.sym (cong (_∷_ ∗ ) (assoc Γ₂ (A ∷ Ø) Γ₁)))
           (extendProj (∗ ∷ Γ₂) Ø f)

-- | Auxiliary function to define predL below.
predL₀ : ∀ {Θ Γ₁ Γ₂} →
         (A : Raw Θ Γ₁ Γ₂) → DecentType A → (f : TyCtxMorP Ø Θ) →
         liftTyCtx f ∣ ∗ ∷ Γ₂ ++ Γ₁ / Ø ⊸Ty
predL₀ ._ (DT-⊤ Θ Γ)                                 f =
  ⊤-PT (liftTyCtx f) (∗ ∷ Ø ++ Γ)
predL₀ ._ (DT-tyVar Γ₁ X)                            f =
  tyVarPT _ (liftTyVar f X) §ₜ ctxProjP' Ø _ Γ₁
predL₀ ._ (DT-inst {Γ₂ = Γ₂} B t B-dec t-dec)        f =
  let B' = predL₀ B B-dec f
  in substPT B' (instToSubst _ Γ₂ (mkPreTerm t-dec))
predL₀ ._ (DT-paramAbstr {Γ₂ = Γ₂} {B = B} Γ₁ A-dec) f =
  subst (λ u → PreType (liftTyCtx f) u Ø)
        (cong (_∷_ ∗) (PE.sym (assoc Γ₂ (B ∷ Ø) Γ₁)))
        (predL₀ _ A-dec f)
predL₀ {Θ} {.Γ₁} {Γ₂} ._ (DT-fp Γ₁ ρ D p)            f =
  fpPT (∗ ∷ Γ₂ ++ Γ₁) ρ (mkD' D p 0) §ₜ f'
  where
    f' : CtxMorP (∗ ∷ Γ₂ ++ Γ₁) (∗ ∷ Γ₂)
    f' = extendP ∗ (ctxProjP' Ø Γ₂ Γ₁)

    mkD' : (D : FpData Raw Θ Γ₂) → DecentFpData D → ℕ →
           FpDataP (liftTyCtx f) (∗ ∷ Γ₂)
    mkD' [ Γ , g , A ] (g-dec , A-dec) k =
      let A' = predL₀ A A-dec (substTy (fpPT Ø ρ (mkFpDataP {D = D} p)) f , f)
      in
        [ ( (∗ ∷ Γ)
          , (α (∗ ∷ Γ) Γ ∗ k §ₘ ctxidP (∗ ∷ Γ))
            ∷ (mkCtxMorP {Γ} {Γ₂} {g} g-dec • ctxProjP Γ (∗ ∷ Ø))
          , A' ) ]
    mkD' ((Γ , g , A) ∷ D₁) ((g-dec , A-dec) , q) k =
      let A' = predL₀ A A-dec (substTy (fpPT Ø ρ (mkFpDataP {D = D} p)) f , f)
      in ( ∗ ∷ Γ
          , (α (∗ ∷ Γ) Γ ∗ k §ₘ ctxidP (∗ ∷ Γ))
            ∷ (mkCtxMorP {Γ} {Γ₂} {g} g-dec • ctxProjP Γ (∗ ∷ Ø))
          , A' )
         ∷ mkD' D₁ q (suc k)

-- | Lift an open type A to predicates. More specifically, predL
-- implements the following rule, in which we write Ā for predL A.
--   X₁ : Δ₁ ⊸ Ty, ..., Xₙ : Δₙ ⊸ Ty | Γ₁ ⊢ A : Γ₂ ⊸ Ty
--   B₁ : Δ₁ ⊸ Ty
--   ...
--   Bₙ : Δ₁ ⊸ Ty
--  ================================================================= (predL)
--   Y₁ : (Δ₁, x₁ : B₁ ⊙ id) ⊸ Ty, ..., (Yₙ : Δₙ, xₙ : Bₙ ⊙ id) ⊸ Ty
--     | Γ₁, Γ₂, z : A[B₁/X₁, ..., Bₙ/Xₙ] ⊙ id
--     ⊢ Ā : Ty
predL : ∀ {Θ Γ₁ Γ₂} →
        PreType Θ Γ₁ Γ₂ →
        (f : TyCtxMorP Ø Θ) →
--      ===========================================================
        liftTyCtx f ∣ ∗ ∷ Γ₂ ++ Γ₁ / Ø ⊸Ty
predL (A , A-dec) = predL₀ A A-dec

-- | Special instance of the predicate lifting for types with one
-- free variable and no parameters.
--           X : Δ ⊸ Ty | Γ ⊢ A : Ty           B : Δ ⊸ Ty
--  =============================================================== (predL₁)
--     Y : (Δ, x : B ⊙ id) ⊸ ∗ | Γ, z : A[B/X] ⊢ Ā : Ty
predL₁ : ∀ {Δ Γ} →
        ((Δ ∷ Ø) ∣ Γ / Ø ⊸Ty) → (Ø ∣ Ø / Δ ⊸Ty) →
--      ===========================================================
        ((∗ ∷ Δ) ∷ Ø) ∣ ∗ ∷ Γ / Ø ⊸Ty
predL₁ A B = predL A (B , tt)
