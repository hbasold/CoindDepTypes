module Syntax where

import Level
open import Data.Empty
open import Data.Unit as Unit
open import Data.Nat
open import Data.List as List renaming ([] to Ø; [_] to [_]L)
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

open import SyntaxRaw

infixr 5 _§ₒ_ _§ₘ_

-----------------------------------------
--- Separate types and terms
-----------------------------------------

mutual
  data DecentType : {Θ : TyCtx} {Γ₁ Γ₂ : RawCtx} → Raw Θ Γ₁ Γ₂ → Set where
    DT-⊤ : (Θ : TyCtx) (Γ : RawCtx) → DecentType (⊤-Raw Θ Γ)
    DT-tyVar : {Θ : TyCtx} (Γ₁ : RawCtx) {Γ₂ : RawCtx} →
               (X : TyVar Θ Γ₂) → DecentType (tyVarRaw Γ₁ X)
    DT-inst : ∀{Θ Γ₁ Γ₂ A} →
              (B : Raw Θ Γ₁ (Γ₂ ↑ A)) → (t : Raw Ø Γ₁ Ø) →
              DecentType B → DecentTerm t →
              DecentType (instRaw {Γ₂ = Γ₂} B t)
    DT-paramAbstr : ∀{Θ Γ₂} {B : U} (Γ₁ : RawCtx) →
                    {A : Raw Θ (B ∷ Γ₁) Γ₂} →
                    DecentType A →
                    DecentType (paramAbstrRaw Γ₁ A)
    DT-fp : ∀{Θ Γ₂} (Γ₁ : RawCtx) →
            (ρ : FP) → (D : FpData Raw Θ Γ₂) →
            DecentFpData D →
            DecentType (fpRaw Γ₁ ρ D)

  data DecentTerm : {Γ₁ Γ₂ : RawCtx} → Raw Ø Γ₁ Γ₂ → Set where
    DO-unit : (Γ : RawCtx) → DecentTerm (unitRaw Γ)
    DO-objVar : {Γ : RawCtx} {A : U} →
                (x : RawVar Γ A) → DecentTerm (objVarRaw x)
    DO-inst : {Γ₁ Γ₂ : RawCtx} {A : U} →
              (t : Raw Ø Γ₁ (Γ₂ ↑ A)) → (s : Raw Ø Γ₁ Ø) →
              DecentTerm t → DecentTerm s →
              DecentTerm (instRaw {Γ₂ = Γ₂} t s)
    DO-dialg : (Δ : RawCtx) (Γ : RawCtx) (A : U) →
               (ρ : FP) (k : ℕ) →
               DecentTerm (dialgRaw Δ Γ A ρ k)
    DO-mapping : (Γ : RawCtx) (Δ : RawCtx) →
                 (gs : FpMapData Raw Γ) → (ρ : FP) →
                 DecentFpMapData gs →
                 DecentTerm (recRaw Γ Δ gs ρ)

  DecentFpMapData : {Γ : RawCtx} → FpMapData Raw Γ → Set
  DecentFpMapData [ (Γ' , A , f , t) ] =
    DecentType A × DecentCtxMor f × DecentTerm t
  DecentFpMapData ((Γ' , A , f , t) ∷ ts) =
    DecentType A × DecentCtxMor f × DecentTerm t × DecentFpMapData ts

  DecentCtxMor : {Γ₁ Γ₂ : RawCtx} → CtxMor Raw Γ₁ Γ₂ → Set
  DecentCtxMor {Γ₂ = Ø}      []      = ⊤
  DecentCtxMor {Γ₂ = x ∷ Γ₂} (t ∷ f) = DecentTerm t × DecentCtxMor f

  DecentFpData : ∀{Θ Γ₂} → FpData Raw Θ Γ₂ → Set
  DecentFpData [ Γ , f , A ] = DecentCtxMor f × DecentType A
  DecentFpData ((Γ , f , A) ∷ D)
    = (DecentCtxMor f × DecentType A) × DecentFpData D

{-
DT-syntax : (Θ : TyCtx) (Γ₁ Γ₂ : RawCtx) → Raw Θ Γ₁ Γ₂ → Set
DT-syntax _ _ _ A = DecentType A

syntax DT-syntax Θ Γ₁ Γ₁ A = Θ ∥ Γ₁ ⊨ A ε Γ₂ ━

DO-syntax : (Γ₁ Γ₂ : RawCtx) → Raw Ø Γ₁ Γ₂ → Set
DO-syntax _ _ t = DecentTerm t

syntax DO-syntax Γ₁ Γ₂ t = Γ₁ ⊢ t ∈ Γ₂ ⊸?
-}


-------------------------------------
------- Pre-types and terms
-------------------------------------


PreType : (Θ : TyCtx) (Γ₁ Γ₂ : RawCtx) → Set
PreType Θ Γ₁ Γ₂ = Σ (Raw Θ Γ₁ Γ₂) λ A → DecentType A

_∣_/_⊸Ty = PreType


mkPreType : ∀ {Θ Γ₁ Γ₂} {A : Raw Θ Γ₁ Γ₂} → DecentType A → PreType Θ Γ₁ Γ₂
mkPreType {A = A} p = (A , p)

PreTerm : (Γ₁ Γ₂ : RawCtx) → Set
PreTerm Γ₁ Γ₂ = Σ (Raw Ø Γ₁ Γ₂) λ t → DecentTerm t

mkPreTerm : ∀ {Γ₁ Γ₂} {t : Raw Ø Γ₁ Γ₂} → DecentTerm t → PreTerm Γ₁ Γ₂
mkPreTerm {t = t} p = (t , p)

CtxMorP = CtxMor (λ _ → PreTerm)

mkCtxMorP : {Γ₁ Γ₂ : RawCtx} {f : CtxMor Raw Γ₁ Γ₂} →
             DecentCtxMor f → CtxMorP Γ₁ Γ₂
mkCtxMorP {Γ₂ = Ø}              p        = []
mkCtxMorP {Γ₂ = x ∷ Γ₂} {t ∷ f} (p , ps) = (t , p) ∷ (mkCtxMorP ps)

TyCtxMorP : TyCtx → TyCtx → Set
TyCtxMorP Θ₁ Ø = ⊤
TyCtxMorP Θ₁ (Γ ∷ Θ₂) = PreType Θ₁ Ø Γ × TyCtxMorP Θ₁ Θ₂

FpDataP : TyCtx → RawCtx → Set
FpDataP Θ Γ = NList (Σ RawCtx (λ Γ' → CtxMorP Γ' Γ × PreType (Γ ∷ Θ) Γ' Ø))

mkFpDataP : ∀ {Θ Γ} {D : FpData Raw Θ Γ} → DecentFpData D → FpDataP Θ Γ
mkFpDataP {D = [ Γ , f , A ]} (p , q) = [ Γ , (mkCtxMorP p) , mkPreType q ]
mkFpDataP {D = (Γ , f , A) ∷ D} ((p , q) , r) =
  (Γ , mkCtxMorP p , mkPreType q) ∷ mkFpDataP {D = D} r

-- | List of types, context morphisms and terms (Aₖ, fₖ, gₖ) such that
--            Γₖ, x : Aₖ[C/X] ⊢ gₖ : C fₖ or
--            Γₖ, x : C fₖ ⊢ gₖ : Aₖ[C/X],
-- which are the premisses of the rule for recursion and corecursion,
-- respectively.
FpMapDataP : RawCtx → Set
FpMapDataP Γ = NList (Σ RawCtx λ Γ' →
                        PreType [ Γ ]L Γ' Ø × CtxMorP Γ' Γ × PreTerm (∗ ∷ Γ') Ø)

mkFpMapDataP : ∀{Γ} {gs : FpMapData Raw Γ} → DecentFpMapData gs → FpMapDataP Γ
mkFpMapDataP {Γ} {[ Γ' , A , f , t ]} (A-decent , f-decent , t-decent) =
  [ Γ' , mkPreType A-decent , mkCtxMorP f-decent , mkPreTerm t-decent ]
mkFpMapDataP {Γ} {(Γ' , A , f , t) ∷ gs} (A-decent , f-decent , t-decent , r) =
  (Γ' , mkPreType A-decent , mkCtxMorP f-decent , mkPreTerm t-decent)
  ∷ mkFpMapDataP {Γ} {gs} r

getFpData : ∀{Γ} → FpMapDataP Γ → FpDataP Ø Γ
getFpData [ Γ' , A , f , _ ]     = [ Γ' , f , A ]
getFpData ((Γ' , A , f , _) ∷ d) = (Γ' , f , A) ∷ getFpData d

projCtxMor₁ : {Γ₁ Γ₂ : RawCtx} → CtxMorP Γ₂ Γ₁ → CtxMor Raw Γ₂ Γ₁
projCtxMor₁ = Vec.map proj₁

projCtxMor₂ : {Γ₁ Γ₂ : RawCtx} →
              (f : CtxMorP Γ₂ Γ₁) →  DecentCtxMor (projCtxMor₁ f)
projCtxMor₂ {Ø} [] = tt
projCtxMor₂ {x ∷ Γ₁} ((t , p) ∷ f) = (p , projCtxMor₂ f)

projPTList₁ : ∀{Γ} → FpMapDataP Γ → FpMapData Raw Γ
projPTList₁ =
  NList.map (Prod.map id (Prod.map proj₁ (Prod.map projCtxMor₁ proj₁)))

projPTList₂ : ∀{Γ} → (gs : FpMapDataP Γ) → DecentFpMapData (projPTList₁ gs)
projPTList₂ [ (Γ' , A , f , t) ] = (proj₂ A , projCtxMor₂ f , proj₂ t)
projPTList₂ ((Γ' , A , f , t) ∷ gs) =
  (proj₂ A , projCtxMor₂ f , proj₂ t , projPTList₂ gs)

projFpData₁ : ∀ {Θ Γ} → FpDataP Θ Γ → FpData Raw Θ Γ
projFpData₁ = NList.map (Prod.map id (Prod.map projCtxMor₁ proj₁))

projFpData₂ : ∀ {Θ Γ} → (D : FpDataP Θ Γ) → DecentFpData (projFpData₁ D)
projFpData₂ [ (Γ , f , A) ] = (projCtxMor₂ f , proj₂ A)
projFpData₂ ((Γ , f , A) ∷ D) = ((projCtxMor₂ f , proj₂ A) , projFpData₂ D)

-----------------------------------------
----- Constructors for pre terms
-----------------------------------------

⊤-PT : (Θ : TyCtx) (Γ : RawCtx) → PreType Θ Γ Ø
⊤-PT Θ Γ = mkPreType (DT-⊤ Θ Γ)

instPT : ∀ {Θ Γ₁ Γ₂ A} → PreType Θ Γ₁ (Γ₂ ↑ A) → PreTerm Γ₁ Ø → PreType Θ Γ₁ Γ₂
instPT (B , p) (t , q) = mkPreType (DT-inst _ _ p q)

_⊙_ = instPT

tyVarPT : {Θ : TyCtx} (Γ₁ : RawCtx) {Γ₂ : RawCtx} → TyVar Θ Γ₂ → PreType Θ Γ₁ Γ₂
tyVarPT Γ₁ X = mkPreType (DT-tyVar _ X)

paramAbstrPT : {Θ : TyCtx} {Γ₂ : RawCtx} (Γ₁ : RawCtx) {A : U} →
               PreType Θ (A ∷ Γ₁) Γ₂ → PreType Θ Γ₁ (Γ₂ ↑ A)
paramAbstrPT Γ₁ (A , p) = mkPreType (DT-paramAbstr Γ₁ p)

fpPT : {Θ : TyCtx} {Γ₂ : RawCtx} (Γ₁ : RawCtx) →
       FP → FpDataP Θ Γ₂ → PreType Θ Γ₁ Γ₂
fpPT Γ₁ ρ D = mkPreType (DT-fp Γ₁ ρ (projFpData₁ D) (projFpData₂ D))

unitPO : (Γ : RawCtx) → PreTerm Γ Ø
unitPO Γ = mkPreTerm (DO-unit _)

varPO : {Γ : RawCtx} {A : U} → RawVar Γ A → PreTerm Γ Ø
varPO x = mkPreTerm (DO-objVar x)

instPO : ∀ {Γ₁ Γ₂ A} → PreTerm Γ₁ (Γ₂ ↑ A) → PreTerm Γ₁ Ø → PreTerm Γ₁ Γ₂
instPO (t , p) (s , q) = mkPreTerm (DO-inst _ _ p q)

_§ₒ_ = instPO

dialgPO : (Δ : RawCtx) (Γ : RawCtx) (A : U) → FP → ℕ → PreTerm Δ (A ∷ Γ)
dialgPO Δ Γ A ρ k = mkPreTerm (DO-dialg _ Γ A ρ k)

α : (Δ : RawCtx) (Γ : RawCtx) (A : U) → ℕ → PreTerm Δ (A ∷ Γ)
α Δ Γ A k = dialgPO Δ Γ A μ k

ξ : (Δ : RawCtx) (Γ : RawCtx) (A : U) → ℕ → PreTerm Δ (A ∷ Γ)
ξ Δ Γ A k = dialgPO Δ Γ A ν k

-- | Generalised recursion, does recursion or corecursion, depending on ρ
grec : (Γ : RawCtx) (Δ : RawCtx) →
       FpMapDataP Γ → FP → PreTerm Δ (∗ ∷ Γ)
grec Γ Δ gs ρ = mkPreTerm (DO-mapping Γ Δ (projPTList₁ gs) ρ (projPTList₂ gs))

-- | Recursion for inductive types
rec : (Γ : RawCtx) (Δ : RawCtx) →
      FpMapDataP Γ → PreTerm Δ (∗ ∷ Γ)
rec Γ Δ gs = grec Γ Δ gs μ

-- Corecursion
corec : (Γ : RawCtx) (Δ : RawCtx) →
        FpMapDataP Γ → PreTerm Δ (∗ ∷ Γ)
corec Γ Δ gs = grec Γ Δ gs ν


instWCtxMorP : {Γ₁ Γ₂ Γ₃ : RawCtx} →
               PreTerm Γ₁ (Γ₃ ++ Γ₂) → CtxMorP Γ₁ Γ₂ → PreTerm Γ₁ Γ₃
instWCtxMorP {Γ₁} {Ø}      {Γ₃} t [] = subst (PreTerm Γ₁) (proj₂ identity Γ₃) t
instWCtxMorP {Γ₁} {x ∷ Γ₂} {Γ₃} t (s ∷ f) =
  instPO
    (instWCtxMorP {Γ₂ = Γ₂} {Γ₃ = Γ₃ ↑ x}
      (subst (PreTerm Γ₁) (mvVar _ Γ₃ x) t) f)
    s

_§ₘ'_ = instWCtxMorP

_§ₘ_ : {Γ₁ Γ₂ : RawCtx} →
       PreTerm Γ₁ Γ₂ → CtxMorP Γ₁ Γ₂ → PreTerm Γ₁ Ø
t §ₘ f = instWCtxMorP {Γ₃ = Ø} t f

instTyWCtxMorP : ∀ {Θ Γ₁ Γ₂ Γ₃} →
                 PreType Θ Γ₁ (Γ₃ ++ Γ₂) → CtxMorP Γ₁ Γ₂ → PreType Θ Γ₁ Γ₃
instTyWCtxMorP {Θ} {Γ₁} {Ø}      {Γ₃} A [] =
  subst (PreType Θ Γ₁) (proj₂ identity Γ₃) A
instTyWCtxMorP {Θ} {Γ₁} {x ∷ Γ₂} {Γ₃} A (s ∷ f) =
  (instTyWCtxMorP (subst (PreType Θ Γ₁) (mvVar _ Γ₃ x) A) f) ⊙ s

_§ₜ_ : ∀ {Θ Γ₁ Γ₂} →
       PreType Θ Γ₁ Γ₂ → CtxMorP Γ₁ Γ₂ → PreType Θ Γ₁ Ø
A §ₜ f = instTyWCtxMorP {Γ₃ = Ø} A f


---------------------------------------------------------
--------- Recursion for pre-types
---------------------------------------------------------

FpDataP' : (TyCtx → RawCtx → RawCtx → Set) → TyCtx → RawCtx → Set
FpDataP' V Θ Γ = NList (Σ RawCtx (λ Γ' → CtxMorP Γ' Γ × V (Γ ∷ Θ) Γ' Ø))

{-# NON_TERMINATING #-}
mapPT : {V : TyCtx → RawCtx → RawCtx → Set} →
        ((Θ : TyCtx) (Γ₁ : RawCtx) → V Θ Γ₁ Ø) →
        (∀{Θ Γ₁ Γ₂} → TyVar Θ Γ₂ → V Θ Γ₁ Γ₂) →
        (∀{Θ Γ₁ Γ₂ A} → V Θ Γ₁ (Γ₂ ↑ A) → PreTerm Γ₁ Ø → V Θ Γ₁ Γ₂) →
        (∀{Θ Γ₁ Γ₂ A} → V Θ (A ∷ Γ₁) Γ₂ → V Θ Γ₁ (Γ₂ ↑ A)) →
        (∀{Θ Γ₁ Γ₂} → FP → FpDataP' V Θ Γ₂ → V Θ Γ₁ Γ₂) →
        ∀{Θ Γ₁ Γ₂} → PreType Θ Γ₁ Γ₂ → V Θ Γ₁ Γ₂
mapPT ⊤-x _ _ _ _ (._ , DT-⊤ Θ Γ) = ⊤-x Θ Γ
mapPT _ var-x _ _ _ (._ , DT-tyVar Γ₁ X) = var-x X
mapPT ⊤-x var-x inst-x abstr-x fp-x (._ , DT-inst B t B-dec t-dec) =
  let r = mapPT ⊤-x var-x inst-x abstr-x fp-x (B , B-dec)
  in inst-x r (t , t-dec)
mapPT ⊤-x var-x inst-x abstr-x fp-x (._ , DT-paramAbstr Γ₁ {A} A-dec) =
  let r = mapPT ⊤-x var-x inst-x abstr-x fp-x (A , A-dec)
  in abstr-x r
mapPT ⊤-x var-x inst-x abstr-x fp-x (._ , DT-fp Γ₁ ρ D D-dec) =
  let D' = NList.map
           (Prod.map id
             (Prod.map id
               (mapPT ⊤-x var-x inst-x abstr-x fp-x))) (mkFpDataP {D = D} D-dec)
  in fp-x ρ D'


----------------------------------------------------------
--------- Meta theory for decent type predicate
---------------------------------------------------------

weakenDO : (Γ₁ : RawCtx) → {Γ₂ Γ₃ : RawCtx} {t : Raw Ø (Γ₁ ++ Γ₂) Γ₃} →
           (A : U) → DecentTerm t → DecentTerm (weaken Γ₁ A t)
weakenDO Γ₁ B (DO-unit ._)             = DO-unit _
weakenDO Γ₁ B (DO-objVar x)            = DO-objVar (weakenObjVar Γ₁ B x)
weakenDO Γ₁ B (DO-inst t s p q)        =
  DO-inst _ _ (weakenDO Γ₁ B p) (weakenDO Γ₁ B q)
weakenDO Γ₁ B (DO-dialg ._ Γ A ρ k)    = DO-dialg _ _ A ρ k
weakenDO Γ₁ B (DO-mapping Γ ._ gs ρ p) = DO-mapping Γ _ gs ρ p

weakenDT : ∀ {Θ} → (Γ₁ : RawCtx) → {Γ₂ Γ₃ : RawCtx} {A : Raw Θ (Γ₁ ++ Γ₂) Γ₃} →
           (B : U) → DecentType A → DecentType (weaken Γ₁ B A)
weakenDT Γ₁ B (DT-⊤ Θ ._)           = DT-⊤ Θ _
weakenDT Γ₁ B (DT-tyVar _ X)        = DT-tyVar _ X
weakenDT Γ₁ B (DT-inst A t p q)     =
  DT-inst _ _ (weakenDT Γ₁ B p) (weakenDO Γ₁ B q)
weakenDT Γ₁ B (DT-paramAbstr _ p)   = DT-paramAbstr _ (weakenDT _ B p)
weakenDT Γ₁ B (DT-fp _ ρ D p)       = DT-fp _ ρ D p

weakenDO₁ : ∀ {Γ₁ Γ₂} {t : Raw Ø Γ₁ Γ₂} →
            (A : U) → DecentTerm t → DecentTerm (weaken₁ A t)
weakenDO₁ = weakenDO Ø

weakenDT₁ : ∀ {Θ Γ₁ Γ₂} {A : Raw Θ Γ₁ Γ₂} →
            (B : U) → DecentType A → DecentType (weaken₁ B A)
weakenDT₁ = weakenDT Ø

weakenDecentCtxMor : {Γ₁ Γ₂ : RawCtx} {f : CtxMor Raw Γ₁ Γ₂} →
                     (A : U) → DecentCtxMor f →
                     DecentCtxMor (Vec.map (weaken₁ A) f)
weakenDecentCtxMor {Γ₂ = Ø}      {[]}    A p        = tt
weakenDecentCtxMor {Γ₂ = x ∷ Γ₂} {t ∷ f} A (p , ps) =
  (weakenDO₁ A p , weakenDecentCtxMor A ps)

weakenCtxMorP : {Γ₁ Γ₂ : RawCtx} → CtxMorP Γ₁ Γ₂ → CtxMorP (∗ ∷ Γ₁) Γ₂
weakenCtxMorP f = mkCtxMorP (weakenDecentCtxMor ∗ (projCtxMor₂ f))

-----------------------------------------------------
------ Meta operations on pre-terms and pre-types
-----------------------------------------------------

weakenPT : {Θ : TyCtx} (Γ₁ : RawCtx) {Γ₂ Γ₃ : RawCtx} →
           (A : U) → PreType Θ (Γ₁ ++ Γ₂) Γ₃ → PreType Θ (Γ₁ ++ A ∷ Γ₂) Γ₃
weakenPT Γ₁ A (B , p) = (_ , weakenDT Γ₁ A p)

weakenPT₁ : ∀ {Θ Γ₁ Γ₂} → (A : U) → PreType Θ Γ₁ Γ₂ → PreType Θ (A ∷ Γ₁) Γ₂
weakenPT₁ = weakenPT Ø

weakenPO : (Γ₁ : RawCtx) {Γ₂ Γ₃ : RawCtx} →
           (A : U) → PreTerm (Γ₁ ++ Γ₂) Γ₃ → PreTerm (Γ₁ ++ A ∷ Γ₂) Γ₃
weakenPO Γ₁ A (t , p) = (_ , weakenDO Γ₁ A p)

weakenPO₁ : {Γ₁ Γ₂ : RawCtx} → (A : U) → PreTerm Γ₁ Γ₂ → PreTerm (A ∷ Γ₁) Γ₂
weakenPO₁ = weakenPO Ø

get' : {Γ₁ Γ₂ : RawCtx} {A : U} →
       (f : CtxMor (λ _ → PreTerm) Γ₂ Γ₁) →
       (x : RawVar Γ₁ A) →
       DecentTerm (get {Raw} (projCtxMor₁ f) x)
get' (t ∷ f) zero                = proj₂ t
get' (t ∷ f) (succ {b = _} _ x)  = get' f x

-- | Lift substitutions to DecentTerm predicate
substDO : {Γ₁ Γ Γ₂ : RawCtx} {t : Raw Ø Γ₁ Γ} →
          (f : CtxMorP Γ₂ Γ₁) →
          DecentTerm t → DecentTerm (substRaw t (projCtxMor₁ f))
substDO f (DO-unit Γ₁)              = DO-unit _
substDO f (DO-objVar x)             = get' f x
substDO f (DO-inst t s p q)         = DO-inst _ _ (substDO f p) (substDO f q)
substDO f (DO-dialg Γ₁ Γ A ρ k)     = DO-dialg _ _ A ρ k
substDO f (DO-mapping Γ Γ₁ gs ρ p)  = DO-mapping Γ _ _ _ p

-- | Lift substRaw to pre terms
substP : {Γ₁ Γ Γ₂ : RawCtx} →
         PreTerm Γ₁ Γ → CtxMorP Γ₂ Γ₁ → PreTerm Γ₂ Γ
substP (t , p) f = (substRaw t (projCtxMor₁ f) , substDO f p)

_↓[_] = substP

-- | Context identity is a decent context morphism
ctxidDO : (Γ : RawCtx) → DecentCtxMor (ctxid Γ)
ctxidDO Ø       = tt
ctxidDO (x ∷ Γ) = (DO-objVar zero , weakenDecentCtxMor _ (ctxidDO Γ))

mkCtxMorP₁ : {Γ₁ Γ₂ : RawCtx} {f : CtxMor Raw Γ₁ Γ₂} →
             (p : DecentCtxMor f) → projCtxMor₁ (mkCtxMorP p) ≡ f
mkCtxMorP₁ {Γ₂ = Ø}      {[]} p = refl
mkCtxMorP₁ {Γ₂ = A ∷ Γ₂} {t ∷ f} (p , ps) =
  begin
    projCtxMor₁ {A ∷ Γ₂} ((t , p) ∷ mkCtxMorP ps)
  ≡⟨ refl ⟩
    t ∷ projCtxMor₁ (mkCtxMorP ps)
  ≡⟨ cong (λ u → t ∷ u) (mkCtxMorP₁ ps) ⟩
    t ∷ f
  ∎

ctxidP : (Γ : RawCtx) → CtxMorP Γ Γ
ctxidP Γ = mkCtxMorP (ctxidDO Γ)

_↓[_/0] : {Γ₁ Γ Γ₂ : RawCtx} →
          PreTerm (∗ ∷ Γ₁) Γ → PreTerm Γ₁ Ø  → PreTerm Γ₁ Γ
_↓[_/0] t s = t ↓[ s ∷ ctxidP _ ]

_•_ : {Γ₁ Γ₂ Γ₃ : RawCtx} → CtxMorP Γ₂ Γ₃ → CtxMorP Γ₁ Γ₂ → CtxMorP Γ₁ Γ₃
_•_ {Γ₃ = Ø} [] f = []
_•_ {Γ₃ = A ∷ Γ₃} (t ∷ g) f = substP t f ∷ (g • f)

-- | Context projection is a decent context morphism
ctxProjDO : (Γ₁ Γ₂ : RawCtx) → DecentCtxMor (ctxProjRaw Γ₁ Γ₂)
ctxProjDO Γ₁ Ø        = ctxidDO Γ₁
ctxProjDO Γ₁ (x ∷ Γ₂) = weakenDecentCtxMor _ (ctxProjDO Γ₁ Γ₂)

ctxProjP : (Γ₁ Γ₂ : RawCtx) → CtxMorP (Γ₂ ++ Γ₁) Γ₁
ctxProjP Γ₁ Γ₂ = mkCtxMorP (ctxProjDO Γ₁ Γ₂)

ctxProjP' : (Γ₁ Γ₂ Γ₃ : RawCtx) → CtxMorP (Γ₁ ++ Γ₂ ++ Γ₃) Γ₂
ctxProjP' Γ₁ Γ₂ Ø =
  subst (λ Γ → CtxMorP (Γ₁ ++ Γ) Γ₂)
        (PE.sym (proj₂ identity Γ₂))
        (ctxProjP Γ₂ Γ₁)
ctxProjP' Γ₁ Γ₂ (A ∷ Γ₃) =
  let f = ctxProjP' Γ₁ Γ₂ Γ₃
  in subst (λ Γ → Vec (PreTerm Γ Ø) (length' Γ₂))
           (assoc Γ₁ Γ₂ (A ∷ Γ₃))
           (Vec.map (weakenPO (Γ₁ ++ Γ₂) A)
                    (subst (λ Γ → Vec (PreTerm Γ Ø) (length' Γ₂))
                           (PE.sym (assoc Γ₁ Γ₂ Γ₃))
                           f
                    )
           )

weakenDO' : {Γ₁ Γ₃ : RawCtx} {t : Raw Ø Γ₁ Γ₃} →
            (Γ₂ : RawCtx) → DecentTerm t → DecentTerm (weaken' Γ₂ t)
weakenDO' {Γ₁} {t = t} Γ₂ p =
  subst DecentTerm
        (cong (substRaw t) (mkCtxMorP₁ (ctxProjDO Γ₁ Γ₂)))
        (substDO (ctxProjP Γ₁ Γ₂) p)

weakenPO' : {Γ₁ Γ₃ : RawCtx} →
            (Γ₂ : RawCtx) → PreTerm Γ₁ Γ₃ → PreTerm (Γ₂ ++ Γ₁) Γ₃
weakenPO' Γ₂ (t , p) = (weaken' Γ₂ t , weakenDO' Γ₂ p)

-- | Lift extension of context morphism to decent terms
extendP : {Γ₁ Γ₂ : RawCtx} →
           (A : U) → (f : CtxMorP Γ₂ Γ₁) → CtxMorP (A ∷ Γ₂) (A ∷ Γ₁)
extendP {Γ₁} {Γ₂} A f = varPO zero ∷ Vec.map (weakenPO₁ A) f

getPO : {Γ₁ Γ₂ : RawCtx} {A : U} → CtxMorP Γ₂ Γ₁ → RawVar Γ₁ A → PreTerm Γ₂ Ø
getPO f x = (get {Raw} (projCtxMor₁ f) x , get' f x)

substPO : ∀ {Γ₁ Γ Γ₂} → PreTerm Γ₁ Γ → CtxMorP Γ₂ Γ₁ → PreTerm Γ₂ Γ
substPO (._ , DO-unit Γ₁)             f = unitPO _
substPO (._ , DO-objVar x)            f = getPO f x
substPO (._ , DO-inst t s p q)        f =
  instPO (substPO (t , p) f) (substPO (s , q) f)
substPO (._ , DO-dialg Γ₁ Γ A ρ k)    f = dialgPO _ Γ A ρ k
substPO (._ , DO-mapping Γ Γ₁ gs ρ p) f = grec Γ _ (mkFpMapDataP {Γ} {gs} p) ρ

weakenPO'' : {Γ₁ Γ₃ : RawCtx} →
             (Γ₂ Γ₂' : RawCtx) → PreTerm Γ₁ Γ₃ → PreTerm (Γ₂' ++ Γ₁ ++ Γ₂) Γ₃
weakenPO'' Γ₂ Γ₂' t = substPO t (ctxProjP' Γ₂' _ Γ₂)

-- | Lift substitution to pretypes
substPT : ∀ {Θ Γ₁ Γ Γ₂} → PreType Θ Γ₁ Γ → CtxMorP Γ₂ Γ₁ → PreType Θ Γ₂ Γ
substPT (._ , DT-⊤ Θ Γ)               f = ⊤-PT _ _
substPT (._ , DT-tyVar Γ₁ X)          f = tyVarPT _ X
substPT (._ , DT-inst B t p q)        f =
  (substPT (B , p) f) ⊙ (substPO (t , q) f)
substPT (._ , DT-paramAbstr Γ₁ {A} p) f =
  paramAbstrPT _ (substPT (A , p) (extendP _ f))
substPT (._ , DT-fp Γ₁ ρ D q)         f = fpPT _ ρ (mkFpDataP {D = D} q)

weakenPT' : ∀ {Θ Γ₁ Γ₂} (Γ : RawCtx) → PreType Θ Γ₁ Γ₂ → PreType Θ (Γ ++ Γ₁) Γ₂
weakenPT' {Γ₁ = Γ₁} Γ A = substPT A (ctxProjP Γ₁ Γ)

weakenPT'' : ∀ {Θ Γ₁} (Γ : RawCtx) → PreType Θ Ø Γ₁ → PreType Θ Γ Γ₁
weakenPT'' Γ A =
  subst (λ u → PreType _ u _) (proj₂ identity Γ) (weakenPT' Γ A)

-- | Project a specific variable out
projVar : (Γ₁ Γ₂ : RawCtx) (A : U) → PreTerm (Γ₂ ++ A ∷ Γ₁) Ø
projVar Γ₁ Ø        A = varPO zero
projVar Γ₁ (∗ ∷ Γ₂) A = weakenPO₁ _ (projVar Γ₁ Γ₂ A)

extendProj : {Γ₁ Γ₂ : RawCtx} → (Γ₃ Γ₄ : RawCtx) →
             CtxMorP (Γ₄ ++ Γ₃ ++ Γ₂) Γ₁ →
             CtxMorP (Γ₄ ++ Γ₃ ++ Γ₂) (Γ₃ ++ Γ₁)
extendProj Ø Γ₄ f = f
extendProj {Γ₁} {Γ₂ = Γ₂} (A ∷ Γ₃) Γ₄ f =
  let p = (assoc Γ₄ (A ∷ Ø) (Γ₃ ++ Γ₂))
      f' = subst (λ u → CtxMorP u Γ₁) (PE.sym p) f
      g = extendProj {Γ₁} {Γ₂} Γ₃ (Γ₄ ↑ A) f'
      g' = subst (λ u → CtxMorP u (Γ₃ ++ Γ₁)) p g
  in projVar (Γ₃ ++ Γ₂) Γ₄ A ∷ g'

weakenTyVar₁ : ∀{Θ₂ Γ₁} (Θ₁ : TyCtx) (Γ : RawCtx) →
               TyVar (Θ₁ ++ Θ₂) Γ₁ → TyVar (Θ₁ ++ Γ ∷ Θ₂) Γ₁
weakenTyVar₁ Ø         Γ X           = succ _ X
weakenTyVar₁ (Γ₁ ∷ Θ₁) Γ zero        = zero
weakenTyVar₁ (Γ₂ ∷ Θ₁) Γ (succ Γ₁ X) = succ Γ₁ (weakenTyVar₁ Θ₁ Γ X)

weakenTyFpData'₁ : ∀ {Θ₂ Γ₁} (Θ₁ : TyCtx) →
                   {D : FpData Raw (Θ₁ ++ Θ₂) Γ₁} →
                   (Γ : RawCtx) → DecentFpData D →
                   Σ (FpData Raw (Θ₁ ++ Γ ∷ Θ₂) Γ₁) DecentFpData

-- | Auxiliary definition to allow Agda to see that it is provided with
-- a well-defined reursion.
weakenTy'₁ : ∀ {Θ₂ Γ₁ Γ₂} (Θ₁ : TyCtx) (Γ : RawCtx) →
             (A : Raw (Θ₁ ++ Θ₂) Γ₁ Γ₂) → DecentType A →
             PreType (Θ₁ ++ Γ ∷ Θ₂) Γ₁ Γ₂
weakenTy'₁ Θ₁ Γ ._ (DT-⊤ ._ Γ₁) =
  ⊤-PT _ _
weakenTy'₁ Θ₁ Γ .(tyVarRaw Γ₁ X) (DT-tyVar Γ₁ X) =
  tyVarPT Γ₁ (weakenTyVar₁ Θ₁ Γ X)
weakenTy'₁ Θ₁ Γ .(instRaw B t) (DT-inst B t p q) =
  (weakenTy'₁ Θ₁ Γ B p) ⊙ (t , q)
weakenTy'₁ Θ₁ Γ .(paramAbstrRaw Γ₁ A) (DT-paramAbstr Γ₁ {A} p) =
  paramAbstrPT Γ₁ (weakenTy'₁ Θ₁ Γ A p)
weakenTy'₁ Θ₁ Γ .(fpRaw Γ₁ ρ D) (DT-fp Γ₁ ρ D p) =
  let (D' , p') = weakenTyFpData'₁ Θ₁ {D} Γ p
  in fpPT Γ₁ ρ (mkFpDataP {D = D'} p')

weakenTyFpData'₁ {Γ₁ = Γ₁} Θ₁ {[ Γ₂ , f , A ]}   Γ (p , q) =
  let (A' , q') = weakenTy'₁ (Γ₁ ∷ Θ₁) Γ A q
  in ([ Γ₂ , f , A' ] , p , q')
weakenTyFpData'₁ {Γ₁ = Γ₁} Θ₁ {(Γ₂ , f , A) ∷ D} Γ ((p , q) , r) =
  let (A' , q') = weakenTy'₁ (Γ₁ ∷ Θ₁) Γ A q
      (D' , r') = weakenTyFpData'₁ Θ₁ {D} Γ r
  in ((Γ₂ , f , A') ∷ D' , (p , q') , r')

weakenTy₁ : ∀ {Θ₂ Γ₁ Γ₂} (Θ₁ : TyCtx) (Γ : RawCtx) →
            PreType (Θ₁ ++ Θ₂) Γ₁ Γ₂ →
            PreType (Θ₁ ++ Γ ∷ Θ₂) Γ₁ Γ₂
weakenTy₁ Θ₁ Γ (A , p) = weakenTy'₁ Θ₁ Γ A p

weakenTyCtxMor₁ : ∀ {Θ₁ Θ₂} →
                  (Γ : RawCtx) → TyCtxMorP Θ₂ Θ₁ → TyCtxMorP (Γ ∷ Θ₂) Θ₁
weakenTyCtxMor₁ {Ø} Γ tt = tt
weakenTyCtxMor₁ {Γ₁ ∷ Θ₁} Γ (A , f) = (weakenTy₁ Ø Γ A , weakenTyCtxMor₁ Γ f)

getTy : ∀ {Θ₁ Θ₂ Γ₁ Γ₂} → TyCtxMorP Θ₁ Θ₂ → TyVar Θ₂ Γ₂ → PreType Θ₁ Γ₁ Γ₂
getTy {Θ₂ = Ø} tt ()
getTy {Θ₁} {Θ₂ = Γ ∷ Θ₂} {Γ₁} (B , f) zero =
  subst (λ Γ' → PreType Θ₁ Γ' Γ) (proj₂ identity Γ₁) (weakenPT' Γ₁ B)
getTy {Θ₂ = Γ ∷ Θ₂} (B , f) (succ Γ₂ X) = getTy f X

extendTy : ∀ {Θ₁ Θ₂} →
           TyCtxMorP Θ₁ Θ₂ → (Γ : RawCtx) → TyCtxMorP (Γ ∷ Θ₁) (Γ ∷ Θ₂)
extendTy f Γ = (tyVarPT Ø zero , weakenTyCtxMor₁ Γ f)

substTyFpData' : ∀ {Θ₁ Θ₂ Γ} →
                 (D : FpData Raw Θ₂ Γ) → DecentFpData D →
                 TyCtxMorP Θ₁ Θ₂ → FpDataP Θ₁ Γ

-- | Substitution for type variables, auxilary version to have a clearly
-- terminating definition.
substTy' : ∀ {Θ₁ Θ₂ Γ₁ Γ₂} →
            (A : Raw Θ₂ Γ₁ Γ₂) → DecentType A → TyCtxMorP Θ₁ Θ₂ →
            PreType Θ₁ Γ₁ Γ₂

substTy' {Θ₁} ._ (DT-⊤ Θ Γ)               f = ⊤-PT Θ₁ _
substTy' {Θ₁} ._ (DT-tyVar Γ₁ X)          f = getTy f X
substTy' {Θ₁} ._ (DT-inst B t p q)        f =
  (substTy' B p f) ⊙ (t , q)
substTy' {Θ₁} ._ (DT-paramAbstr Γ₁ {A} p) f =
  paramAbstrPT Γ₁ (substTy' A p f)
substTy' {Θ₁} ._ (DT-fp Γ₁ ρ D p)         f =
  fpPT Γ₁ ρ (substTyFpData' D p f)

substTyFpData' {Γ = Γ} [ Γ₁ , g , A ] (p , q) f =
  [ Γ₁ , mkCtxMorP p , substTy' A q (extendTy f Γ) ]
substTyFpData' {Γ = Γ} ((Γ₁ , g , A) ∷ D) ((p , q) , r) f =
  (Γ₁ , mkCtxMorP p , substTy' A q (extendTy f Γ))
  ∷ substTyFpData' D r f

-- | Substitution for type variables
substTy : ∀ {Θ₁ Θ₂ Γ₁ Γ₂} →
          PreType Θ₂ Γ₁ Γ₂ → TyCtxMorP Θ₁ Θ₂ → PreType Θ₁ Γ₁ Γ₂
substTy (A , p) = substTy' A p

{-
weakenTy : {Θ₁ : TyCtx} {Γ₁ Γ₂ : RawCtx}
           (Θ₂ : TyCtx) → Raw Θ₁ Γ₁ Γ₂ → Raw (Θ₂ ++ Θ₁) Γ₁ Γ₂
weakenTy = {!!}
-}

-----------------------------------------------
--- Other operations
----------------------------------------------
Λ : ∀ {Θ Γ₁ Γ₂} → PreType Θ Γ₁ Γ₂ → PreType Θ Ø (Γ₂ ++ Γ₁)
Λ {Γ₁ = Ø}           A =
  subst (λ Γ → PreType _ Ø Γ) (PE.sym (proj₂ identity _)) A
Λ {Γ₁ = B ∷ Γ₁} {Γ₂} A =
  let A' = Λ (paramAbstrPT Γ₁ A)
  in subst (λ Γ → PreType _ Ø Γ) (assoc Γ₂ (B ∷ Ø) Γ₁) A'

--------------------------------------------------
-- Examples
--------------------------------------------------

-- We could prove the following
-- DT-Prod : (Γ : RawCtx) → DecentType (ProdRaw Γ)
-- However, it is easier to construct the product directly as pretype.

Prod : (Γ : RawCtx) → PreType (Γ ︵ Γ) Ø Γ
Prod Γ = fpPT Ø ν D
  where
    Δ = Γ ︵ Γ

    A : TyVar (Γ ∷ Δ) Γ
    A = succ Γ zero

    B : TyVar (Γ ∷ Δ) Γ
    B = succ Γ (succ Γ zero)

    D₁ = (Γ , ctxidP Γ , instTyWCtxMorP (tyVarPT Γ A) (ctxidP Γ))

    D₂ = (Γ , ctxidP Γ , instTyWCtxMorP (tyVarPT Γ B) (ctxidP Γ))

    D : FpDataP Δ Γ
    D = D₁ ∷ [ D₂ ]
