module Indexed.examples where
    
open import Indexed.datatypes 
open import Non_Indexed.telescope
open import Indexed.casetrees
open import Indexed.translation
open import Indexed.unify

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Unit.Base
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ<; toℕ) renaming (zero to fzero; suc to fsuc)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

module ordering-example where 

    NatD : DataDesc 2 nil
    NatD fzero        = _ , one' tt
    NatD (fsuc fzero)  = _ , {!   !}

    -- -- datatype
    -- BoolD : DataDesc 2
    -- BoolD fzero        = _ , one'
    -- BoolD (fsuc fzero) = _ , one'

    -- pattern true'  = ⟨ fzero , tt ⟩
    -- pattern false' = ⟨ fsuc fzero , tt ⟩

    -- not : μ BoolD → μ BoolD
    -- not true'  = false' 
    -- not false' = true' 

    -- -- case tree
    -- CTNotRoot : CaseTree (_ ∈ μ BoolD , nil) (λ _ → μ BoolD) 
    -- CTNotRoot = node (here tt) λ where
    --     (fzero)      → leaf (λ _ → false')
    --     (fsuc fzero) → leaf (λ _ → true')     

    -- -- translation
    -- ≡-not : {x : μ BoolD} (b : μ BoolD) → not b ≡ x 
    --     → eval CTNotRoot ( b , tt ) ≡ x
    -- ≡-not true' refl = refl 
    -- ≡-not false' refl = refl 
    