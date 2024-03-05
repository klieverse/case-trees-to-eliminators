-- {-# OPTIONS --allow-unsolved-metas #-}
module Non_Indexed.casetrees where
    
open import Non_Indexed.datatypes
open import Non_Indexed.telescope

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Unit.Base
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ<; toℕ) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

-- types in telescope of constructor C
conTel : {j k : ℕ} → (D : DataDesc j) → (C : ConDesc k) → (Telescope k)
conTel D one' = nil
conTel {k = suc i} D (Σ' S C) = s ∈ S , conTel D (C s)
conTel {k = suc i} D (ind×' C) = μD ∈ μ D , conTel D C

telToCon : {j k : ℕ}{D : DataDesc j}{C : ConDesc k} → ⟦ conTel D C ⟧telD → ⟦ C ⟧c (μ D)
telToCon {C = one'} _ = tt
telToCon {C = Σ' S C} (s , d) = s , telToCon d 
telToCon {C = ind×' C} (μD , d) = μD , telToCon d 

conToTel : {j k : ℕ}{D : DataDesc j}{C : ConDesc k} → ⟦ C ⟧c (μ D) → ⟦ conTel D C ⟧telD
conToTel {C = one'} _ = tt
conToTel {C = Σ' S C} (s , d) = s , conToTel d
conToTel {C = ind×' C} (μD , d) = μD , conToTel d

telToCon∘conToTel : {j k : ℕ}{D : DataDesc j}{C : ConDesc k} → (d : ⟦ C ⟧c (μ D))
    → telToCon (conToTel d) ≡ d 
telToCon∘conToTel {C = one'} tt = refl
telToCon∘conToTel {C = Σ' S C} (s , d) = cong (λ d → s , d) (telToCon∘conToTel d) 
telToCon∘conToTel {C = ind×' C} (μD , d) = cong (λ d → μD , d) (telToCon∘conToTel d)

data CaseTree {ℓ : Level} : {i : ℕ}(Δ : Telescope i)(T : ⟦ Δ ⟧telD → Set ℓ) → Set (lsuc ℓ) where
    leaf : {i : ℕ}{Δ : Telescope i}{T : ⟦ Δ ⟧telD → Set ℓ} → 
            (t : (d : ⟦ Δ ⟧telD) → T d) → CaseTree Δ T
    node : {j k : ℕ}{Δ : Telescope (suc k)}{T : ⟦ Δ ⟧telD → Set ℓ}
            → {i : ℕ} → {D : DataDesc (suc j)} 
            → (e : Δ [ i ]∶Σ[ ⊤ ] (λ _ → μ D))
            → (f : (target : Fin (suc j)) → CaseTree 
                (expandTel Δ (λ _ → conTel D (proj₂ (D target))) (λ _ x → ⟨ target , telToCon x ⟩) e)
                (expandSort e T))
            → CaseTree Δ T


            