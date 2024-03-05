{-# OPTIONS --allow-unsolved-metas #-}
module Indexed.casetrees where
    
open import Indexed.datatypes
open import Non_Indexed.telescope
open import Indexed.unify

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ<; toℕ) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Data.Vec using (Vec; []; _∷_)

-- types in telescope of constructor C
private variable
  i j k : ℕ
  IΔ    : Telescope j

vecTel : {IΔ : Telescope j} (d₁ d₂ : ⟦ IΔ ⟧telD) → Telescope (suc j) 
vecTel {j = zero}  {IΔ = nil } d₁ d₂ = e ∈ d₁ ≡ d₂ , nil 
vecTel {j = suc j} {IΔ = cons D E} (d₁ , ds₁) (d₂ , ds₂) = e ∈ (d₁ ≡ d₂) , vecTel (subst (λ d → ⟦ E d ⟧telD) e ds₁) ds₂

conTel : {IΔ : Telescope j}(D : DataDesc i IΔ)(C : ConDesc IΔ k)(d : ⟦ IΔ ⟧telD) → Telescope (k + (suc j))
conTel D (one' d') d = vecTel d' d
conTel D (Σ' S C) d = s ∈ S , conTel D (C s) d
conTel D (×' d' C) d = μD ∈ μ D d' , conTel D C d

telToVec : {IΔ : Telescope j}{d₁ d₂ : ⟦ IΔ ⟧telD}
    → (t : ⟦ vecTel d₁ d₂ ⟧telD) → d₁ ≡ d₂
telToVec {j = zero}  {IΔ = nil } (t , tt) = t 
telToVec {j = suc j} {IΔ = cons D E} {d₁} {d₂} (t , ts) = subst (λ ds₂ → (proj₁ d₁ , proj₂ d₁) ≡ (proj₁ d₂ , ds₂)) (telToVec ts) 
    (J (λ d₂ t → (proj₁ d₁ , snd d₁) ≡ (d₂ , subst (λ d → ⟦ E d ⟧telD) t (snd d₁))) refl t) 

telToCon : {D : DataDesc i IΔ}{C : ConDesc IΔ k}{d : ⟦ IΔ ⟧telD}
    → (t : ⟦ conTel D C d ⟧telD) → ⟦ C ⟧c (μ D) d
telToCon {C = one' d'} {d} v = telToVec v
telToCon {C = Σ' S C} (s , t) = s , telToCon t
telToCon {C = ×' d' C} (μD , t) = μD , telToCon t

vecToTel : {IΔ : Telescope j}{d₁ d₂ : ⟦ IΔ ⟧telD}
    → d₁ ≡ d₂ → ⟦ vecTel d₁ d₂ ⟧telD
vecToTel {j = zero}  {IΔ = nil } e = e , tt
vecToTel {j = suc j} {IΔ = cons S E} {d₁} {d₂} e = cong proj₁ e , vecToTel {d₁ = subst (λ d → ⟦ E d ⟧telD) (cong (λ r → proj₁ r) e) (snd d₁)} 
    {d₂ = snd d₂} (J (λ d₂ e → subst (λ d → ⟦ E d ⟧telD) (cong (λ r → proj₁ r) e) (snd d₁) ≡ snd d₂) refl e) 
    
conToTel : {D : DataDesc i IΔ}{C : ConDesc IΔ k}{d : ⟦ IΔ ⟧telD}
    → ⟦ C ⟧c (μ D) d → ⟦ conTel D C d ⟧telD
conToTel {C = one' v} e = vecToTel e
conToTel {C = Σ' S C} (s , t) = s , conToTel t 
conToTel {C = ×' _ C} (μD , t) = μD , conToTel t

≡Cong : {D : Set} {DS : D → Set} {x₁ x₂ : Σ D DS} (e : x₁ ≡ x₂) 
        → subst (λ ds₂ → x₁ ≡ (proj₁ x₂ , ds₂)) 
          (J (λ d₃ e₁ → subst DS (cong (λ r → proj₁ r) e₁) (proj₂ x₁) ≡ snd d₃) refl e)
          (J (λ d₃ t → x₁ ≡ (d₃ , subst DS t (proj₂ x₁))) refl (cong (λ r → proj₁ r) e))
          ≡ e
≡Cong {D} {DS} {x₁} {x₂} e = J {x = x₁} (λ x₂ e → subst (λ ds₂ → x₁ ≡ (proj₁ x₂ , ds₂)) 
          (J (λ d₃ e₁ → subst DS (cong (λ r → proj₁ r) e₁) (proj₂ x₁) ≡ snd d₃) refl e)
          (J (λ d₃ t → x₁ ≡ (d₃ , subst DS t (proj₂ x₁))) refl (cong (λ r → proj₁ r) e))
          ≡ e) refl e 

telToVec∘vecToTel : {IΔ : Telescope j}{d₁ d₂ : ⟦ IΔ ⟧telD}
    → (e : d₁ ≡ d₂) → telToVec (vecToTel e) ≡ e
telToVec∘vecToTel {j = zero}  {IΔ = nil } e = refl
telToVec∘vecToTel {j = suc j} {IΔ = cons D E} {d₁ = (d₁ , ds₁)} {d₂ = (d₂ , ds₂)} e 
  = subst (λ e' → subst (λ ds₃ → (d₁ , ds₁) ≡ (d₂ , ds₃)) e' (J (λ d₃ t → (d₁ , ds₁) ≡ (d₃ , subst (λ d → ⟦ E d ⟧telD) t ds₁)) refl (cong (λ r → proj₁ r) e)) ≡ e) 
            (sym (telToVec∘vecToTel (J (λ d₃ e₁ → subst (λ d → ⟦ E d ⟧telD) (cong (λ r → proj₁ r) e₁) ds₁ ≡ snd d₃) refl e))) 
            (≡Cong e)

telToCon∘conToTel : {D : DataDesc i IΔ}{C : ConDesc IΔ k}{d : ⟦ IΔ ⟧telD}
    → (t : ⟦ C ⟧c (μ D) d) → telToCon (conToTel t) ≡ t 
telToCon∘conToTel {C = one' v} e = telToVec∘vecToTel e
telToCon∘conToTel {C = Σ' S C} (s , t) = cong (s ,_) (telToCon∘conToTel t)
telToCon∘conToTel {C = ×' _ C} (μD , t) = cong (μD ,_) (telToCon∘conToTel t)

data CaseTree {ℓ : Level} : {i : ℕ}(Δ : Telescope i)(T : ⟦ Δ ⟧telD → Set ℓ) → Set (lsuc ℓ) where
    leaf : {i : ℕ}{Δ : Telescope i}{T : ⟦ Δ ⟧telD → Set ℓ} → 
            (t : (d : ⟦ Δ ⟧telD) → T d) → CaseTree Δ T
    node : {j Δn : ℕ}{Δ : Telescope (suc Δn)}{T : ⟦ Δ ⟧telD → Set ℓ}
            {IΔ : Telescope i}{D : DataDesc (suc j) IΔ}
            → {i : ℕ}
            → (e : Δ [ i ]∶Σ[ ⟦ IΔ ⟧telD ] (μ D))
            → (f : (target : Fin (suc j)) 
                → Σ[ u ∈ Unification (expandTel Δ (conTel D (proj₂ (D target))) (λ d x → ⟨ target , telToCon x ⟩ ) e)] 
                        (CaseTree (proj₂ (unifyTel u)) (λ t → expandSort e T (linvUnify u t))))
            → CaseTree Δ T