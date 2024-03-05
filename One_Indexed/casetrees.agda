-- {-# OPTIONS --allow-unsolved-metas #-}
module One_Indexed.casetrees where
    
import Non_Indexed.datatypes as NI
open import One_Indexed.datatypes
open import Non_Indexed.telescope
open import Non_Indexed.unify

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
  IΔ    : DVec j

vecTel : {IΔ : DVec j} (d₁ d₂ : ⟦ IΔ ⟧Vec) → Telescope j 
vecTel {j = zero}  {IΔ = [] } tt tt = nil 
vecTel {j = suc j} {IΔ = d ∷ ds} (d₁ , ds₁) (d₂ , ds₂) = e ∈ (d₁ ≡ d₂) , vecTel ds₁ ds₂

conTel : {IΔ : DVec j}(D : DataDesc i IΔ)(C : ConDesc IΔ k)(d : ⟦ IΔ ⟧Vec) → Telescope (k + j)
conTel D (one' d') d = vecTel d' d
conTel D (Σ' S C) d = s ∈ S , conTel D (C s) d
conTel D (×' d' C) d = μD ∈ μ D d' , conTel D C d

telToVec : {IΔ : DVec j}{d₁ d₂ : ⟦ IΔ ⟧Vec}
    → (t : ⟦ vecTel d₁ d₂ ⟧telD) → d₁ ≡ d₂
telToVec {j = zero}  {IΔ = [] } tt = refl
telToVec {j = suc j} {IΔ = d ∷ ds} {d₁} {d₂} (t , ts) = subst (λ ds₂ → (proj₁ d₁ , proj₂ d₁) ≡ (proj₁ d₂ , ds₂)) (telToVec ts) 
        (subst (λ d₂ → (proj₁ d₁ , proj₂ d₁) ≡ (d₂ , proj₂ d₁)) t refl)

telToCon : {D : DataDesc i IΔ}{C : ConDesc IΔ k}{d : ⟦ IΔ ⟧Vec}
    → (t : ⟦ conTel D C d ⟧telD) → ⟦ C ⟧c (μ D) d
telToCon {C = one' d'} {d} v = telToVec v
telToCon {C = Σ' S C} (s , t) = s , telToCon t
telToCon {C = ×' d' C} (μD , t) = μD , telToCon t

vecToTel : {IΔ : DVec j}{d₁ d₂ : ⟦ IΔ ⟧Vec}
    → d₁ ≡ d₂ → ⟦ vecTel d₁ d₂ ⟧telD
vecToTel {j = zero}  {IΔ = [] } e = tt
vecToTel {j = suc j} {IΔ = d ∷ ds} e = cong proj₁ e , vecToTel (cong proj₂ e)

conToTel : {D : DataDesc i IΔ}{C : ConDesc IΔ k}{d : ⟦ IΔ ⟧Vec}
    → ⟦ C ⟧c (μ D) d → ⟦ conTel D C d ⟧telD
conToTel {C = one' v} e = vecToTel e
conToTel {C = Σ' S C} (s , t) = s , conToTel t 
conToTel {C = ×' _ C} (μD , t) = μD , conToTel t

≡Cong : {D DS : Set} {x₁ x₂ : Σ D (λ v → DS)} (e : x₁ ≡ x₂) 
        → subst (λ ds₂ → x₁ ≡ (proj₁ x₂ , ds₂)) (cong (λ r → proj₂ r) e)
          (subst (λ d₂ → x₁ ≡ (d₂ , proj₂ x₁)) (cong (λ r → proj₁ r) e)
          refl)
          ≡ e
≡Cong {D} {DS} {x₁} {x₂} e = J {x = x₁} (λ x₂ e → subst (λ ds₂ → x₁ ≡ (proj₁ x₂ , ds₂)) (cong (λ r → snd r) e)
      (subst (λ d₂ → x₁ ≡ (d₂ , snd x₁)) (cong (λ r → proj₁ r) e) refl)
      ≡ e) refl e 

telToVec∘vecToTel : {IΔ : DVec j}{d₁ d₂ : ⟦ IΔ ⟧Vec}
    → (e : d₁ ≡ d₂) → telToVec (vecToTel e) ≡ e
telToVec∘vecToTel {j = zero} {IΔ = []} {d₁ = tt} {d₂ = tt} e = linvJ (λ _ e' → e' ≡ e) e refl
telToVec∘vecToTel {j = suc j} {IΔ = d ∷ ds} {d₁ = (d₁ , ds₁)} {d₂ = (d₂ , ds₂)} e 
  = subst (λ e₂ → subst (λ ds₂ → (d₁ , ds₁) ≡ (d₂ , ds₂)) e₂
      (subst (λ d₂ → (d₁ , ds₁) ≡ (d₂ , ds₁)) (cong (λ r → proj₁ r) e)
      refl) ≡ e) (sym (telToVec∘vecToTel (cong (λ r → snd r) e))) (≡Cong e)

telToCon∘conToTel : {D : DataDesc i IΔ}{C : ConDesc IΔ k}{d : ⟦ IΔ ⟧Vec}
    → (t : ⟦ C ⟧c (μ D) d) → telToCon (conToTel t) ≡ t 
telToCon∘conToTel {C = one' v} e = telToVec∘vecToTel e
telToCon∘conToTel {C = Σ' S C} (s , t) = cong (s ,_) (telToCon∘conToTel t)
telToCon∘conToTel {C = ×' _ C} (μD , t) = cong (μD ,_) (telToCon∘conToTel t)

data CaseTree {ℓ : Level} : {i : ℕ}(Δ : Telescope i)(T : ⟦ Δ ⟧telD → Set ℓ) → Set (lsuc ℓ) where
    leaf : {i : ℕ}{Δ : Telescope i}{T : ⟦ Δ ⟧telD → Set ℓ} → 
            (t : (d : ⟦ Δ ⟧telD) → T d) → CaseTree Δ T
    node : {i j Δn : ℕ}{Δ : Telescope (suc Δn)}{T : ⟦ Δ ⟧telD → Set ℓ}
            {IΔ : DVec i}{D : DataDesc (suc j) IΔ}
            → {Δi : ℕ}
            → (e : Δ [ Δi ]∶Σ[ ⟦ IΔ ⟧Vec ] (μ D))
            → (f : (target : Fin (suc j)) 
                → Σ[ u ∈ Unification (expandTel Δ (conTel D (proj₂ (D target))) (λ d x → ⟨ target , telToCon x ⟩) e)] 
                        (CaseTree (proj₂ (unifyTel u)) (λ t → expandSort e T (linvUnify u t))))
            → CaseTree Δ T



