{-# OPTIONS --safe #-}
module Indexed.casetrees where
    
open import Indexed.datatypes
open import Non_Indexed.telescope
open import Indexed.unify
open import lib

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ<; toℕ) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Data.Vec using (Vec; []; _∷_)

private variable
  cₙ aₙ iₙ n k : ℕ
  ℓ  : Level
  is : Telescope iₙ

-- telescope of equivalent indices
vecTel : {is : Telescope iₙ} (is₁ is₂ : ⟦ is ⟧telD) → Telescope iₙ
vecTel {is = nil     } tt tt = nil 
vecTel {is = cons S E} (i₁ , is₁) (i₂ , is₂) = e ∈ (i₁ ≡ i₂) , vecTel (subst (λ s → ⟦ E s ⟧telD) e is₁) is₂

-- telescope of constructor arguments for constructor description C on X
conTel : {is : Telescope iₙ}(X : ⟦ is ⟧telD → Set)(C : ConDesc is aₙ)(i : ⟦ is ⟧telD) → Telescope (aₙ + iₙ)
conTel X (one' i') i = vecTel i' i
conTel X (Σ' S C ) i = s ∈ S , conTel X (C s) i
conTel X (×' i' C) i = x ∈ X i' , conTel X C i

-- telescope of constructor arguments for constructor description C on X
telToVec : {is : Telescope iₙ}{is₁ is₂ : ⟦ is ⟧telD}
    → (t : ⟦ vecTel is₁ is₂ ⟧telD) → is₁ ≡ is₂
telToVec {is = nil} tt = refl 
telToVec {is = cons S E} (t , ts) = Σ-create t (telToVec ts) 

telToCon : {X : ⟦ is ⟧telD → Set}{C : ConDesc is aₙ}{i : ⟦ is ⟧telD}
    → (t : ⟦ conTel X C i ⟧telD) → ⟦ C ⟧c X i
telToCon {C = one' i'} t       = telToVec t
telToCon {C = Σ' S C } (s , t) = s , telToCon t
telToCon {C = ×' i' C} (x , t) = x , telToCon t

-- instantiation of conTel from interpretation of constructor interpretation on X
vecToTel : {is : Telescope iₙ}{is₁ is₂ : ⟦ is ⟧telD}
    → is₁ ≡ is₂ → ⟦ vecTel is₁ is₂ ⟧telD
vecToTel {is = nil } e = tt
vecToTel {is = cons S E} e = linvΣ₁ e , vecToTel (linvΣ₂ e) 
    
conToTel : {X : ⟦ is ⟧telD → Set}{C : ConDesc is aₙ}{i : ⟦ is ⟧telD}
    → ⟦ C ⟧c X i → ⟦ conTel X C i ⟧telD
conToTel {C = one' i} e = vecToTel e
conToTel {C = Σ' S C} (s , t) = s , conToTel t 
conToTel {C = ×' i C} (x , t) = x , conToTel t

-- proof of section-retraction pair
telToVec∘vecToTel : {is : Telescope iₙ}{is₁ is₂ : ⟦ is ⟧telD}
    → (e : is₁ ≡ is₂) → telToVec (vecToTel e) ≡ e
telToVec∘vecToTel {is = nil } refl = refl
telToVec∘vecToTel {is = cons S E} e 
  = subst (λ e' → Σ-create (linvΣ₁ e) e' ≡ e) (sym (telToVec∘vecToTel (linvΣ₂ e))) (isLinvΣ e) 

telToCon∘conToTel : {X : ⟦ is ⟧telD → Set}{C : ConDesc is aₙ}{i : ⟦ is ⟧telD}
    → (t : ⟦ C ⟧c X i) → telToCon (conToTel t) ≡ t 
telToCon∘conToTel {C = one' v} e = telToVec∘vecToTel e
telToCon∘conToTel {C = Σ' S C} (s , t) = cong (s ,_) (telToCon∘conToTel t)
telToCon∘conToTel {C = ×' _ C} (x , t) = cong (x ,_) (telToCon∘conToTel t)

-- representation of a case tree
data CaseTree (Δ : Telescope n)(T : ⟦ Δ ⟧telD → Set ℓ) : Set (lsuc ℓ) where
    leaf : (t : (args : ⟦ Δ ⟧telD) → T args) → CaseTree Δ T
    node : {D : DataDesc is cₙ} (p : Δ [ k ]∶Σ[ ⟦ is ⟧telD ] (μ D))
      → (bs : (cᵢ : Fin cₙ) 
        -- add unification algorithm for indices
        → Σ[ u ∈ Unification (expandTel Δ (conTel (μ D) (proj₂ (D cᵢ))) p
            (λ args → ⟨ cᵢ , telToCon args ⟩ ))] 
          (CaseTree (proj₂ (unifyTel u)) (λ args → T (shrink p (unify' u args)))))
      → CaseTree Δ T

-- example flip function
ΔFlip : {A : Set} (w : A) → Telescope 8 
ΔFlip {A = A} w = x ∈ A , y ∈ A , z ∈ A , t ∈ μ (≡D w) (x , tt) , b ∈ μ (≡D y) (z , tt) , l ∈ μ (≡D w) (y , tt) , r ∈ μ (≡D x) (z , tt) ,
            s ∈ μ (SquareD w) (x , y , z , t , b , l , r , tt) , nil

TFlip : {A : Set} (w : A) → ⟦ ΔFlip w ⟧telD → Set 
TFlip w (x , y , z , t , b , l , r , _) = μ (SquareD w) (y , x , z , l , r , t , b , tt)

CTFlip : {A : Set} (w : A) → CaseTree (ΔFlip w) (TFlip w)
CTFlip {A} w = node (there (λ x → there (λ y → there (λ z → there (λ t → there (λ b → there (λ l → there (λ r → here (x , y , z , t , b , l , r , tt))))))))) (λ where 
  f0 → unifyFlip , leaf (λ _ → ids w)) where 
  
  Δsplit₆ : Telescope 2 
  Δsplit₆ = r ∈ μ (≡D w) (w , tt) , ewy ∈ idp w ≡ r , nil
  
  unifyFlip₆ : Unification Δsplit₆
  unifyFlip₆ = Usolution {B = λ a → μ (≡D a) (a , tt)} (here (w , idp w)) (UEnd nil)

  Δsplit₅ : Telescope 4 
  Δsplit₅ = l ∈ μ (≡D w) (w , tt) , r ∈ μ (≡D w) (w , tt) ,
              ewy ∈ idp w ≡ l , _
  
  unifyFlip₅ : Unification Δsplit₅
  unifyFlip₅ = UReorder f1 f0 (λ _ → _ , there (λ l → here tt))
                  (Usolution {B = λ a → μ (≡D a) (a , tt)} (here (w , idp w)) unifyFlip₆) 

  Δsplit₄ : Telescope 6 
  Δsplit₄ = b ∈ μ (≡D w) (w , tt) , l ∈ μ (≡D w) (w , tt) , r ∈ μ (≡D w) (w , tt) ,
              ewy ∈ idp w ≡ b , _
  
  unifyFlip₄ : Unification Δsplit₄
  unifyFlip₄ = UReorder f1 f0 (λ _ → _ , there (λ b → there (λ l → here tt)))
                  (Usolution {B = λ a → μ (≡D a) (a , tt)} (here (w , idp w)) unifyFlip₅) 

  Δsplit₃ : Telescope 8 
  Δsplit₃ = t ∈ μ (≡D w) (w , tt) , b ∈ μ (≡D w) (w , tt) , l ∈ μ (≡D w) (w , tt) , r ∈ μ (≡D w) (w , tt) ,
              ewy ∈ idp w ≡ t , _
  
  unifyFlip₃ : Unification Δsplit₃
  unifyFlip₃ = UReorder f1 f0 (λ _ → _ , there (λ t → there (λ b → there (λ l → here tt))))
                  (Usolution {B = λ a → μ (≡D a) (a , tt)} (here (w , idp w)) unifyFlip₄) 

  Δsplit₂ : Telescope 10 
  Δsplit₂ = z ∈ A , t ∈ μ (≡D w) (w , tt) , b ∈ μ (≡D w) (z , tt) , l ∈ μ (≡D w) (w , tt) , r ∈ μ (≡D w) (z , tt) ,
              ewy ∈ w ≡ z , _
  
  unifyFlip₂ : Unification Δsplit₂
  unifyFlip₂ = UReorder f1 f0 (λ _ → _ , there (λ z → there (λ t → there (λ b → there (λ l → here tt))))) 
                  (Usolution {A = ⊤} {B = λ a → A} (here (tt , w)) unifyFlip₃) 

  Δsplit₁ : Telescope 12 
  Δsplit₁ = y ∈ A , z ∈ A , t ∈ μ (≡D w) (w , tt) , b ∈ μ (≡D y) (z , tt) , l ∈ μ (≡D w) (y , tt) , r ∈ μ (≡D w) (z , tt) ,
              ewy ∈ w ≡ y , _ 
  
  unifyFlip₁ : Unification Δsplit₁
  unifyFlip₁ = UReorder f1 f0 (λ _ → _ , there (λ y → there (λ z → there (λ t → there (λ b → there (λ l → here tt)))))) 
                  (Usolution {A = ⊤} {B = λ a → A} (here (tt , w)) unifyFlip₂) 

  Δsplit : Telescope 14 
  Δsplit = x ∈ A , y ∈ A , z ∈ A , t ∈ μ (≡D w) (x , tt) , b ∈ μ (≡D y) (z , tt) , l ∈ μ (≡D w) (y , tt) , r ∈ μ (≡D x) (z , tt) ,
    ewx ∈ w ≡ x , _

  unifyFlip : Unification Δsplit
  unifyFlip = UReorder f1 f0 (λ _ → _ , there (λ y → there (λ z → there (λ t → there (λ b → there (λ l → there (λ r → here tt)))))))
                (Usolution {A = ⊤} {B = λ a → A} (here (tt , w)) unifyFlip₁)
