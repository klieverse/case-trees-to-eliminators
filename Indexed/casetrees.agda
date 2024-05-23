{-# OPTIONS --allow-unsolved-metas #-}
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
  ℓ   : Level
  i n m : ℕ
  IΔ    : Telescope i

-- telescope of equivalent indices
vecTel : {IΔ : Telescope n} (d₁ d₂ : ⟦ IΔ ⟧telD) → Telescope n
vecTel {IΔ = nil     } tt tt = nil 
vecTel {IΔ = cons D E} (d₁ , ds₁) (d₂ , ds₂) = e ∈ (d₁ ≡ d₂) , vecTel (subst (λ d → ⟦ E d ⟧telD) e ds₁) ds₂

-- telescope of constructor arguments for constructor description C on X
conTel : {IΔ : Telescope n}(X : ⟦ IΔ ⟧telD → Set)(C : ConDesc IΔ m)(d : ⟦ IΔ ⟧telD) → Telescope (m + n)
conTel X (one' d') d = vecTel d' d
conTel X (Σ' S C) d = s ∈ S , conTel X (C s) d
conTel X (×' d' C) d = x ∈ X d' , conTel X C d

-- telescope of constructor arguments for constructor description C on X
telToVec : {IΔ : Telescope n}{d₁ d₂ : ⟦ IΔ ⟧telD}
    → (t : ⟦ vecTel d₁ d₂ ⟧telD) → d₁ ≡ d₂
telToVec {IΔ = nil} tt = refl 
telToVec {IΔ = cons D E} (t , ts) = Σ-create t (telToVec ts) 

telToCon : {X : ⟦ IΔ ⟧telD → Set}{C : ConDesc IΔ n}{d : ⟦ IΔ ⟧telD}
    → (t : ⟦ conTel X C d ⟧telD) → ⟦ C ⟧c X d
telToCon {C = one' d'} {d} v = telToVec v
telToCon {C = Σ' S C} (s , t) = s , telToCon t
telToCon {C = ×' d' C} (x , t) = x , telToCon t

-- instantiation of conTel from interpretation of constructor interpretation on X
vecToTel : {IΔ : Telescope n}{d₁ d₂ : ⟦ IΔ ⟧telD}
    → d₁ ≡ d₂ → ⟦ vecTel d₁ d₂ ⟧telD
vecToTel {IΔ = nil } e = tt
vecToTel {IΔ = cons S E} e = linvΣ₁ e , vecToTel (linvΣ₂ e) 
    
conToTel : {X : ⟦ IΔ ⟧telD → Set}{C : ConDesc IΔ n}{d : ⟦ IΔ ⟧telD}
    → ⟦ C ⟧c X d → ⟦ conTel X C d ⟧telD
conToTel {C = one' v} e = vecToTel e
conToTel {C = Σ' S C} (s , t) = s , conToTel t 
conToTel {C = ×' _ C} (x , t) = x , conToTel t

-- proof of section-retraction pair
telToVec∘vecToTel : {IΔ : Telescope n}{d₁ d₂ : ⟦ IΔ ⟧telD}
    → (e : d₁ ≡ d₂) → telToVec (vecToTel e) ≡ e
telToVec∘vecToTel {IΔ = nil } refl = refl
telToVec∘vecToTel {IΔ = cons D E} e 
  = subst (λ e' → Σ-create (linvΣ₁ e) e' ≡ e) (sym (telToVec∘vecToTel (linvΣ₂ e))) (isLinvΣ e) 

telToCon∘conToTel : {X : ⟦ IΔ ⟧telD → Set}{C : ConDesc IΔ n}{d : ⟦ IΔ ⟧telD}
    → (t : ⟦ C ⟧c X d) → telToCon (conToTel t) ≡ t 
telToCon∘conToTel {C = one' v} e = telToVec∘vecToTel e
telToCon∘conToTel {C = Σ' S C} (s , t) = cong (s ,_) (telToCon∘conToTel t)
telToCon∘conToTel {C = ×' _ C} (x , t) = cong (x ,_) (telToCon∘conToTel t)

-- representation of a case tree
data CaseTree (Δ : Telescope n)(T : ⟦ Δ ⟧telD → Set ℓ) : Set (lsuc ℓ) where
    leaf : (t : (args : ⟦ Δ ⟧telD) → T args) → CaseTree Δ T
    node : {k d : ℕ}{IΔ : Telescope d}{D : DataDesc m IΔ}
      → (p : Δ [ k ]∶Σ[ ⟦ IΔ ⟧telD ] (μ D))
      → (bs : (con : Fin m) 
        -- add unification algorithm for indices
        → Σ[ u ∈ Unification (expandTel Δ (conTel (μ D) (proj₂ (D con))) 
            (λ d args → ⟨ con , telToCon args ⟩ ) p)] 
          (CaseTree (proj₂ (unifyTel u)) (λ args → expandSort p T (unify' u args))))
      → CaseTree Δ T

-- example flip function
ΔFlip : {A : Set} (w : A) → Telescope 8 
ΔFlip {A = A} w = x ∈ A , y ∈ A , z ∈ A , t ∈ μ (≡D w) (x , tt) , b ∈ μ (≡D y) (z , tt) , l ∈ μ (≡D w) (y , tt) , r ∈ μ (≡D x) (z , tt) ,
            s ∈ μ (SquareD w) (x , y , z , t , b , l , r , tt) , nil

TFlip : {A : Set} (w : A) → ⟦ ΔFlip w ⟧telD → Set 
TFlip w (x , y , z , t , b , l , r , _) = μ (SquareD w) (y , x , z , l , r , t , b , tt)

CTFlip : {A : Set} (w : A) → CaseTree (ΔFlip w) (TFlip w)
CTFlip {A} w = node (there (λ x → there (λ y → there (λ z → there (λ t → there (λ b → there (λ l → there (λ r → here (x , y , z , t , b , l , r , tt))))))))) (λ where 
  (fzero) → unifyFlip , leaf (λ _ → ids w)) where 
  
  Δsplit₆ : Telescope 2 
  Δsplit₆ = r ∈ μ (≡D w) (w , tt) , ewy ∈ idp w ≡ r , nil
  
  unifyFlip₆ : Unification Δsplit₆
  unifyFlip₆ = Usolution {A = λ a → μ (≡D a) (a , tt)} (here (w , idp w)) (UEnd nil)

  Δsplit₅ : Telescope 4 
  Δsplit₅ = l ∈ μ (≡D w) (w , tt) , r ∈ μ (≡D w) (w , tt) ,
              ewy ∈ idp w ≡ l , _
  
  unifyFlip₅ : Unification Δsplit₅
  unifyFlip₅ = UReorder (fsuc fzero) fzero (λ _ → _ , there (λ l → here tt))
                  (Usolution {A = λ a → μ (≡D a) (a , tt)} (here (w , idp w)) unifyFlip₆) 

  Δsplit₄ : Telescope 6 
  Δsplit₄ = b ∈ μ (≡D w) (w , tt) , l ∈ μ (≡D w) (w , tt) , r ∈ μ (≡D w) (w , tt) ,
              ewy ∈ idp w ≡ b , _
  
  unifyFlip₄ : Unification Δsplit₄
  unifyFlip₄ = UReorder (fsuc fzero) fzero (λ _ → _ , there (λ b → there (λ l → here tt)))
                  (Usolution {A = λ a → μ (≡D a) (a , tt)} (here (w , idp w)) unifyFlip₅) 

  Δsplit₃ : Telescope 8 
  Δsplit₃ = t ∈ μ (≡D w) (w , tt) , b ∈ μ (≡D w) (w , tt) , l ∈ μ (≡D w) (w , tt) , r ∈ μ (≡D w) (w , tt) ,
              ewy ∈ idp w ≡ t , _
  
  unifyFlip₃ : Unification Δsplit₃
  unifyFlip₃ = UReorder (fsuc fzero) fzero (λ _ → _ , there (λ t → there (λ b → there (λ l → here tt))))
                  (Usolution {A = λ a → μ (≡D a) (a , tt)} (here (w , idp w)) unifyFlip₄) 

  Δsplit₂ : Telescope 10 
  Δsplit₂ = z ∈ A , t ∈ μ (≡D w) (w , tt) , b ∈ μ (≡D w) (z , tt) , l ∈ μ (≡D w) (w , tt) , r ∈ μ (≡D w) (z , tt) ,
              ewy ∈ w ≡ z , _
  
  unifyFlip₂ : Unification Δsplit₂
  unifyFlip₂ = UReorder (fsuc fzero) fzero (λ _ → _ , there (λ z → there (λ t → there (λ b → there (λ l → here tt))))) 
                  (Usolution {X = ⊤} {A = λ a → A} (here (tt , w)) unifyFlip₃) 

  Δsplit₁ : Telescope 12 
  Δsplit₁ = y ∈ A , z ∈ A , t ∈ μ (≡D w) (w , tt) , b ∈ μ (≡D y) (z , tt) , l ∈ μ (≡D w) (y , tt) , r ∈ μ (≡D w) (z , tt) ,
              ewy ∈ w ≡ y , _ 
  
  unifyFlip₁ : Unification Δsplit₁
  unifyFlip₁ = UReorder (fsuc fzero) fzero (λ _ → _ , there (λ y → there (λ z → there (λ t → there (λ b → there (λ l → here tt)))))) 
                  (Usolution {X = ⊤} {A = λ a → A} (here (tt , w)) unifyFlip₂) 

  Δsplit : Telescope 14 
  Δsplit = x ∈ A , y ∈ A , z ∈ A , t ∈ μ (≡D w) (x , tt) , b ∈ μ (≡D y) (z , tt) , l ∈ μ (≡D w) (y , tt) , r ∈ μ (≡D x) (z , tt) ,
    ewx ∈ w ≡ x , _

  unifyFlip : Unification Δsplit
  unifyFlip = UReorder (fsuc fzero) fzero (λ _ → _ , there (λ y → there (λ z → there (λ t → there (λ b → there (λ l → there (λ r → here tt)))))))
                (Usolution {X = ⊤} {A = λ a → A} (here (tt , w)) unifyFlip₁)
