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

private variable
  ℓ   : Level
  n m : ℕ
  
-- telescope of constructor arguments for constructor description C on X
conTel : (X : Set) (C : ConDesc n) → Telescope n
conTel X (one'   ) = nil
conTel X (Σ' S C ) = s ∈ S , conTel X (C s)
conTel X (ind×' C) = x ∈ X , conTel X C

-- constructor interpretation on X from an instantiation of conTel
telToCon : {X : Set} {C : ConDesc n} → ⟦ conTel X C ⟧telD → ⟦ C ⟧c X
telToCon {C = one'   } _       = tt
telToCon {C = Σ' S C } (s , d) = s , telToCon d 
telToCon {C = ind×' C} (x , d) = x , telToCon d 

-- instantiation of conTel from interpretation of constructor interpretation on X
conToTel : {X : Set} {C : ConDesc n} → ⟦ C ⟧c X → ⟦ conTel X C ⟧telD
conToTel {C = one'   } _       = tt
conToTel {C = Σ' S C } (s , d) = s , conToTel d
conToTel {C = ind×' C} (x , d) = x , conToTel d

-- proof of section-retraction pair
telToCon∘conToTel
  : {X : Set} {C : ConDesc n} (args : ⟦ C ⟧c X)
  → telToCon (conToTel args) ≡ args
telToCon∘conToTel {C = one'   } tt      = refl
telToCon∘conToTel {C = Σ' S C } (s , d) = cong (s ,_) (telToCon∘conToTel d) 
telToCon∘conToTel {C = ind×' C} (x , d) = cong (x ,_) (telToCon∘conToTel d)


-- representation of a case tree
data CaseTree (Δ : Telescope n)(T : ⟦ Δ ⟧telD → Set ℓ) : Set (lsuc ℓ) where
  -- a leaf contains the result of the function
  leaf : (t : (d : ⟦ Δ ⟧telD) → T d) → CaseTree Δ T
  -- a node splits an element at position k in the telescope of arguments
  -- into m branches bs where the element is replaced by the respective 
  -- constructor arguments
  node : {k : ℕ}{D : DataDesc m} (p : Δ [ k ]∶Σ[ ⊤ ] (λ _ → μ D))
    → (bs : (con : Fin m) → CaseTree 
        (expandTel Δ (λ _ → conTel (μ D) (proj₂ (D con))) 
          (λ _ args → ⟨ con , telToCon args ⟩) p)
        (expandSort p T))
    → CaseTree Δ T

-- example case tree of the not function
CTNotRoot : CaseTree (_ ∈ μ BoolD , nil) (λ _ → μ BoolD) 
CTNotRoot = node (here tt) λ where
  (fzero)      → leaf (λ _ → false')
  (fsuc fzero) → leaf (λ _ → true')     

-- example case tree of the half function
CTHalfRoot : CaseTree halfΔ (λ _ → μ NatD)
CTHalfRoot = node (here tt) (λ where 
  (fzero) → leaf (λ where 
    (lift tt , tt) → zero')
  (fsuc fzero) → node (here tt) (λ where 
    (fzero) → leaf (λ where 
      (((Hzero , lift tt) , lift tt) , tt) → zero')
    (fsuc fzero) → leaf (λ where 
      (n , ((Hzero , ((Hsuc , b) , lift tt)) , lift tt) , tt) → suc' Hsuc)))
    
-- example case tree of the + function
+P : μ NatD → Set 
+P n = (t : ⟦ n ∈ μ NatD , m ∈ μ NatD , nil ⟧telD) → n ≡ proj₁ t → μ NatD

+Δ : Telescope 3
+Δ = n ∈ μ NatD , m ∈ μ NatD , b ∈ Below +P n , nil

CT+ : CaseTree +Δ (λ _ → μ NatD) 
CT+ = node (here tt) (λ where 
  (fzero) → leaf (λ where 
    (m , b , tt) → m) 
  (fsuc fzero) → leaf (λ where 
    (n , m , ((H , b) , _) , tt) → suc' (H (n , (m , tt)) refl)))

-- example case tree of the create function
CTCreateRoot : {X : Set} → CaseTree (createΔ {X}) (createT {X})
CTCreateRoot {X} = node (here tt) (λ where
  (fzero) → leaf (λ _ → nilV) 
  (fsuc fzero) → leaf (λ where 
    (n , (a , (((n' , _) , _) , _))) → consV n a n'))

