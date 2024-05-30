-- {-# OPTIONS --allow-unsolved-metas #-}
module Indexed.datatypes where

open import lib
open import Non_Indexed.telescope using (Telescope; nil; cons; ⟦_⟧telD)

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Agda.Builtin.Unit
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_)
open import Data.Fin using (Fin; fromℕ<; fromℕ; toℕ; raise; _≟_ ) renaming (zero to fzero; suc to fsuc)

private variable
  cₙ dₙ iₙ : ℕ
  ℓ   : Level

-- defines the description for datatypes indexed by a vector of non-indexed datatypes
data ConDesc (is : Telescope iₙ) : ℕ → Set₁ where
  one' : ⟦ is ⟧telD → ConDesc is 0     
  Σ'   : (S : Set) → (D : S → ConDesc is cₙ) → ConDesc is (suc cₙ)              
  ×'   : ⟦ is ⟧telD → ConDesc is cₙ → ConDesc is (suc cₙ)

DataDesc : Telescope iₙ → ℕ → Set₁
DataDesc is dₙ = Fin dₙ → Σ ℕ (ConDesc is)

private variable
  is : Telescope iₙ

-- interpretation of description
⟦_⟧c : ConDesc is cₙ → (⟦ is ⟧telD → Set) → ⟦ is ⟧telD → Set
⟦ one' d ⟧c  X t = d ≡ t
⟦ Σ' S D ⟧c  X t = Σ[ s ∈ S ] (⟦ D s ⟧c X t)
⟦ ×' d D ⟧c  X t = X d × ⟦ D ⟧c X t

⟦_⟧ : DataDesc is dₙ → (⟦ is ⟧telD → Set) → ⟦ is ⟧telD → Set
⟦_⟧ {dₙ = dₙ} D X t = Σ[ i ∈ Fin dₙ ] (⟦ proj₂ (D i) ⟧c X t)

-- fix point
data μ (D : DataDesc is dₙ) : ⟦ is ⟧telD → Set where 
    ⟨_⟩ : {d : ⟦ is ⟧telD} (x : ⟦ D ⟧ (μ D) d) → μ D d



-- example natural numbers 
NatD : DataDesc nil 2
NatD f0        = _ , one' tt
NatD f1 = _ , ×' tt (one' tt)

pattern zero'  = ⟨ f0 , refl ⟩ 
pattern suc' n = ⟨ f1 , (n , refl) ⟩

suc₁ : μ NatD tt → μ NatD tt 
suc₁ n = ⟨ f1 , (n , refl) ⟩

-- example vector
VecTel : Telescope 1
VecTel = n ∈ μ NatD tt , nil

VecD : (X : Set) → DataDesc VecTel 2
VecD X f0        = _ , one' (zero' , tt) 
VecD X f1 = _ , Σ' (μ NatD tt) (λ n → 
    Σ' X (λ x → ×' (n , tt) (one' (suc' n , tt))))

pattern nil'         = ⟨ f0 , refl ⟩ 
pattern cons' n x xs = ⟨ f1 , (n , (x , (xs , refl))) ⟩

cons₁ : (X : Set) (n : μ NatD tt) → X → μ (VecD X) (n , tt) → μ (VecD X) (suc' n , tt)
cons₁ X n x xs = ⟨ f1 , (n , (x , (xs , refl))) ⟩

-- example _≡_
≡D : {A : Set} (a : A) → DataDesc (a ∈ A , nil) 1
≡D a f0 = _ , one' (a , tt)

idp' : {A : Set} (a : A) → μ (≡D a) (a , tt)
idp' a = ⟨ f0 , refl  ⟩

pattern idp a = ⟨ f0 , refl {x = (a , tt)} ⟩

-- example Square
SquareD : {A : Set} (a : A) → DataDesc (b ∈ A , c ∈ A , d ∈ A , p ∈ μ (≡D a) (b , tt) , 
    q ∈ μ (≡D c) (d , tt) , r ∈ μ (≡D a) (c , tt) , s ∈ μ (≡D b) (d , tt) , nil) 1
SquareD a f0 = _ , one' (a , a , a , idp a , idp a , idp a , idp a , tt)

ids : {A : Set} (a : A) → μ (SquareD a) (a , a , a , idp a , idp a , idp a , idp a , tt)
ids a = ⟨ f0 , refl {x = (a , a , a , idp a , idp a , idp a , idp a , tt)} ⟩

flip : {A : Set} (w x y z : A) (t : μ (≡D w) (x , tt)) (b : μ (≡D y) (z , tt)) (l : μ (≡D w) (y , tt)) (r : μ (≡D x) (z , tt)) 
    → μ (SquareD w) (x , y , z , t , b , l , r , tt) → μ (SquareD w) (y , x , z , l , r , t , b , tt)
flip w .w .w .w ⟨ f0 , refl ⟩ ⟨ f0 , refl  ⟩ ⟨ f0 , refl  ⟩ ⟨ f0 , refl ⟩ ⟨ f0 , refl ⟩ 
    = ids w


-- gets constructor index from fix point
conᵢ : {D : DataDesc is dₙ}{d : ⟦ is ⟧telD} → μ D d → Fin dₙ
conᵢ ⟨ x ⟩ = proj₁ x 

-- gets number of constructor elements from fix point
conₙ : {D : DataDesc is dₙ}{d : ⟦ is ⟧telD} → μ D d → ℕ
conₙ {D = D} ⟨ i , _ ⟩ = proj₁ (D i)


-- collects every subobject in D
AllC : (C : ConDesc is cₙ)(X : ⟦ is ⟧telD → Set) 
    (P : (d : ⟦ is ⟧telD) → X d → Set ℓ)(d : ⟦ is ⟧telD)(xs : ⟦ C ⟧c X d) → Set ℓ
AllC (one' v)  X P d e        = Lift _ ⊤
AllC (Σ' S D)  X P d (s , t)  = AllC (D s) X P d t
AllC (×' d' D) X P d (x' , t) = (P d' x') × (AllC D X P d t)

All :  (D : DataDesc is dₙ)(X : ⟦ is ⟧telD → Set) 
    (P : (d : ⟦ is ⟧telD) → X d → Set ℓ)(d : ⟦ is ⟧telD)(xs : ⟦ D ⟧ X d ) → Set ℓ
All D X P d (s , t) = AllC (proj₂ (D s)) X P d t

-- generic elimination principle for datatype description
elim-μ : (D : DataDesc is dₙ)(P : (d : ⟦ is ⟧telD) → μ D d → Set ℓ)  
    → (m : (d : ⟦ is ⟧telD) → (x : ⟦ D ⟧ (μ D) d) → All D (μ D) P d x → P d ⟨ x ⟩)
    → (d : ⟦ is ⟧telD) → (x : μ D d) → P d x 
elim-μ {is = is} {dₙ = dₙ} D P m d ⟨ x ⟩ = m d x (all D D P m d x) where 

    allC : (D : ConDesc is cₙ)(E : DataDesc is dₙ)
        (P : (d : ⟦ is ⟧telD) → μ E d → Set ℓ) 
        (m : (d : ⟦ is ⟧telD) → (x : ⟦ E ⟧ (μ E) d) → All E (μ E) P d x → P d ⟨ x ⟩)
        (d : ⟦ is ⟧telD) → (x : ⟦ D ⟧c (μ E) d) → AllC D (μ E) P d x
    allC (one' v) E P m d e = lift tt
    allC (Σ' S D) E P m d (s , t) = allC (D s) E P m d t
    allC (×' d' D) E P m d (x , t) = elim-μ E P m d' x , allC D E P m d t

    all : (D E : DataDesc is dₙ)(P : (d : ⟦ is ⟧telD) → μ E d → Set ℓ) 
        (m : (d : ⟦ is ⟧telD) → (x : ⟦ E ⟧ (μ E) d) → All E (μ E) P d x → P d ⟨ x ⟩)
        (d : ⟦ is ⟧telD) → (x : ⟦ D ⟧ (μ E) d) → All D (μ E) P d x
    all D E P m d (x , t) = allC (proj₂ (D x)) E P m d t

-- generic case-D eliminator
case-μ : (D : DataDesc is dₙ)(P : (d : ⟦ is ⟧telD) → μ D d → Set ℓ)  
    → (m : (d : ⟦ is ⟧telD) → (x : ⟦ D ⟧ (μ D) d) → P d ⟨ x ⟩)
    → (d : ⟦ is ⟧telD) → (x : μ D d) → P d x 
case-μ D P m d x = elim-μ D P (λ d x h → m d x) d x

-- collects all recursive calls for μ D d
Below : {D : DataDesc is dₙ}(P : (d : ⟦ is ⟧telD) → μ D d → Set ℓ) 
        → (d : ⟦ is ⟧telD) → μ D d → Set ℓ
Below {is = is} {ℓ = ℓ} {D} P d ⟨ k , c ⟩ = BelowC (proj₂ (D k)) c module _ where 

    BelowC : {m : ℕ}(C : ConDesc is m)(c : ⟦ C ⟧c (μ D) d) → Set ℓ
    BelowC (one' v) e = Lift _ ⊤
    BelowC (Σ' S E) (s , c) = BelowC (E s) c
    BelowC (×' d' C) (u , c) = (P d' u × Below P d' u) × (BelowC C c)

-- proof that P holds for all calls in μ D d
below : {D : DataDesc is dₙ}(P : (d : ⟦ is ⟧telD) → μ D d → Set ℓ) 
    → (p : (d : ⟦ is ⟧telD) → (x : μ D d) → Below P d x → P d x) 
    → (d : ⟦ is ⟧telD) → (x : μ D d) → Below P d x
below {is = is} {D = D} P p d ⟨ k , c ⟩ = belowC (proj₂ (D k)) c where

    belowC : (C' : ConDesc is cₙ)(c' : ⟦ C' ⟧c (μ D) d) → BelowC P d k c C' c'
    belowC (one' v) e = lift tt
    belowC (Σ' S E) (s , c') = belowC (E s) c'
    belowC (×' d' C') (u , c') = ((p d' u (below P p d' u) , below P p d' u) , belowC C' c')

-- proof that P holds for μ D d
rec : {D : DataDesc is dₙ}(P : (d : ⟦ is ⟧telD) → μ D d → Set ℓ) 
    → (p : (d : ⟦ is ⟧telD) → (x : μ D d) → Below P d x → P d x) 
    → (d : ⟦ is ⟧telD) → (x : μ D d) → P d x
rec P p d x = p d x (below P p d x) 