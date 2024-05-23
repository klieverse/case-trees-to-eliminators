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
  i j n m : ℕ
  ℓ       : Level

-- defines the description for datatypes indexed by a vector of non-indexed datatypes
data ConDesc (IΔ : Telescope i) : ℕ → Set₁ where
  one' : ⟦ IΔ ⟧telD → ConDesc IΔ 0     
  Σ'   : (S : Set) → (D : S → ConDesc IΔ n) → ConDesc IΔ (suc n)              
  ×'   : ⟦ IΔ ⟧telD → ConDesc IΔ n → ConDesc IΔ (suc n)

DataDesc : (j : ℕ)(Δ : Telescope i) → Set₁
DataDesc j Δ = (s : Fin j) → Σ[ n ∈ ℕ ] (ConDesc Δ n)

-- interpretation of description
⟦_⟧c : {IΔ : Telescope i} → ConDesc IΔ n → (⟦ IΔ ⟧telD → Set) 
  → ⟦ IΔ ⟧telD → Set
⟦ one' d ⟧c  X t = d ≡ t
⟦ Σ' S D ⟧c  X t = Σ[ s ∈ S ] (⟦ D s ⟧c X t)
⟦ ×' d D ⟧c  X t = X d × ⟦ D ⟧c X t

⟦_⟧ : {IΔ : Telescope i} → DataDesc n IΔ → (⟦ IΔ ⟧telD → Set) → ⟦ IΔ ⟧telD → Set
⟦_⟧ {n = n} D X t = Σ[ s ∈ Fin n ] (⟦ proj₂ (D s) ⟧c X t)

-- fix point
data μ {IΔ : Telescope i}(D : DataDesc n IΔ) : ⟦ IΔ ⟧telD → Set where 
    ⟨_⟩ : {d : ⟦ IΔ ⟧telD} (x : ⟦ D ⟧ (μ D) d) → μ D d



-- example natural numbers 
NatD : DataDesc 2 nil
NatD fzero = _ , one' tt
NatD (fsuc fzero) = _ , ×' tt (one' tt)

pattern zero' = ⟨ fzero , refl ⟩ 
pattern suc' n = ⟨ fsuc fzero , (n , refl) ⟩

suc₁ : (n : μ NatD tt) → μ NatD tt 
suc₁ n = ⟨ fsuc fzero , (n , refl) ⟩

-- example vector
VecTel : Telescope 1
VecTel = n ∈ μ NatD tt , nil

VecD : (X : Set) → DataDesc 2 VecTel
VecD X fzero = _ , one' (zero' , tt) 
VecD X (fsuc fzero) = _ , Σ' (μ NatD tt) (λ n → 
    Σ' X (λ x → ×' (n , tt) (one' (suc' n , tt))))

pattern nil' = ⟨ fzero , refl ⟩ 
pattern cons' n x xs = ⟨ fsuc fzero , (n , (x , (xs , refl))) ⟩

cons₁ : (X : Set) (n : μ NatD tt) (x : X) (xs : μ (VecD X) (n , tt)) → μ (VecD X) (suc' n , tt)
cons₁ X n x xs = ⟨ fsuc fzero , (n , (x , (xs , refl))) ⟩

-- example _≡_
≡D : {A : Set} (a : A) → DataDesc 1 (a ∈ A , nil)
≡D a fzero = _ , one' (a , tt)

idp' : {A : Set} (a : A) → μ (≡D a) (a , tt)
idp' a = ⟨ fzero , refl  ⟩

pattern idp a = ⟨ fzero , refl {x = (a , tt)} ⟩

-- example Square
SquareD : {A : Set} (a : A) → DataDesc 1 (b ∈ A , c ∈ A , d ∈ A , p ∈ μ (≡D a) (b , tt) , 
    q ∈ μ (≡D c) (d , tt) , r ∈ μ (≡D a) (c , tt) , s ∈ μ (≡D b) (d , tt) , nil)
SquareD a fzero = _ , one' (a , a , a , idp a , idp a , idp a , idp a , tt)

ids : {A : Set} (a : A) → μ (SquareD a) (a , a , a , idp a , idp a , idp a , idp a , tt)
ids a = ⟨ fzero , refl {x = (a , a , a , idp a , idp a , idp a , idp a , tt)} ⟩

flip : {A : Set} (w x y z : A) (t : μ (≡D w) (x , tt)) (b : μ (≡D y) (z , tt)) (l : μ (≡D w) (y , tt)) (r : μ (≡D x) (z , tt)) 
    → μ (SquareD w) (x , y , z , t , b , l , r , tt) → μ (SquareD w) (y , x , z , l , r , t , b , tt)
flip w .w .w .w ⟨ fzero , refl ⟩ ⟨ fzero , refl  ⟩ ⟨ fzero , refl  ⟩ ⟨ fzero , refl ⟩ ⟨ fzero , refl ⟩ 
    = ids w


-- gets constructor index from fix point
conᵢ : {IΔ : Telescope i}{D : DataDesc n IΔ}{d : ⟦ IΔ ⟧telD} → μ D d → Fin n
conᵢ ⟨ x ⟩ = proj₁ x 

-- gets number of constructor elements from fix point
conₙ : {IΔ : Telescope i}{D : DataDesc n IΔ}{d : ⟦ IΔ ⟧telD} → μ D d → ℕ
conₙ {D = D} ⟨ k , _ ⟩ = proj₁ (D k)


-- collects every subobject in D
AllC :{IΔ : Telescope i}(C : ConDesc IΔ n)(X : ⟦ IΔ ⟧telD → Set) 
            (P : (d : ⟦ IΔ ⟧telD) → X d → Set ℓ)(d : ⟦ IΔ ⟧telD)(xs : ⟦ C ⟧c X d) → Set ℓ
AllC (one' v)  X P d e        = Lift _ ⊤
AllC (Σ' S D)  X P d (s , t)  = AllC (D s) X P d t
AllC (×' d' D) X P d (x' , t) = (P d' x') × (AllC D X P d t)

All : {IΔ : Telescope i} (D : DataDesc n IΔ)(X : ⟦ IΔ ⟧telD → Set) 
    (P : (d : ⟦ IΔ ⟧telD) → X d → Set ℓ)(d : ⟦ IΔ ⟧telD)(xs : ⟦ D ⟧ X d ) → Set ℓ
All D X P d (s , t) = AllC (proj₂ (D s)) X P d t

-- generic elimination principle for datatype description
elim-μ : {IΔ : Telescope i}(D : DataDesc n IΔ)(P : (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ)  
    → (m : (d : ⟦ IΔ ⟧telD) → (x : ⟦ D ⟧ (μ D) d) → All D (μ D) P d x → P d ⟨ x ⟩)
    → (d : ⟦ IΔ ⟧telD) → (x : μ D d) → P d x 
elim-μ {n = n} {IΔ = IΔ} D P m d ⟨ x ⟩ = m d x (all D D P m d x) where 

    allC : {i m : ℕ}{IΔ : Telescope i}(D : ConDesc IΔ m)(E : DataDesc n IΔ)
        (P : (d : ⟦ IΔ ⟧telD) → μ E d → Set ℓ) 
        (m : (d : ⟦ IΔ ⟧telD) → (x : ⟦ E ⟧ (μ E) d) → All E (μ E) P d x → P d ⟨ x ⟩)
        (d : ⟦ IΔ ⟧telD) → (x : ⟦ D ⟧c (μ E) d) → AllC D (μ E) P d x
    allC (one' v) E P m d e = lift tt
    allC (Σ' S D) E P m d (s , t) = allC (D s) E P m d t
    allC (×' d' D) E P m d (x , t) = elim-μ E P m d' x , allC D E P m d t

    all : (D E : DataDesc n IΔ)(P : (d : ⟦ IΔ ⟧telD) → μ E d → Set ℓ) 
        (m : (d : ⟦ IΔ ⟧telD) → (x : ⟦ E ⟧ (μ E) d) → All E (μ E) P d x → P d ⟨ x ⟩)
        (d : ⟦ IΔ ⟧telD) → (x : ⟦ D ⟧ (μ E) d) → All D (μ E) P d x
    all D E P m d (x , t) = allC (proj₂ (D x)) E P m d t

-- generic case-D eliminator
case-μ : {IΔ : Telescope i}(D : DataDesc n IΔ)(P : (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ)  
    → (m : (d : ⟦ IΔ ⟧telD) → (x : ⟦ D ⟧ (μ D) d) → P d ⟨ x ⟩)
    → (d : ⟦ IΔ ⟧telD) → (x : μ D d) → P d x 
case-μ D P m d x = elim-μ D P (λ d x h → m d x) d x

-- collects all recursive calls for μ D d
Below : {IΔ : Telescope i}{D : DataDesc n IΔ}(P : (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ) 
        → (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ
Below {ℓ = ℓ} {IΔ = IΔ} {D} P d ⟨ k , c ⟩ = BelowC (proj₂ (D k)) c module _ where 

    BelowC : {m : ℕ}(C : ConDesc IΔ m)(c : ⟦ C ⟧c (μ D) d) → Set ℓ
    BelowC (one' v) e = Lift _ ⊤
    BelowC (Σ' S E) (s , c) = BelowC (E s) c
    BelowC (×' d' C) (u , c) = (P d' u × Below P d' u) × (BelowC C c)

-- proof that P holds for all calls in μ D d
below : {IΔ : Telescope i}{D : DataDesc n IΔ}(P : (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ) 
    → (p : (d : ⟦ IΔ ⟧telD) → (x : μ D d) → Below P d x → P d x) 
    → (d : ⟦ IΔ ⟧telD) → (x : μ D d) → Below P d x
below {IΔ = IΔ} {D} P p d ⟨ k , c ⟩ = belowC (proj₂ (D k)) c where

    belowC : {m : ℕ}(C' : ConDesc IΔ m)(c' : ⟦ C' ⟧c (μ D) d) → BelowC P d k c C' c'
    belowC (one' v) e = lift tt
    belowC (Σ' S E) (s , c') = belowC (E s) c'
    belowC (×' d' C') (u , c') = ((p d' u (below P p d' u) , below P p d' u) , belowC C' c')

-- proof that P holds for μ D d
rec : {IΔ : Telescope i}{D : DataDesc n IΔ}(P : (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ) 
    → (p : (d : ⟦ IΔ ⟧telD) → (x : μ D d) → Below P d x → P d x) 
    → (d : ⟦ IΔ ⟧telD) → (x : μ D d) → P d x
rec P p d x = p d x (below P p d x) 