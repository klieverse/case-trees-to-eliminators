{-# OPTIONS --safe #-}
module One_Indexed.datatypes where

import Non_Indexed.datatypes as NI
open import lib

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Agda.Builtin.Unit
open import Data.Empty
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_)
open import Data.Fin using (Fin; fromℕ<; fromℕ; toℕ; raise; _≟_ ) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)

private variable
  cₙ aₙ iₙ : ℕ
  ℓ   : Level

-- vector of non-indexed indices
DVec : ℕ → Set₁
DVec = Vec (Σ ℕ NI.DataDesc)

⟦_⟧Vec : (is : DVec iₙ) → Set
⟦_⟧Vec [] = ⊤
⟦_⟧Vec ((_ , D) ∷ is) = (NI.μ D) × (⟦ is ⟧Vec)

-- example indices for a vector datatype
VecTel : DVec 1
VecTel = (_ , NI.NatD) ∷ []

nilVec : ⟦ VecTel ⟧Vec
nilVec = NI.zero' , tt

consVec : NI.μ NI.NatD → ⟦ VecTel ⟧Vec
consVec n = NI.suc' n , tt

-- example indices for a ≤-datatype
≤Tel : DVec 2 
≤Tel = (_ , NI.NatD) ∷  (_ , NI.NatD) ∷ [] 

-- example indices for nat₁ datatype 
Nat₁Tel : DVec 2
Nat₁Tel = (_ , NI.NatD) ∷  (_ , NI.NatD) ∷ []


-- defines the description for datatypes indexed by a vector of non-indexed datatypes
data ConDesc (is : DVec iₙ) : ℕ → Set₁ where
  one' : ⟦ is ⟧Vec → ConDesc is 0     
  Σ'   : (S : Set)(D : S → ConDesc is aₙ) → ConDesc is (suc aₙ)              
  ×'   : ⟦ is ⟧Vec → ConDesc is aₙ → ConDesc is (suc aₙ)

DataDesc : DVec iₙ → ℕ → Set₁
DataDesc is cₙ = Fin cₙ → Σ ℕ (ConDesc is)

-- example vector
VecD : Set → DataDesc VecTel 2
VecD X f0 = _ , one' (NI.zero' , tt) 
VecD X f1 = _ , Σ' (NI.μ NI.NatD) (λ n → 
  Σ' X (λ x → ×' (n , tt) (one' (NI.suc' n , tt))))

-- example ≤
≤D : DataDesc ≤Tel 2
≤D f0        = _ , Σ' (NI.μ NI.NatD) (λ n → one' (NI.zero' , n , tt))
≤D f1 = _ , Σ' (NI.μ NI.NatD) (λ n → 
  Σ' (NI.μ NI.NatD) (λ m → ×' (n , m , tt) (one' (NI.suc' n , NI.suc' m , tt))))

-- example nat₁ 
Nat₁D : DataDesc Nat₁Tel 2
Nat₁D f0        = _ , one' (NI.zero' , (NI.zero' , tt))
Nat₁D f1 = _ , Σ' (NI.μ NI.NatD) (λ n₁ → Σ' (NI.μ NI.NatD) (λ n₂ 
                          → ×' (n₁ , (n₂ , tt)) (one' (NI.suc' n₁ , (NI.suc' n₂ , tt)))))
    

private variable
  is : DVec iₙ

-- interpretation of description
⟦_⟧c : ConDesc is aₙ → (⟦ is ⟧Vec → Set) → ⟦ is ⟧Vec → Set
⟦ one' d ⟧c  X t = d ≡ t -- indices must be equivalent
⟦ Σ' S D ⟧c  X t = Σ[ s ∈ S ] ( ⟦ D s ⟧c X t)
⟦ ×' d D ⟧c  X t = X d × ⟦ D ⟧c X t

⟦_⟧ : DataDesc is cₙ → (⟦ is ⟧Vec → Set) → ⟦ is ⟧Vec → Set
⟦_⟧ {cₙ = cₙ} D X t = Σ[ cᵢ ∈ Fin cₙ ] (⟦ proj₂ (D cᵢ) ⟧c X t)

-- fix point
data μ (D : DataDesc is cₙ) : ⟦ is ⟧Vec → Set where 
    ⟨_⟩ : {d : ⟦ is ⟧Vec} (x : ⟦ D ⟧ (μ D) d) → μ D d

-- example head function vector 
nil₁ : (X : Set) → μ (VecD X) (NI.zero' , tt)
nil₁ X = ⟨ f0 , refl ⟩ 

cons₁ : (X : Set)(n : NI.μ NI.NatD)(x : X)(xs : μ (VecD X) (n , tt)) → μ (VecD X) (NI.suc' n , tt)
cons₁ X n x xs = ⟨ f1 , (n , (x , (xs , refl))) ⟩

pattern nil' = ⟨ f0 , refl ⟩ 
pattern cons' n x xs = ⟨ f1 , (n , (x , (xs , refl))) ⟩

head' : (X : Set) → (n : NI.μ NI.NatD) → (xs : μ (VecD X) (NI.suc' n , tt)) → X
head' X n (cons' n x xs) = x

-- example antisym function 
pattern lz n = ⟨ f0 , (n , refl) ⟩
pattern ls n m x = ⟨ f1 , (n , m , x , refl) ⟩ 

antisym : (n m : NI.μ NI.NatD)(x : μ ≤D (n , m , tt))(y : μ ≤D (m , n , tt)) → n ≡ m 
antisym .NI.zero' .NI.zero' (lz .NI.zero') (lz .NI.zero') = refl
antisym .NI.zero' m (lz .m) ⟨ f1 , _ , n , _ , () ⟩
antisym .(NI.suc' n) .(NI.suc' m) (ls n m x) (ls .m .n y) = cong NI.suc' (antisym n m x y)

-- example Nat₁-K-like-elim function 
pattern zero₁' = ⟨ f0 , refl ⟩
pattern suc₁' n₁ n₂ n = ⟨ f1 , (n₁ , (n₂ , (n , refl))) ⟩ 

Nat₁-K-like-elim : (P : (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) 
  (mzero : P NI.zero' zero₁')
  (msuc : (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
    P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁))
  (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → P n₀ n₁
Nat₁-K-like-elim P mzero msuc n zero₁' = mzero
Nat₁-K-like-elim P mzero msuc n (suc₁' n₁ _ n₂) = msuc n₁ n₂ (Nat₁-K-like-elim P mzero msuc n₁ n₂) 

    

-- collects every subobject in D
AllC : (C : ConDesc is aₙ)(X : ⟦ is ⟧Vec → Set) 
  (P : (d : ⟦ is ⟧Vec) → X d → Set ℓ)(d : ⟦ is ⟧Vec)(xs : ⟦ C ⟧c X d) → Set ℓ
AllC (one' v)  X P d _        = Lift _ ⊤
AllC (Σ' S D)  X P d (s , t)  = AllC (D s) X P d t
AllC (×' d' D) X P d (x' , t) = (P d' x') × (AllC D X P d t)

All : (D : DataDesc is cₙ)(X : ⟦ is ⟧Vec → Set) 
    (P : (d : ⟦ is ⟧Vec) → X d → Set ℓ)(d : ⟦ is ⟧Vec)(xs : ⟦ D ⟧ X d ) → Set ℓ
All D X P d (s , t) = AllC (proj₂ (D s)) X P d t

-- generic elimination principle for datatype description
elim-μ : (D : DataDesc is cₙ)(P : (d : ⟦ is ⟧Vec) → μ D d → Set ℓ)  
    → (m : (d : ⟦ is ⟧Vec) → (x : ⟦ D ⟧ (μ D) d) → All D (μ D) P d x → P d ⟨ x ⟩)
    → (d : ⟦ is ⟧Vec) → (x : μ D d) → P d x 
elim-μ {ℓ = ℓ} D P m d ⟨ x ⟩ = m d x (all D D P m d x) where 

    allC : (D : ConDesc is aₙ)(E : DataDesc is cₙ)
        (P : (d : ⟦ is ⟧Vec) → μ E d → Set ℓ) 
        (m : (d : ⟦ is ⟧Vec) → (x : ⟦ E ⟧ (μ E) d) → All E (μ E) P d x → P d ⟨ x ⟩)
        (d : ⟦ is ⟧Vec) → (x : ⟦ D ⟧c (μ E) d) → AllC D (μ E) P d x
    allC (one' v) E P m d e = lift tt
    allC (Σ' S D) E P m d (s , t) = allC (D s) E P m d t
    allC (×' d' D) E P m d (x , t) = elim-μ E P m d' x , allC D E P m d t

    all : (D E : DataDesc is cₙ)(P : (d : ⟦ is ⟧Vec) → μ E d → Set ℓ) 
        (m : (d : ⟦ is ⟧Vec) → (x : ⟦ E ⟧ (μ E) d) → All E (μ E) P d x → P d ⟨ x ⟩)
        (d : ⟦ is ⟧Vec) → (x : ⟦ D ⟧ (μ E) d) → All D (μ E) P d x
    all D E P m d (x , t) = allC (proj₂ (D x)) E P m d t

-- generic case-D eliminator
case-μ : (D : DataDesc is cₙ)(P : (d : ⟦ is ⟧Vec) → μ D d → Set ℓ)  
    → (m : (d : ⟦ is ⟧Vec) → (x : ⟦ D ⟧ (μ D) d) → P d ⟨ x ⟩)
    → (d : ⟦ is ⟧Vec) → (x : μ D d) → P d x 
case-μ D P m d x = elim-μ D P (λ d x h → m d x) d x


-- collects all recursive calls for μ D d
Below : {D : DataDesc is cₙ}(P : (d : ⟦ is ⟧Vec) → μ D d → Set ℓ) 
        → (d : ⟦ is ⟧Vec) → μ D d → Set ℓ
Below {is = is} {ℓ = ℓ} {D = D} P d ⟨ n , c ⟩ = BelowC (proj₂ (D n)) c module _ where 

    BelowC : (C : ConDesc is aₙ)(c : ⟦ C ⟧c (μ D) d) → Set ℓ
    BelowC (one' v) e = Lift ℓ ⊤
    BelowC (Σ' S E) (s , c) = BelowC (E s) c
    BelowC (×' d' C) (u , c) = (P d' u × Below P d' u) × (BelowC C c)

-- proof that P holds for all calls in μ D d
below : {D : DataDesc is cₙ}(P : (d : ⟦ is ⟧Vec) → μ D d → Set ℓ) 
    → (p : (d : ⟦ is ⟧Vec) → (x : μ D d) → Below P d x → P d x) 
    → (d : ⟦ is ⟧Vec) → (x : μ D d) → Below P d x
below {is = is} {D = D} P p d ⟨ n , c ⟩ = belowC (proj₂ (D n)) c where

    belowC : (C' : ConDesc is aₙ)(c' : ⟦ C' ⟧c (μ D) d) → BelowC P d n c C' c'
    belowC (one' v) e = lift tt
    belowC (Σ' S E) (s , c') = belowC (E s) c'
    belowC (×' d' C') (u , c') = ((p d' u (below P p d' u) , below P p d' u) , belowC C' c')

-- proof that P holds for μ D d
rec : {D : DataDesc is cₙ}(P : (d : ⟦ is ⟧Vec) → μ D d → Set ℓ) 
    → (p : (d : ⟦ is ⟧Vec) → (x : μ D d) → Below P d x → P d x) 
    → (d : ⟦ is ⟧Vec) → (x : μ D d) → P d x
rec P p d x = p d x (below P p d x) 