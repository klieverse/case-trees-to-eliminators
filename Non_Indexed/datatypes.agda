-- {-# OPTIONS --allow-unsolved-metas #-}
module Non_Indexed.datatypes where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Data.Sum
open import Data.Unit.Base
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Fin using (Fin; fromℕ<; fromℕ; toℕ; raise; _≟_ ) renaming (zero to fzero; suc to fsuc)

J : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : (y : A) → x ≡ y → Set ℓ') → (p : P x refl) → {y : A} (e : x ≡ y) → P y e
J P p refl = p

linvJ : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : (y : A) → x ≡ y → Set ℓ')
            → {y : A} (e : x ≡ y) → (p : P y e) → P x refl
linvJ {x = x} P {y = y} e p = subst (λ xe → P (proj₁ xe) (proj₂ xe)) (J (λ y e → (y , e) ≡ (x , refl)) refl e) p 

isLinvJ : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : (y : A) → x ≡ y → Set ℓ') → (p : P x refl) → {y : A} (e : x ≡ y) 
        → linvJ P e (J P p e) ≡ p 
isLinvJ {x = x} P p e = J (λ y e → linvJ P e (J P p e) ≡ p) refl e

J' : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : (y : A) → y ≡ x → Set ℓ') → (p : P x refl) → {y : A} (e : y ≡ x) → P y e
J' P p refl = p

data ConDesc : (i : ℕ) → Set₁ where
  one'   : ConDesc zero                              
  Σ'     : {i : ℕ}(S : Set) → (D : S → ConDesc i) → ConDesc (suc i) 
  ind×'  : {i : ℕ}(D : ConDesc i) → ConDesc (suc i)                  

⟦_⟧c : {i : ℕ} → ConDesc i → Set → Set
⟦ one' ⟧c    X = ⊤ 
⟦ Σ' S D ⟧c  X = Σ[ s ∈ S ] (⟦ D s ⟧c X)
⟦ ind×' D ⟧c X = X × (⟦ D ⟧c X)

ConDesci : {i : ℕ} → ConDesc i → ℕ 
ConDesci {i} _ = i

DataDesc : (i : ℕ) → Set₁
DataDesc i = (s : Fin i) → Σ[ n ∈ ℕ ] (ConDesc n)

⟦_⟧ : {i : ℕ} → DataDesc i → Set → Set
⟦_⟧ {i} D X = Σ[ j ∈ Fin i ] (⟦ proj₂ (D j) ⟧c X)

data μ {i : ℕ}(D : DataDesc i) : Set where 
    ⟨_⟩ : (d : ⟦ D ⟧ (μ D)) → μ D

conᵢ : {i : ℕ}{D : DataDesc i} → μ D → Fin i 
conᵢ ⟨ x ⟩ = proj₁ x 

conₙ : {i : ℕ}{D : DataDesc i} → μ D → ℕ
conₙ {D = D} ⟨ fst , snd ⟩ = ConDesci (proj₂ (D fst))

AllC : ∀{ℓ} {k : ℕ}(D : ConDesc k)(X : Set) (P : X → Set ℓ) (xs : ⟦ D ⟧c X) → Set ℓ
AllC {ℓ} one'     X P _       = Lift ℓ ⊤
AllC (Σ' S D)     X P (s , d) = AllC (D s) X P d
AllC (ind×' D)    X P (x , d) = (P x) × (AllC D X P d)

All : ∀{ℓ}{i : ℕ} (D : DataDesc i)(X : Set) (P : X → Set ℓ) (xs : ⟦ D ⟧ X ) → Set ℓ
All D X P (s , d) = AllC (proj₂ (D s)) X P d

elim-μ : ∀{ℓ} {i : ℕ} (D : DataDesc i)(P : (μ D) → Set ℓ)  
    → (m : (d : ⟦ D ⟧ (μ D)) → All D (μ D) P d → P ⟨ d ⟩) 
    → (x : μ D) → P x 
elim-μ {ℓ} {i} D P m ⟨ d ⟩ = m d (all D D P m d) where 

    allC : {k : ℕ}(D : ConDesc k)(E : DataDesc i)(P : μ E → Set ℓ) 
        (m : (d : ⟦ E ⟧ (μ E)) → All E (μ E) P d → P ⟨ d ⟩)
        (d : ⟦ D ⟧c (μ E) ) → AllC D (μ E) P d
    allC one'      E P m _       = lift tt
    allC (Σ' S D)  E P m (s , d) = allC (D s) E P m d
    allC (ind×' D) E P m (x , d) = elim-μ E P m x , allC D E P m d

    all : (D E : DataDesc i)(P : μ E → Set ℓ) 
        (m : (d : ⟦ E ⟧ (μ E)) → All E (μ E) P d → P ⟨ d ⟩)
        (d : ⟦ D ⟧ (μ E) ) → All D (μ E) P d
    all D E P m (s , d) = allC (proj₂ (D s)) E P m d

case-μ : ∀{ℓ} {i : ℕ} (D : DataDesc i)(P : (μ D) → Set ℓ)  
    → (m : (d : ⟦ D ⟧ (μ D)) → P ⟨ d ⟩) → (x : μ D) → P x 
case-μ {ℓ} {i} D P m d = elim-μ D P (λ d h → m d) d

-- Below
Below : ∀ {ℓ} {i : ℕ}{D : DataDesc i} → (P : μ D → Set ℓ) → (d : μ D) → Set ℓ
Below {ℓ} {i} {D} P ⟨ n , c ⟩ = BelowC (proj₂ (D n)) c module _ where 

    BelowC : {j : ℕ}(C : ConDesc j)(c : ⟦ C ⟧c (μ D)) → Set ℓ
    BelowC one' _ = Lift ℓ ⊤
    BelowC (Σ' S E) (s , c) = BelowC (E s) c
    BelowC (ind×' C) (u , c) = (P u × Below P u) × (BelowC C c)

below : ∀ {ℓ} {i : ℕ}{D : DataDesc i} → (P : μ D → Set ℓ) → (p : (d : μ D) → Below P d → P d) 
    → (d : μ D) → Below P d 
below {ℓ} {i} {D} P p ⟨ n , c ⟩ = belowC (proj₂ (D n)) c where

    belowC : {j : ℕ}(C' : ConDesc j) → (c' : ⟦ C' ⟧c (μ D)) → BelowC P n c C' c'
    belowC one' _ = lift tt
    belowC (Σ' S E) (s , c') = belowC (E s) c'
    belowC (ind×' C') (u , c') = (((p u (below P p u)) , below P p u ) , belowC C' c' )

rec : ∀ {ℓ} {i : ℕ}{D : DataDesc i} → (P : μ D → Set ℓ) → (p : (d : μ D) → Below P d → P d) 
    → (d : μ D) → P d 
rec P p d = p d (below P p d) 