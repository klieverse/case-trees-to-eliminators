-- {-# OPTIONS --allow-unsolved-metas #-}
module Indexed.datatypes where

open import Non_Indexed.telescope using (Telescope; nil; cons; ⟦_⟧telD)

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Agda.Builtin.Unit
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_)
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

linvJ' : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : (y : A) → y ≡ x → Set ℓ')
            → {y : A} (e : y ≡ x) → (p : P y e) → P x refl
linvJ' {x = x} P {y = y} e p = subst (λ xe → P (proj₁ xe) (proj₂ xe)) (J' (λ y e → (y , e) ≡ (x , refl)) refl e) p 


data ConDesc {j : ℕ}(IΔ : Telescope j) : (i : ℕ) → Set₁ where
  one' : ⟦ IΔ ⟧telD → ConDesc IΔ zero     
  Σ'   : {i : ℕ}(S : Set) → (D : S → ConDesc IΔ i) → ConDesc IΔ (suc i)              
  ×'   : {i : ℕ} → ⟦ IΔ ⟧telD → ConDesc IΔ i → ConDesc IΔ (suc i)

⟦_⟧c : ∀ {i j : ℕ}{IΔ : Telescope j} → ConDesc IΔ i → (⟦ IΔ ⟧telD → Set) 
  → ⟦ IΔ ⟧telD → Set
⟦ one' d ⟧c  X t = d ≡ t
⟦ Σ' S D ⟧c  X t = Σ[ s ∈ S ] (⟦ D s ⟧c X t)
⟦ ×' d D ⟧c  X t = X d × ⟦ D ⟧c X t

DataDesc : {j : ℕ}(i : ℕ)(Δ : Telescope j) → Set₁
DataDesc {j} i Δ = (s : Fin i) → Σ[ n ∈ ℕ ] (ConDesc Δ n)

⟦_⟧ : {i j : ℕ}{IΔ : Telescope j} → DataDesc i IΔ → (⟦ IΔ ⟧telD → Set) → ⟦ IΔ ⟧telD → Set
⟦_⟧ {i} {j} {IΔ} D X t = Σ[ s ∈ Fin i ] (⟦ proj₂ (D s) ⟧c X t)

data μ {i j : ℕ}{IΔ : Telescope j}(D : DataDesc i IΔ) : ⟦ IΔ ⟧telD → Set where 
    ⟨_⟩ : {d : ⟦ IΔ ⟧telD} (x : ⟦ D ⟧ (μ D) d) → μ D d

conᵢ : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d : ⟦ IΔ ⟧telD} → μ D d → Fin i 
conᵢ ⟨ x ⟩ = proj₁ x 

μx : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d : ⟦ IΔ ⟧telD} → μ D d → ⟦ D ⟧ (μ D) d
μx ⟨ x ⟩ = x 

ConDesci : {i j : ℕ}{IΔ : Telescope j} → ConDesc IΔ i → ℕ 
ConDesci {i} _ = i

conₙ : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d : ⟦ IΔ ⟧telD} → μ D d → ℕ
conₙ {D = D} ⟨ fst , snd ⟩ = ConDesci (proj₂ (D fst))


AllC : ∀{ℓ} {i k : ℕ}{IΔ : Telescope i}(C : ConDesc IΔ k)(X : ⟦ IΔ ⟧telD → Set) 
            (P : (d : ⟦ IΔ ⟧telD) → X d → Set ℓ)(d : ⟦ IΔ ⟧telD)(xs : ⟦ C ⟧c X d) → Set ℓ
AllC {ℓ} (one' v) X P d e = Lift ℓ ⊤
AllC (Σ' S D) X P d (s , t) = AllC (D s) X P d t
AllC (×' d' D) X P d (x' , t) = (P d' x') × (AllC D X P d t)

All : ∀{ℓ}{i j : ℕ}{IΔ : Telescope j} (D : DataDesc i IΔ)(X : ⟦ IΔ ⟧telD → Set) 
    (P : (d : ⟦ IΔ ⟧telD) → X d → Set ℓ)(d : ⟦ IΔ ⟧telD)(xs : ⟦ D ⟧ X d ) → Set ℓ
All D X P d (s , t) = AllC (proj₂ (D s)) X P d t

elim-μ : ∀{ℓ} {i j : ℕ}{IΔ : Telescope j}(D : DataDesc i IΔ)(P : (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ)  
    → (m : (d : ⟦ IΔ ⟧telD) → (x : ⟦ D ⟧ (μ D) d) → All D (μ D) P d x → P d ⟨ x ⟩)
    → (d : ⟦ IΔ ⟧telD) → (x : μ D d) → P d x 
elim-μ {ℓ} {i} {j} {IΔ} D P m d ⟨ x ⟩ = m d x (all D D P m d x) where 

    allC : {j k : ℕ}{IΔ : Telescope j}(D : ConDesc IΔ k)(E : DataDesc i IΔ)
        (P : (d : ⟦ IΔ ⟧telD) → μ E d → Set ℓ) 
        (m : (d : ⟦ IΔ ⟧telD) → (x : ⟦ E ⟧ (μ E) d) → All E (μ E) P d x → P d ⟨ x ⟩)
        (d : ⟦ IΔ ⟧telD) → (x : ⟦ D ⟧c (μ E) d) → AllC D (μ E) P d x
    allC (one' v) E P m d e = lift tt
    allC (Σ' S D) E P m d (s , t) = allC (D s) E P m d t
    allC (×' d' D) E P m d (x , t) = elim-μ E P m d' x , allC D E P m d t

    all : (D E : DataDesc i IΔ)(P : (d : ⟦ IΔ ⟧telD) → μ E d → Set ℓ) 
        (m : (d : ⟦ IΔ ⟧telD) → (x : ⟦ E ⟧ (μ E) d) → All E (μ E) P d x → P d ⟨ x ⟩)
        (d : ⟦ IΔ ⟧telD) → (x : ⟦ D ⟧ (μ E) d) → All D (μ E) P d x
    all D E P m d (x , t) = allC (proj₂ (D x)) E P m d t

case-μ : ∀{ℓ}{i j : ℕ}{IΔ : Telescope j}(D : DataDesc i IΔ)(P : (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ)  
    → (m : (d : ⟦ IΔ ⟧telD) → (x : ⟦ D ⟧ (μ D) d) → P d ⟨ x ⟩)
    → (d : ⟦ IΔ ⟧telD) → (x : μ D d) → P d x 
case-μ {ℓ} {i} D P m d x = elim-μ D P (λ d x h → m d x) d x

-- Below
Below : ∀ {ℓ} {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}(P : (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ) 
        → (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ
Below {ℓ} {i} {j} {IΔ} {D} P d ⟨ n , c ⟩ = BelowC (proj₂ (D n)) c module _ where 

    BelowC : {k : ℕ}(C : ConDesc IΔ k)(c : ⟦ C ⟧c (μ D) d) → Set ℓ
    BelowC (one' v) e = Lift ℓ ⊤
    BelowC (Σ' S E) (s , c) = BelowC (E s) c
    BelowC (×' d' C) (u , c) = (P d' u × Below P d' u) × (BelowC C c)

below : ∀ {ℓ} {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}(P : (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ) 
    → (p : (d : ⟦ IΔ ⟧telD) → (x : μ D d) → Below P d x → P d x) 
    → (d : ⟦ IΔ ⟧telD) → (x : μ D d) → Below P d x
below {ℓ} {i} {j} {IΔ} {D} P p d ⟨ n , c ⟩ = belowC (proj₂ (D n)) c where

    belowC : {k : ℕ}(C' : ConDesc IΔ k)(c' : ⟦ C' ⟧c (μ D) d) → BelowC P d n c C' c'
    belowC (one' v) e = lift tt
    belowC (Σ' S E) (s , c') = belowC (E s) c'
    belowC (×' d' C') (u , c') = ((p d' u (below P p d' u) , below P p d' u) , belowC C' c')

rec : ∀ {ℓ} {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}(P : (d : ⟦ IΔ ⟧telD) → μ D d → Set ℓ) 
    → (p : (d : ⟦ IΔ ⟧telD) → (x : μ D d) → Below P d x → P d x) 
    → (d : ⟦ IΔ ⟧telD) → (x : μ D d) → P d x
rec P p d x = p d x (below P p d x) 