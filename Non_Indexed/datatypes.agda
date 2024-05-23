-- {-# OPTIONS --allow-unsolved-metas #-}

module Non_Indexed.datatypes where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Data.Sum
open import Data.Unit.Base
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Fin using (Fin; fromℕ<; fromℕ; toℕ; raise; _≟_ ) 
    renaming (zero to fzero; suc to fsuc)

open import lib

private variable
  i n : ℕ
  ℓ   : Level

-- defines a constructor description
data ConDesc : (i : ℕ) → Set₁ where
  -- the empty constructor  
  one'   : ConDesc 0   
  -- constructor argument                           
  Σ'     : (S : Set) → (D : S → ConDesc i) → ConDesc (suc i) 
  -- inductive argument
  ind×'  : (D : ConDesc i) → ConDesc (suc i)                  

-- define a datatype description as a function from a 
-- constructor index to the constructor description
DataDesc : (i : ℕ) → Set₁
DataDesc i = (s : Fin i) → Σ[ n ∈ ℕ ] (ConDesc n)

-- example booleans
BoolD : DataDesc 2
BoolD fzero        = _ , one' -- true
BoolD (fsuc fzero) = _ , one' -- false

-- example natural numbers
NatD : DataDesc 2 
NatD fzero        = _ , one'        -- zero
NatD (fsuc fzero) = _ , ind×' one'  -- suc

-- interpretation of descriptions
⟦_⟧c : ConDesc i → Set → Set
⟦ one'    ⟧c X = ⊤ 
⟦ Σ' S D  ⟧c X = Σ[ s ∈ S ] (⟦ D s ⟧c X)
⟦ ind×' D ⟧c X = X × (⟦ D ⟧c X)

⟦_⟧ : DataDesc i → Set → Set
⟦_⟧ {i} D X = Σ[ j ∈ Fin i ] (⟦ proj₂ (D j) ⟧c X)

-- fix point
data μ (D : DataDesc i) : Set where 
    ⟨_⟩ : (d : ⟦ D ⟧ (μ D)) → μ D

-- example booleans
pattern true'  = ⟨ fzero , tt ⟩
pattern false' = ⟨ fsuc fzero , tt ⟩

not : μ BoolD → μ BoolD
not true'  = false' 
not false' = true' 

-- example natural numbers
pattern zero' = ⟨ fzero , tt ⟩ 
pattern suc' n = ⟨ fsuc fzero , (n , tt) ⟩

_+'_ : μ NatD → μ NatD → μ NatD 
zero'  +' m = m 
suc' n +' m = suc' (n +' m)

half : μ NatD → μ NatD
half zero' = zero' 
half (suc' zero') = zero' 
half (suc' (suc' n)) = suc' (half n) 

-- example vector 
data Vec (X : Set) : (n : μ NatD) → Set where 
  nilV : Vec X zero' 
  consV : (n : μ NatD) → (x : X) → Vec X n → Vec X (suc' n)

create : {X : Set} (n : μ NatD) → (x : X) → Vec X n 
create zero' x = nilV
create (suc' n) x = consV n x (create n x)


-- gets constructor index from fix point
conᵢ : {D : DataDesc i} → μ D → Fin i 
conᵢ ⟨ x ⟩ = proj₁ x 

-- gets number of constructor elements from fix point
conₙ : {D : DataDesc i} → μ D → ℕ
conₙ {D = D} ⟨ k , _ ⟩ = proj₁ (D k)


-- collects every subobject in D
AllC : (D : ConDesc i)(X : Set) (P : X → Set ℓ) (xs : ⟦ D ⟧c X) → Set ℓ
AllC one'      X P _       = Lift _ ⊤
AllC (Σ' S D)  X P (s , d) = AllC (D s) X P d
AllC (ind×' D) X P (x , d) = (P x) × (AllC D X P d)

All : (D : DataDesc i)(X : Set) (P : X → Set ℓ) (xs : ⟦ D ⟧ X ) → Set ℓ
All D X P (s , d) = AllC (proj₂ (D s)) X P d

-- generic elimination principle for datatype description
elim-μ : (D : DataDesc i)(P : (μ D) → Set ℓ)  
    → (m : (d : ⟦ D ⟧ (μ D)) → All D (μ D) P d → P ⟨ d ⟩) 
    → (x : μ D) → P x 
elim-μ {i} {ℓ} D P m ⟨ d ⟩ = m d (all D D P m d) where 

    allC : {j : ℕ}(D : ConDesc j)(E : DataDesc i)(P : μ E → Set ℓ) 
        (m : (d : ⟦ E ⟧ (μ E)) → All E (μ E) P d → P ⟨ d ⟩)
        (d : ⟦ D ⟧c (μ E) ) → AllC D (μ E) P d
    allC one'      E P m tt       = lift tt
    allC (Σ' S D)  E P m (s , d) = allC (D s) E P m d
    allC (ind×' D) E P m (x , d) = elim-μ E P m x , allC D E P m d

    all : (D E : DataDesc i)(P : μ E → Set ℓ) 
        (m : (d : ⟦ E ⟧ (μ E)) → All E (μ E) P d → P ⟨ d ⟩)
        (d : ⟦ D ⟧ (μ E) ) → All D (μ E) P d
    all D E P m (s , d) = allC (proj₂ (D s)) E P m d

-- example natural numbers
_+₁_ : μ NatD → μ NatD → μ NatD
n +₁ m = elim-μ NatD (λ n → μ NatD → μ NatD) (λ where
  (fzero      , tt    ) (lift tt)     m → m
  (fsuc fzero , n , tt) (h , lift tt) m → suc' (h m)) n m

-- generic case-D eliminator for datatype description D
case-μ : (D : DataDesc i)(P : (μ D) → Set ℓ)  
    → (m : (d : ⟦ D ⟧ (μ D)) → P ⟨ d ⟩) → (x : μ D) → P x 
case-μ {i} {ℓ} D P m d = elim-μ D P (λ d h → m d) d


-- collects all recursive calls for μ D
Below : {D : DataDesc i} → (P : μ D → Set ℓ) → (d : μ D) → Set ℓ
Below {i} {ℓ} {D} P ⟨ n , c ⟩ = BelowC (proj₂ (D n)) c module _ where 

    BelowC : {j : ℕ}(C : ConDesc j)(c : ⟦ C ⟧c (μ D)) → Set ℓ
    BelowC one' tt = Lift ℓ ⊤
    BelowC (Σ' S E) (s , c) = BelowC (E s) c
    BelowC (ind×' C) (u , c) = (P u × Below P u) × (BelowC C c)

-- proof that P holds for all recursive calls in μ D
below : {D : DataDesc i} → (P : μ D → Set ℓ) → (p : (d : μ D) → Below P d → P d) 
    → (d : μ D) → Below P d 
below {i} {ℓ} {D} P p ⟨ n , c ⟩ = belowC (proj₂ (D n)) c where

    belowC : {j : ℕ}(C' : ConDesc j) → (c' : ⟦ C' ⟧c (μ D)) → BelowC P n c C' c'
    belowC one' tt = lift tt
    belowC (Σ' S E) (s , c') = belowC (E s) c'
    belowC (ind×' C') (u , c') = (((p u (below P p u)) , below P p u ) , belowC C' c' )

-- proof that P holds for μ D
rec : {D : DataDesc i} → (P : μ D → Set ℓ) → (p : (d : μ D) → Below P d → P d) 
    → (d : μ D) → P d 
rec P p d = p d (below P p d) 

-- example natural number 
_+₂'_ : (n : μ NatD) → μ NatD → Below (λ n → μ NatD → μ NatD) n → μ NatD
(n +₂' m) h = case-μ NatD 
  (λ n → Below (λ n → μ NatD → μ NatD) n → μ NatD → μ NatD) (λ where
    (fzero      , tt    ) (lift tt)           m → m
    (fsuc fzero , n , tt) ((h , b) , lift tt) m → suc' (h m)) n h m

_+₂_ : μ NatD → μ NatD → μ NatD
n +₂ m = (n +₂' m) (below (λ n → μ NatD → μ NatD) (λ n h m → (n +₂' m) h) n)

-- example course-of-value iteration fibonacci function
fib' : (n : μ NatD) → Below (λ n → μ NatD) n → μ NatD 
fib' = case-μ NatD (λ n → Below (λ n → μ NatD) n → μ NatD) (λ where
  (fzero      , tt    ) (lift tt)           → zero'
  (fsuc fzero , n , tt) ((h , b) , lift tt) → case-μ NatD (λ n → Below (λ n → μ NatD) n → μ NatD) (λ where
    (fzero      , tt    ) (lift tt)             → suc' zero'
    (fsuc fzero , n' , tt) ((h' , b) , lift tt) → h +' h') n b)

fib : (n : μ NatD) → μ NatD 
fib n =  fib' n (below (λ n → μ NatD) (λ n h → fib' n h) n)