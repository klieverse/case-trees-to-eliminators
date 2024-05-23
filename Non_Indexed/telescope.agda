{-# OPTIONS --allow-unsolved-metas #-}
module Non_Indexed.telescope where 

open import Non_Indexed.datatypes
open import lib

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Product.Properties using (Σ-≡,≡↔≡)
open import Data.Unit.Base
open import Data.Empty
open import Function.Base using (id; _∘_)
open import Relation.Binary.PropositionalEquality
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_)
open import Data.Nat.Properties using (+-comm)
open import Data.Fin using (Fin; fromℕ; toℕ; _-_) renaming (zero to fzero; suc to fsuc)

private variable 
  n m i j k : ℕ
  ℓ         : Level

-- a telescope that is either empty or contains at least one element that the 
-- remaining telescope is dependent on
data Telescope : ℕ → Set₁ where 
    nil : Telescope 0
    cons : (S : Set) (E : (s : S) → Telescope n) → Telescope (suc n)
    
syntax cons S (λ s → T) = s ∈ S , T

-- example telescope of arguments for the half function
halfΔ : Telescope 2
halfΔ = n ∈ μ NatD , _ ∈ Below (λ n → μ NatD) n , nil

-- example telescope of arguments for the create function
createΔ : {X : Set} → Telescope 3
createΔ {X} = n ∈ μ NatD , a ∈ X , b ∈ Below (λ n → Vec X n) n , nil


-- interpretation of a telescope
⟦_⟧telD : (Δ : Telescope n) → Set
⟦ nil      ⟧telD = ⊤
⟦ cons S E ⟧telD = Σ[ s ∈ S ] (⟦ E s ⟧telD)

-- example that returns a type that is a vector of length of the first element 
-- in the interpretation of the createΔ telescope
createT : {X : Set} → ⟦ createΔ {X} ⟧telD → Set
createT {X} (n , _) = Vec X n


-- B aatatype that states that the element at a location in the telescope is of 
-- type (B a) for some B aerived from the first part of the telescope
data TelAt (A : Set) (B : A → Set) : Telescope n → ℕ → Set₁ where

  here  : (a : A) {E : (y : B a) → Telescope i}
        → TelAt A B (y ∈ B a , E y) 0

  there : {S : Set} {E : S → Telescope (suc i)}
        → ((s : S) → TelAt A B (E s) k)
        → TelAt A B (s ∈ S , E s) (suc k)

syntax TelAt A B Δ k = Δ [ k ]∶Σ[ A ] B

-- example at location 1 there is a natural number
_ : (x ∈ μ NatD , y ∈ μ NatD , nil) [ 1 ]∶Σ[ ⊤ ] (λ _ → μ NatD)
_ = there (λ x → here tt)

-- example at location 1 there is an element of the Fin type 
_ : (x ∈ ℕ , y ∈ Fin x , nil) [ 1 ]∶Σ[ ℕ ] Fin
_ = there (λ x → here x)


-- B aatatype that states that the element at a location in the telescope is of 
-- type (B a) for some B aerived from the first part of the telescope 
-- and the element at the next location is of type C a b for (b : B a)
data TelAt' (A : Set) (B : A → Set) (C : (a : A) → B a → Set) : Telescope i → ℕ → Set₁ where
  
  here  : (a : A) {E : (b : B a) (z : C a b) → Telescope i}
        → TelAt' A B C (b ∈ B a , c ∈ C a b , E b c) 0

  there : {S : Set} {E : (s : S) → Telescope (suc (suc i))} {k : ℕ} 
        → ((s : S) → TelAt' A B C (E s) k)
        → TelAt' A B C (s ∈ S , E s) (suc k)

syntax TelAt' A B C Δ k = Δ [ k ]∶Σ[ A ] B ∶ C

-- example at location 1 there is an element of the Fin type 
_ : (x ∈ ℕ , y ∈ Fin x , e ∈ y ≡ y , nil) [ 1 ]∶Σ[ ℕ ] (λ x → Fin x) ∶ (λ x y → y ≡ y)
_ = there (λ x → here x)


-- lookup function that takes a proof p that there is an element of type B at location k 
-- and returns that element from an instantiation of that telescope
lookup
  : {Δ  : Telescope n} {A : Set} {B : A → Set}
    (p  : Δ [ k ]∶Σ[ A ] B)
    (ts : ⟦ Δ ⟧telD)
  → Σ[ x ∈ A ] B x
lookup (here  x) (s , _ ) = x , s
lookup (there p) (s , ts) = lookup (p s) ts

syntax lookup p ts = ts Σ[ p ]

-- example
_ : lookup {Δ = x ∈ ℕ , y ∈ ⊤ , z ∈ Fin x , nil} {A = ℕ} {B = Fin}
      (there (λ x → there (λ y → here x))) -- proof that we have Fin at position 2
      (2 , tt , fzero , tt)
  ≡ (2 , fzero)
_ = refl


-- keep a k-prefix of a telescope
keepTel : (k : Fin n) (Δ : Telescope n)
        → Telescope (toℕ k)
keepTel fzero    _          = nil
keepTel (fsuc k) (cons S T) = s ∈ S , keepTel k (T s)

-- drop a k-prefix of a telescope, given k values
dropTel : (k : Fin n) (Δ : Telescope n)
        → (⟦ keepTel k Δ ⟧telD → Telescope (n ∸ toℕ k))
dropTel fzero    Δ          _        = Δ
dropTel (fsuc k) (cons _ E) (s , ts) = dropTel k (E s) ts

-- splits the telescope at position k
splitTel
  : (k : Fin n) (Δ : Telescope n)
  → Σ[ Δ ∈ Telescope (toℕ k) ] (⟦ Δ ⟧telD → Telescope (n ∸ toℕ k))
splitTel k Δ = keepTel k Δ , dropTel k Δ


-- merge two telescopes X and Y
-- assuming that from an instanciation of X (e.g ⟦ X ⟧telD),
-- we can extract the values telescope Y depends on (e.g S)
mergeTel
  : (X : Telescope n) {S : Set} (Y : S → Telescope m)
  → (⟦ X ⟧telD → S)
  → Telescope (n + m)
mergeTel nil        Y f = Y (f tt)
mergeTel (cons S T) Y f = s ∈ S , mergeTel (T s) Y (λ t → f (s , t))

-- merge two instances of telescope X and Y
merge
  : {X : Telescope n} {S : Set} {Y : S → Telescope m}
    {f : ⟦ X ⟧telD → S}
    (x : ⟦ X ⟧telD)
  → ⟦ Y (f x) ⟧telD
  → ⟦ mergeTel X Y f ⟧telD
merge {X = nil     } x       t = t
merge {X = cons S T} (s , x) t = s , merge x t

-- project out the first half of a merge
mproj₁
  : {X : Telescope n} {S : Set} {Y : S → Telescope m}
    {f : ⟦ X ⟧telD → S}
  → ⟦ mergeTel X Y f ⟧telD
  → ⟦ X ⟧telD
mproj₁ {X = nil}      t       = tt
mproj₁ {X = cons S T} (s , t) = s , mproj₁ t

-- project out the second half of a merge
mproj₂
  : {X : Telescope n} {S : Set} {Y : S → Telescope m}
    {f : ⟦ X ⟧telD → S}
  → (t : ⟦ mergeTel X Y f ⟧telD)
  → ⟦ Y (f (mproj₁ t)) ⟧telD
mproj₂ {X = nil}      t       = t
mproj₂ {X = cons S T} (s , t) = mproj₂ {X = T s} t

-- section-retraction pair of mrpoj and merge
mproj∘merge
  : {X : Telescope n} {S : Set} {Y : S → Telescope m}
    {f : ⟦ X ⟧telD → S}
    (x : ⟦ X ⟧telD)
    (y : ⟦ Y (f x) ⟧telD)
  → (_,_ {B = λ xs → ⟦ Y (f xs) ⟧telD} x y) ≡ 
      (mproj₁ {Y = Y} {f = f} (merge x y) , mproj₂ {X = X} {Y = Y} {f = f} (merge x y))
mproj∘merge {X = nil}      tt      y = refl
mproj∘merge {X = cons S T} {Y = Y} (s , x) y = cong (λ x₁ → (s , (proj₁ x₁)) , (proj₂ x₁)) (mproj∘merge x y)  
  




-- replace a cell at position k in telescope X with a telescope Y
-- provided that cell k in X has type B, and telescope Y can produce a value of such type.
expandTel
  : (T : Telescope n){A : Set}{B : A → Set} (Δ : A → Telescope m) 
    (f : (a : A) → ⟦ Δ a ⟧telD → B a)
  → T [ k ]∶Σ[ A ] B
  → Telescope (k + (m + (n ∸ suc k)))
expandTel (cons A T) Δ f (here a)  = mergeTel (Δ a) T (f a)
expandTel (cons A T) Δ f (there k) = x ∈ A , expandTel (T x) Δ f (k x)

expand
  : {n m k : ℕ}{T   : Telescope n}{A : Set}{B : A → Set}{Δ : A → Telescope m}
    {f  : (a : A) → ⟦ Δ a ⟧telD → B a}
    (s  : T [ k ]∶Σ[ A ] B)
    {a  : A}
    {x  : B a}
    (d' : ⟦ Δ a ⟧telD)
    (fd : f a d' ≡ x)
    (t  : ⟦ T ⟧telD)
  → t Σ[ s ] ≡ (a , x)
  → ⟦ expandTel T Δ f s ⟧telD
expand {n = suc i} {T  = cons S T} {A} {B} {Δ} {f} (here a₂) {a₁} {b₁} a fd (b₂ , t) p 
  = J (λ a₂b₂ p → {f : (a : A) → ⟦ Δ a ⟧telD → B a} (a : ⟦ Δ a₁ ⟧telD) (fd : f a₁ a ≡ b₁) {T : B (proj₁ a₂b₂) → Telescope i} (t : ⟦ T (snd a₂b₂) ⟧telD) → ⟦ mergeTel (Δ (proj₁ a₂b₂)) T (f (proj₁ a₂b₂)) ⟧telD) 
      (λ {f} a → J (λ b₁ fd → {T : B a₁ → Telescope i} → ⟦ T b₁ ⟧telD → ⟦ mergeTel (Δ a₁) T (f a₁) ⟧telD) 
        (λ t → merge a t)) (sym p) a fd t
expand (there k) d fd (s , t) p = s , expand (k s) d fd t p 

expandSort
  : ∀{ℓ}{n m k : ℕ}{T : Telescope n}{A : Set}{B : A → Set}{Δ : A → Telescope m}
    {f : (a : A) → ⟦ Δ a ⟧telD → B a}
    (p : T [ k ]∶Σ[ A ] B)
  → (⟦ T ⟧telD → Set ℓ)
  → (⟦ expandTel T Δ f p ⟧telD → Set ℓ)
expandSort {T  = cons S T} {Δ = Δ} {f = f} (here a) X t
  = X ((f a (mproj₁ t)) , mproj₂ {X = Δ a} {Y = T} t) 
expandSort (there k) X (s , t) = expandSort (k s) (λ x → X (s , x)) t

shrinkExpand
  : ∀{ℓ}{n m k : ℕ} {T : Telescope n}{A : Set}{B : A → Set}{Δ : A → Telescope m}
    {f : (a : A) → ⟦ Δ a ⟧telD → B a}
    (p : T [ k ]∶Σ[ A ] B)
    {a : A}
    {x   : B a}
    (d'   : ⟦ Δ a ⟧telD)
    (fd  : f a d' ≡ x)
    (X : ⟦ T ⟧telD → Set ℓ)
    (t : ⟦ T ⟧telD)
    (e : t Σ[ p ] ≡ (a , x))
  → expandSort p X (expand {f = f} p d' fd t e)
  → X t
shrinkExpand {ℓ} {n = suc i} {T  = cons S T} {A} {B} {Δ} {f} (here a₂) {a₁} {b₁} a fd X (b₂ , t) p e
  = J (λ a₂b₂ p → {f : (a : A) → ⟦ Δ a ⟧telD → B a} (a : ⟦ Δ a₁ ⟧telD) (fd : f a₁ a ≡ b₁) {T : B (proj₁ a₂b₂) → Telescope i} (t : ⟦ T (snd a₂b₂) ⟧telD) 
      (X : Σ-syntax (B (proj₁ a₂b₂)) (λ s → ⟦ T s ⟧telD) → Set ℓ) → expandSort {f = f} (here (proj₁ a₂b₂)) X (expand {f = f} (here (proj₁ a₂b₂)) a fd (proj₂ a₂b₂ , t) (sym p)) → X (proj₂ a₂b₂ , t))
    (λ {f} a → J (λ b₁ fd → {T : B a₁ → Telescope i} → (t : ⟦ T b₁ ⟧telD) → (X : Σ-syntax (B a₁) (λ s → ⟦ T s ⟧telD) → Set ℓ) → expandSort {f = f} (here a₁) X (expand {f = f} (here a₁) a fd (b₁ , t) (sym refl)) → X (b₁ , t)) 
        (λ t X e → subst (λ x → X (f a₁ (proj₁ x) , (proj₂ x))) (sym (mproj∘merge a t)) e))
    (sym p) a fd t X (subst (λ e → expandSort {f = f} (here a₂) X (expand {f = f} (here a₂) a fd (b₂ , t) e)) (J (λ _ p → p ≡ sym (sym p)) refl p) e) 
    
shrinkExpand (there p) d fd X (s , dt) e t = shrinkExpand (p s) d fd (λ x → X (s , x)) dt e t


-- replace the element at position k with x
replaceTel
  : {X : Set} (x : X) (Δ : Telescope (suc n)) (p : Δ [ k ]∶Σ[ ⊤ ] (λ _ → X))
    → Telescope n
replaceTel x (cons S E) (here tt) = E x
replaceTel x (cons S E) (there p) = cons S (λ s → replaceTel x (E s) (p s))

replace 
  : {X : Set}  {Δ : Telescope (suc n)} (p : Δ [ k ]∶Σ[ ⊤ ] (λ _ → X))
    → (xs : ⟦ Δ ⟧telD)
    → ⟦ replaceTel (proj₂ (xs Σ[ p ])) Δ p ⟧telD
replace (here tt) (s , xs) = xs
replace (there p) (s , xs) = s , replace (p s) xs

replace' 
  : {X : Set}  {Δ : Telescope (suc n)} (x : X) (p : Δ [ k ]∶Σ[ ⊤ ] (λ _ → X))
    → (xs : ⟦ replaceTel x Δ p ⟧telD)
    → ⟦ Δ ⟧telD
replace' x (here tt) xs = x , xs
replace' x (there p) (s , xs) = s , replace' x (p s) xs

replace'∘replace 
  : {X : Set}  {Δ : Telescope (suc n)} (p : Δ [ k ]∶Σ[ ⊤ ] (λ _ → X))
    → (xs : ⟦ Δ ⟧telD)
    → replace' (proj₂ (xs Σ[ p ])) p (replace p xs) ≡ xs
replace'∘replace  (here tt) (s , xs) = refl
replace'∘replace  (there p) (s , xs) = subst (λ xs' → (s , xs') ≡ (s , xs)) (sym (replace'∘replace  (p s) xs)) refl


-- move X back in the telescope to position goal
moveBackTel
  : (Δ : Telescope n) {X : Set} (p : Δ [ k ]∶Σ[ ⊤ ] (λ _ → X))
    → (goal : Fin k)
    → Telescope n 
moveBackTel (cons S E) {X} p fzero = cons X (λ x → replaceTel x (cons S E) p)
moveBackTel (cons S E) (there p) (fsuc goal) = cons S λ s → moveBackTel (E s) (p s) goal 

moveBack
  : {Δ : Telescope n} {X : Set} (p : Δ [ k ]∶Σ[ ⊤ ] (λ _ → X))
    → (goal : Fin k)
    → (xs : ⟦ Δ ⟧telD)
    → ⟦ moveBackTel Δ p goal ⟧telD
moveBack {Δ = cons S E} p fzero (s , xs) = proj₂ ((s , xs) Σ[ p ]) , replace p (s , xs) 
moveBack (there p) (fsuc goal) (s , xs) = s , moveBack (p s) goal xs 

moveBack'
  : {Δ : Telescope n} {X : Set} (p : Δ [ k ]∶Σ[ ⊤ ] (λ _ → X))
    → (goal : Fin k)
    → (xs : ⟦ moveBackTel Δ p goal ⟧telD)
    → ⟦ Δ ⟧telD
moveBack' {Δ = cons S E} p fzero (s , xs) = replace' s p xs
moveBack' (there p) (fsuc goal) (s , xs) = s , moveBack' (p s) goal xs 

moveBack'∘moveBack
  : {Δ : Telescope n} {X : Set} (p : Δ [ k ]∶Σ[ ⊤ ] (λ _ → X))
    → (goal : Fin k)
    → (xs : ⟦ Δ ⟧telD)
    → moveBack' p goal (moveBack p goal xs) ≡ xs
moveBack'∘moveBack {Δ = cons S E} p fzero xs = replace'∘replace  p xs
moveBack'∘moveBack (there p) (fsuc goal) (s , xs) = subst (λ xs' → (s , xs') ≡ (s , xs)) (sym (moveBack'∘moveBack (p s) goal xs)) refl


-- move back the element at k to the position goal after split that is not dependent 
-- on elements before the split
reorderTel : (split : Fin n) (Δ : Telescope n) (goal : Fin k)
  → (p : (x : ⟦ proj₁ (splitTel split Δ) ⟧telD) → (Σ[ X ∈ Set ] ((proj₂ (splitTel split Δ)) x) [ k ]∶Σ[ ⊤ ] (λ _ → X)))
  → Telescope n
reorderTel fzero (cons S E) goal p = moveBackTel (cons S E) (proj₂ (p tt)) goal
reorderTel (fsuc split) (cons S E) goal p = cons S (λ s → reorderTel split (E s) goal (λ x → p (s , x)))

reorder : (split : Fin n) {Δ : Telescope n} (goal : Fin k)
  → (p : (x : ⟦ proj₁ (splitTel split Δ) ⟧telD) → (Σ[ X ∈ Set ] ((proj₂ (splitTel split Δ)) x) [ k ]∶Σ[ ⊤ ] (λ _ → X)))
  → (xs : ⟦ Δ ⟧telD)
  → ⟦ reorderTel split Δ goal p ⟧telD
reorder fzero {cons S E} goal p xs = moveBack (proj₂ (p tt)) goal xs
reorder (fsuc split) {Δ = cons S E} goal p (s , xs) = s , reorder split goal (λ x → p (s , x)) xs 

reorder' : (split : Fin n) {Δ : Telescope n} (goal : Fin k)
  → (p : (x : ⟦ proj₁ (splitTel split Δ) ⟧telD) → (Σ[ X ∈ Set ] ((proj₂ (splitTel split Δ)) x) [ k ]∶Σ[ ⊤ ] (λ _ → X)))
  → (xs : ⟦ reorderTel split Δ goal p ⟧telD)
  → ⟦ Δ ⟧telD
reorder' fzero {Δ = cons S E} goal p xs = moveBack' (proj₂ (p tt)) goal xs
reorder' (fsuc split) {Δ = cons S E} goal p (s , xs) = s , reorder' split goal (λ x → p (s , x)) xs 

reorder'∘reorder : (split : Fin n) {Δ : Telescope n} (goal : Fin k)
  → (p : (x : ⟦ proj₁ (splitTel split Δ) ⟧telD) → (Σ[ X ∈ Set ] ((proj₂ (splitTel split Δ)) x) [ k ]∶Σ[ ⊤ ] (λ _ → X)))
  → (xs : ⟦ Δ ⟧telD)
  → reorder' split goal p (reorder split goal p xs) ≡ xs
reorder'∘reorder fzero {Δ = cons S E} goal p xs = moveBack'∘moveBack (proj₂ (p tt)) goal xs
reorder'∘reorder (fsuc split) {Δ = cons S E} goal p (s , xs) = subst (λ xs' → (s , xs') ≡ (s , xs)) (sym (reorder'∘reorder split goal (λ x → p (s , x)) xs)) refl



-- replace type Y₁ in the telescope if it is equivalent to a type Y₂
replaceInTel : {X : Set} (Y₁ Y₂ : X → Set) (Δ : Telescope n) (p : Δ [ k ]∶Σ[ X ] Y₁)
  → (f : (x : X) → Y₁ x ≡ Y₂ x)
  → Telescope n
replaceInTel Y₁ Y₂ (cons S E) (here x) f = cons (Y₂ x) (λ y₂ → E ((subst id (sym (f x)) y₂)))
replaceInTel Y₁ Y₂ (cons S E) (there p) f = cons S (λ s → replaceInTel Y₁ Y₂ (E s) (p s) f)

replaceIn 
  : {X : Set} {Y₁ Y₂ : X → Set} {Δ : Telescope n} (p : Δ [ k ]∶Σ[ X ] Y₁)
  → (f : (x : X) → Y₁ x ≡ Y₂ x)
    → (xs : ⟦ Δ ⟧telD)
    → ⟦ replaceInTel Y₁ Y₂ Δ p f ⟧telD
replaceIn {Δ = cons S Δ} (here x) f (s , xs) = subst id (f x) s , J (λ _ e → ⟦ Δ (subst id (sym e) (subst id e s)) ⟧telD) xs (f x)
replaceIn (there p) f (s , xs) = s , replaceIn (p s) f xs

replaceIn' 
  : {X : Set} {Y₁ Y₂ : X → Set} {Δ : Telescope n} (p : Δ [ k ]∶Σ[ X ] Y₁)
  → (f : (x : X) → Y₁ x ≡ Y₂ x)
  → (xs : ⟦ replaceInTel Y₁ Y₂ Δ p f ⟧telD)
  → ⟦ Δ ⟧telD
replaceIn' {Δ = cons S Δ} (here x) f (s , xs) = subst id (sym (f x)) s , xs
replaceIn' (there p) f (s , xs) = s , replaceIn' (p s) f xs

replaceIn'∘replaceIn
  : {X : Set} {Y₁ Y₂ : X → Set} {Δ : Telescope n} (p : Δ [ k ]∶Σ[ X ] Y₁)
  → (f : (x : X) → Y₁ x ≡ Y₂ x)
  → (xs : ⟦ Δ ⟧telD)
  → replaceIn' p f (replaceIn p f xs) ≡ xs
replaceIn'∘replaceIn {Δ = cons S Δ} (here x) f (s , xs) = J (λ _ e₁ → 
  (subst id (sym e₁) (subst id e₁ s) , J (λ z e → ⟦ Δ (subst id (sym e) (subst id e s)) ⟧telD) xs e₁) 
    ≡ (s , xs)) refl (f x)
replaceIn'∘replaceIn (there p) f (s , xs) = subst (λ xs' → (s , xs') ≡ (s , xs)) (sym (replaceIn'∘replaceIn (p s) f xs)) refl


-- split (a₁ , b₁) ≡ (a₂ , b₂) at location k into 
-- (e : a₁ ≡ a₂)(subst B e b₁ ≡ b₂)
splitΣTel 
  : {Δ : Telescope n}{A : Set} 
  → {B : A → Set} {C : (a : A) → B a → Set}
  → (AB₁ : (a : A) → Σ (B a) (C a)) → (AB₂ : (a : A) → Σ (B a) (C a))
  → Δ [ k ]∶Σ[ A ] (λ a → AB₁ a ≡ AB₂ a)
  → Telescope (suc n)
splitΣTel {Δ  = cons S T} {B = B} {C} AB₁ AB₂ (here a)  = ea ∈ proj₁ (AB₁ a) ≡ proj₁ (AB₂ a) 
  , eb ∈ subst (C a) ea (proj₂ (AB₁ a)) ≡ proj₂ (AB₂ a) , T (Σ-create ea eb)
splitΣTel {Δ  = cons S T} A B (there k) = x ∈ S , splitΣTel A B (k x)

splitΣ 
  : {Δ : Telescope n}{A : Set} 
  → {B : A → Set} {C : (a : A) → B a → Set}
  → (AB₁ : (a : A) → Σ (B a) (C a)) → (AB₂ : (a : A) → Σ (B a) (C a))
  → (p : Δ [ k ]∶Σ[ A ] (λ a → AB₁ a ≡ AB₂ a))
  → (xs : ⟦ Δ ⟧telD)
  → ⟦ splitΣTel AB₁ AB₂ p ⟧telD
splitΣ {Δ  = cons S T} A B (here a) (ab , xs) = linvΣ₁ ab , linvΣ₂ ab , subst (λ e → ⟦ T e ⟧telD) (sym (isLinvΣ ab)) xs
splitΣ A B (there k) (x , xs) = x , splitΣ A B (k x) xs

splitΣ' 
  : {Δ : Telescope n}{A : Set} 
  → {B : A → Set} {C : (a : A) → B a → Set}
  → (AB₁ : (a : A) → Σ (B a) (C a)) → (AB₂ : (a : A) → Σ (B a) (C a))
  → (p : Δ [ k ]∶Σ[ A ] (λ a → AB₁ a ≡ AB₂ a))
  → ⟦ splitΣTel AB₁ AB₂ p ⟧telD
  → ⟦ Δ ⟧telD
splitΣ' A B (here a) (b , c , xs) = Σ-create b c , xs
splitΣ' A B (there k) (x , xs) = x , splitΣ' A B (k x) xs

splitΣ'∘splitΣ
  : {Δ : Telescope n}{A : Set} 
  → {B : A → Set} {C : (a : A) → B a → Set}
  → (AB₁ : (a : A) → Σ (B a) (C a)) → (AB₂ : (a : A) → Σ (B a) (C a))
  → (p : Δ [ k ]∶Σ[ A ] (λ a → AB₁ a ≡ AB₂ a))
  → (xs : ⟦ Δ ⟧telD)
  → splitΣ' AB₁ AB₂ p (splitΣ AB₁ AB₂ p xs) ≡ xs
splitΣ'∘splitΣ {Δ  = cons S T} A B (here a) (ab , xs) 
  = Σ-create (isLinvΣ ab) (J (λ ab e₁ → (xs : ⟦ T ab ⟧telD) → subst (λ s → ⟦ T s ⟧telD) e₁
    (subst (λ e → ⟦ T e ⟧telD) (sym e₁) xs) ≡ xs) (λ _ → refl) (isLinvΣ ab) xs) 
splitΣ'∘splitΣ A B (there k) (x , xs) = cong (x ,_) (splitΣ'∘splitΣ A B (k x) xs)

-- combine (a₁ ≡ a₂) at location k to ((a₁ , tt) ≡ (a₂ , tt))
combineΣTel 
  : {Δ : Telescope n}{A : Set} 
  → {B : A → Set} 
  → (A₁ : (a : A) → B a) → (A₂ : (a : A) → B a)
  → Δ [ k ]∶Σ[ A ] (λ a → A₁ a ≡ A₂ a)
  → Telescope n
combineΣTel {Δ  = cons S T} A₁ A₂ (here a)  = ea ∈ (A₁ a , tt) ≡ (A₂ a , tt) 
  , T (cong proj₁ ea)
combineΣTel {Δ  = cons S T} A B (there k) = x ∈ S , combineΣTel A B (k x)

combineΣ 
  : {Δ : Telescope n}{A : Set} 
  → {B : A → Set} 
  → (A₁ : (a : A) → B a) → (A₂ : (a : A) → B a)
  → (p : Δ [ k ]∶Σ[ A ] (λ a → A₁ a ≡ A₂ a))
  → (xs : ⟦ Δ ⟧telD)
  → ⟦ combineΣTel A₁ A₂ p ⟧telD
combineΣ {n = suc i} {Δ  = cons S T} A B (here a) (b , xs) = cong (_, tt) b , 
  J (λ c d → (T : A a ≡ c → Telescope i) → ⟦ T d ⟧telD → ⟦ T (cong (λ r → proj₁ r) (cong (_, tt) d)) ⟧telD) (λ T₁ x → x) b T xs
combineΣ A B (there k) (x , xs) = x , combineΣ A B (k x) xs

combineΣ' 
  : {Δ : Telescope n}{A : Set} 
  → {B : A → Set} 
  → (A₁ : (a : A) → B a) → (A₂ : (a : A) → B a)
  → (p : Δ [ k ]∶Σ[ A ] (λ a → A₁ a ≡ A₂ a))
  → ⟦ combineΣTel A₁ A₂ p ⟧telD
  → ⟦ Δ ⟧telD
combineΣ' A B (here a) (b , xs) = cong proj₁ b , xs
combineΣ' A B (there k) (x , xs) = x , combineΣ' A B (k x) xs

combineΣ'∘combineΣ 
  : {Δ : Telescope n}{A : Set} 
  → {B : A → Set} 
  → (A₁ : (a : A) → B a) → (A₂ : (a : A) → B a)
  → (p : Δ [ k ]∶Σ[ A ] (λ a → A₁ a ≡ A₂ a))
  → (xs : ⟦ Δ ⟧telD)
  → combineΣ' A₁ A₂ p (combineΣ  A₁ A₂ p xs) ≡ xs
combineΣ'∘combineΣ {n = suc i} {Δ  = cons S T} A B (here a) (b , xs) 
  = J (λ b₁ c → (T : A a ≡ b₁ → Telescope i) → (xs : ⟦ T c ⟧telD) → (cong (λ r → proj₁ r) (cong (_, tt) c) , 
    J (λ b c₁ → (T₁ : A a ≡ b → Telescope i) → ⟦ T₁ c₁ ⟧telD → ⟦ T₁ (cong (λ r → proj₁ r) (cong (_, tt) c₁)) ⟧telD) (λ T₁ x → x) c T xs)
      ≡ (c , xs)) (λ T₁ xs₁ → refl) b T xs 
combineΣ'∘combineΣ A B (there k) (x , xs) = cong (x ,_) (combineΣ'∘combineΣ A B (k x) xs)


updateTel₁ : {i i' j : ℕ} {Δ : Telescope i} {X : Set}{A : X → Set}
    → (p : Δ [ j ]∶Σ[ X ] (λ x → A x)) 
    → (fTel : Telescope i')
    → (f : (x : X) → A x → ⟦ fTel ⟧telD)
    → (f' : (x : X) → ⟦ fTel ⟧telD → A x)
    → (f'∘f : (x : X) → (e : A x) → f' x (f x e) ≡ e)
    → Telescope (i + i' ∸ 1)
updateTel₁ {i = suc i} {i' = i'} {Δ = cons S E} (here x) fTel f f' f'∘f 
  = subst Telescope (+-comm i' i) (mergeTel fTel E (f' x)) 
updateTel₁ {Δ = cons S E} (there p) fTel f f' f'∘f = cons S (λ s → updateTel₁ (p s) fTel f f' f'∘f) 

update₁ : {i i' j : ℕ} {Δ : Telescope i} {X : Set}{A : X → Set}
    → (p : Δ [ j ]∶Σ[ X ] (λ x → A x)) 
    → (fTel : Telescope i')
    → (f : (x : X) → A x → ⟦ fTel ⟧telD)
    → (f' : (x : X) → ⟦ fTel ⟧telD → A x)
    → (f'∘f : (x : X) → (e : A x) → f' x (f x e) ≡ e)
    → ⟦ Δ ⟧telD
    → ⟦ updateTel₁ p fTel f f' f'∘f ⟧telD
update₁ {i = suc i} {i' = i'} {Δ = cons S E} (here x) fTel f f' f'∘f (a , xs)
  =  J (λ _ e → ⟦ subst Telescope e (mergeTel fTel E (f' x)) ⟧telD) 
    (merge (f x a) (subst (λ e → ⟦ E e ⟧telD) (sym (f'∘f x a)) xs))
    (+-comm i' i)
update₁ {Δ = cons S E} (there p) fTel f f' f'∘f (x , xs) = x , update₁ (p x) fTel f f' f'∘f xs

update₁' : {i i' j : ℕ} {Δ : Telescope i} {X : Set}{A : X → Set}
    → (p : Δ [ j ]∶Σ[ X ] (λ x → A x)) 
    → (fTel : Telescope i')
    → (f : (x : X) → A x → ⟦ fTel ⟧telD)
    → (f' : (x : X) → ⟦ fTel ⟧telD → A x)
    → (f'∘f : (x : X) → (e : A x) → f' x (f x e) ≡ e)
    → ⟦ updateTel₁ p fTel f f' f'∘f ⟧telD
    → ⟦ Δ ⟧telD
update₁' {i = suc i} {i' = i'} {Δ = cons S E} (here x) fTel f f' f'∘f xs 
  = f' x (mproj₁ (J' (λ _ e → ⟦ subst Telescope e (mergeTel fTel E (f' x)) ⟧telD) (+-comm i' i) xs)) , 
    mproj₂ {X = fTel} {Y = E} (J' (λ _ e → ⟦ subst Telescope e (mergeTel fTel E (f' x)) ⟧telD) (+-comm i' i) xs) 
update₁' {Δ = cons S E} (there p) fTel f f' f'∘f (x , xs) = x , update₁' (p x) fTel f f' f'∘f xs

update₁'∘update₁ : {i i' j : ℕ} {Δ : Telescope i} {X : Set}{A : X → Set}
    → (p : Δ [ j ]∶Σ[ X ] (λ x → A x)) 
    → (fTel : Telescope i')
    → (f : (x : X) → A x → ⟦ fTel ⟧telD)
    → (f' : (x : X) → ⟦ fTel ⟧telD → A x)
    → (f'∘f : (x : X) → (e : A x) → f' x (f x e) ≡ e)
    → (xs : ⟦ Δ ⟧telD)
    → update₁' p fTel f f' f'∘f (update₁ p fTel f f' f'∘f xs) ≡ xs 
update₁'∘update₁ {i = suc i} {i' = i'} {Δ = cons S E} (here x) fTel f f' f'∘f (a , xs) 
  = subst (λ e₁ → (f' x (mproj₁ e₁) , mproj₂ {X = fTel} {Y = E} e₁) ≡ (a , xs))
      (sym (J'∘J (λ z e → ⟦ subst Telescope e (mergeTel fTel E (f' x)) ⟧telD) (merge (f x a) (subst (λ e → ⟦ E e ⟧telD) (sym (f'∘f x a)) xs)) (+-comm i' i))) 
      (subst (λ axs → (f' x (proj₁ axs) , snd axs) ≡ (a , xs)) (mproj∘merge (f x a) (subst (λ e → ⟦ E e ⟧telD) (sym (f'∘f x a)) xs)) 
        (J (λ x₁ e₁ → (x₁ , subst (λ e → ⟦ E e ⟧telD) e₁ xs) ≡ (a , xs)) refl (sym (f'∘f x a)))) 
update₁'∘update₁ {Δ = cons S E} (there p) fTel f f' f'∘f (x , xs) 
  = subst (λ e → (x , e) ≡ (x , xs)) (sym (update₁'∘update₁ (p x) fTel f f' f'∘f xs)) refl

updateTel₂ : {i i' j : ℕ} {Δ : Telescope i} {X : Set}{A : X → Set}{B : (x : X)(a : A x) → Set}
    → (p : Δ [ j ]∶Σ[ X ] (λ x → A x) ∶ (λ x a → B x a)) 
    → (fTel : Telescope i')
    → (f : (x : X) → Σ[ a ∈ A x ] (B x a) → ⟦ fTel ⟧telD)
    → (f' : (x : X) → ⟦ fTel ⟧telD → Σ[ a ∈ A x ] (B x a))
    → (f'∘f : (x : X) → (e : Σ[ a ∈ A x ] (B x a)) → f' x (f x e) ≡ e)
    → Telescope (i + i' ∸ 2)
updateTel₂ {i = suc (suc i)} {i' = i'} {Δ = cons S _} (here x {E = E}) fTel f f' f'∘f 
  = subst Telescope (+-comm i' i) (mergeTel fTel (λ ab → E (proj₁ ab) (proj₂ ab)) (f' x)) 
updateTel₂ {Δ = cons S E} (there p) fTel f f' f'∘f = cons S (λ s → updateTel₂ (p s) fTel f f' f'∘f) 

update₂ : {i i' j : ℕ} {Δ : Telescope i} {X : Set}{A : X → Set}{B : (x : X)(a : A x) → Set}
    → (p : Δ [ j ]∶Σ[ X ] (λ x → A x) ∶ (λ x a → B x a)) 
    → (fTel : Telescope i')
    → (f : (x : X) → Σ[ a ∈ A x ] (B x a) → ⟦ fTel ⟧telD)
    → (f' : (x : X) → ⟦ fTel ⟧telD → Σ[ a ∈ A x ] (B x a))
    → (f'∘f : (x : X) → (e : Σ[ a ∈ A x ] (B x a)) → f' x (f x e) ≡ e)
    → ⟦ Δ ⟧telD
    → ⟦ updateTel₂ p fTel f f' f'∘f ⟧telD
update₂ {i = suc (suc i)} {i' = i'} {Δ = cons S E} (here x {E = Δ}) fTel f f' f'∘f (a , b , xs)
  = J (λ _ e → ⟦ subst Telescope e (mergeTel fTel (λ ab → Δ (proj₁ ab) (snd ab)) (f' x)) ⟧telD) 
    (merge (f x (a , b)) (subst (λ e → ⟦ Δ (proj₁ e) (proj₂ e) ⟧telD) (subst (λ e₁ → (a , b) ≡ (proj₁ e₁ , snd e₁)) (sym (f'∘f x (a , b))) refl) xs))
    (+-comm i' i) 
update₂ {Δ = cons S E} (there p) fTel f f' f'∘f (x , xs) = x , update₂ (p x) fTel f f' f'∘f xs

update₂' : {i i' j : ℕ} {Δ : Telescope i} {X : Set}{A : X → Set}{B : (x : X)(a : A x) → Set}
    → (p : Δ [ j ]∶Σ[ X ] (λ x → A x) ∶ (λ x a → B x a)) 
    → (fTel : Telescope i')
    → (f : (x : X) → Σ[ a ∈ A x ] (B x a) → ⟦ fTel ⟧telD)
    → (f' : (x : X) → ⟦ fTel ⟧telD → Σ[ a ∈ A x ] (B x a))
    → (f'∘f : (x : X) → (e : Σ[ a ∈ A x ] (B x a)) → f' x (f x e) ≡ e)
    → ⟦ updateTel₂ p fTel f f' f'∘f ⟧telD
    → ⟦ Δ ⟧telD
update₂' {i = suc (suc i)} {i' = i'} {Δ = cons S E} (here x {E = Δ}) fTel f f' f'∘f xs 
  = proj₁ (f' x (mproj₁ mTel)) , proj₂ (f' x (mproj₁ mTel)) , 
    mproj₂ {X = fTel} {Y = λ ab → Δ (proj₁ ab) (snd ab)} mTel where

  mTel : ⟦ mergeTel fTel (λ ab → Δ (proj₁ ab) (snd ab)) (f' x) ⟧telD
  mTel = J' (λ _ e → ⟦ subst Telescope e (mergeTel fTel (λ ab → Δ (proj₁ ab) (snd ab)) (f' x)) ⟧telD) (+-comm i' i) xs 

update₂' {Δ = cons S E} (there p) fTel f f' f'∘f (x , xs) = x , update₂' (p x) fTel f f' f'∘f xs

update₂'∘update₂ : {i i' j : ℕ} {Δ : Telescope i} {X : Set}{A : X → Set}{B : (x : X)(a : A x) → Set}
    → (p : Δ [ j ]∶Σ[ X ] (λ x → A x) ∶ (λ x a → B x a)) 
    → (fTel : Telescope i')
    → (f : (x : X) → Σ[ a ∈ A x ] (B x a) → ⟦ fTel ⟧telD)
    → (f' : (x : X) → ⟦ fTel ⟧telD → Σ[ a ∈ A x ] (B x a))
    → (f'∘f : (x : X) → (e : Σ[ a ∈ A x ] (B x a)) → f' x (f x e) ≡ e)
    → (xs : ⟦ Δ ⟧telD)
    → update₂' p fTel f f' f'∘f (update₂ p fTel f f' f'∘f xs) ≡ xs 
update₂'∘update₂ {i = suc (suc i)} {i' = i'} {Δ = cons S E} (here x {E = Δ}) fTel f f' f'∘f (a , b , xs) 
  = subst (λ e₁ → (proj₁ (f' x (mproj₁ e₁)) , proj₂ (f' x (mproj₁ e₁)) , mproj₂ {X = fTel} {Y = λ ab → Δ (proj₁ ab) (snd ab)} e₁) ≡ (a , b , xs)) 
      (sym (J'∘J (λ z e → ⟦ subst Telescope e (mergeTel fTel (λ ab → Δ (proj₁ ab) (snd ab)) (f' x)) ⟧telD) 
        (merge (f x (a , b)) (subst (λ e → ⟦ Δ (proj₁ e) (proj₂ e) ⟧telD) (subst (λ e₁ → (a , b) ≡ (proj₁ e₁ , snd e₁)) (sym (f'∘f x (a , b))) refl) xs)) 
        (+-comm i' i)))
      (subst (λ axs → (proj₁ (f' x (proj₁ axs)) , snd (f' x (proj₁ axs)) , proj₂ axs) ≡ (a , b , xs)) 
        (mproj∘merge (f x (a , b)) (subst (λ e → ⟦ Δ (proj₁ e) (snd e) ⟧telD)
            (subst (λ e₁ → (a , b) ≡ (proj₁ e₁ , snd e₁))
              (sym (f'∘f x (a , b))) refl) xs)) 
        (J (λ x₁ e₁ → (proj₁ x₁ , snd x₁ , subst (λ e → ⟦ Δ (proj₁ e) (proj₂ e) ⟧telD) (subst (λ e₁ → (a , b) ≡ (proj₁ e₁ , snd e₁)) e₁ refl) xs) ≡ (a , b , xs)) 
          refl (sym (f'∘f x (a , b)))))
          
update₂'∘update₂ {Δ = cons S E} (there p) fTel f f' f'∘f (x , xs) 
  = subst (λ e → (x , e) ≡ (x , xs)) (sym (update₂'∘update₂ (p x) fTel f f' f'∘f xs)) refl  