{-# OPTIONS --allow-unsolved-metas #-}
module Non_Indexed.telescope where 

open import Non_Indexed.datatypes

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Unit.Base
open import Data.Empty
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_)
open import Data.Nat.Properties using (+-comm)
open import Data.Fin using (Fin; fromℕ; toℕ; _-_) renaming (zero to fzero; suc to fsuc)


data Telescope : (i : ℕ) → Set₁ where 
    nil : Telescope zero
    cons : {i : ℕ} → (S : Set) → (E : (s : S) → Telescope i) → Telescope (suc i)

syntax cons S (λ s → T) = s ∈ S , T

⟦_⟧telD : {i : ℕ} (Δ : Telescope i) → Set
⟦_⟧telD {zero} nil = ⊤
⟦_⟧telD {suc i} (cons S T) = Σ[ s ∈ S ] (⟦ T s ⟧telD)

data _[_]∶Σ[_]_ : {n : ℕ} → (Δ : Telescope n) → ℕ → (D : Set) → (D → Set) → Set₁ where
    here : ∀ {i : ℕ}{D : Set}{S : D → Set} (d : D) {Δ : (s : S d) → Telescope i} → (cons (S d) Δ) [ zero ]∶Σ[ D ] S
    there : ∀ {i : ℕ}{T D : Set}{S : D → Set}{Δ : (t : T) → Telescope (suc i)}{n : ℕ} 
        → ((t : T) → (Δ t) [ n ]∶Σ[ D ] S) → (cons T Δ) [ suc n ]∶Σ[ D ] S

syntax there (λ t → T) = t > T

_Σ[_] : ∀ {n k : ℕ} {T : Telescope n} {D : Set} {S : D → Set} → ⟦ T ⟧telD → T [ k ]∶Σ[ D ] S 
    → Σ[ d ∈ D ] (S d)
(s , _) Σ[ here d ]   = d , s
(s , t) Σ[ there k ] = t Σ[ k s ]

_Σ[_]Δ : ∀ {n k : ℕ} {T : Telescope n} {D : Set} {S : D → Set} → ⟦ T ⟧telD → T [ k ]∶Σ[ D ] S 
    → Σ[ d ∈ D ] ((s : S d) → Telescope (n ∸ (suc k)))
(s , _) Σ[ here {i = i} d {Δ = Δ} ]Δ = d , Δ 
(s , t) Σ[ there k ]Δ =  t Σ[ k s ]Δ

-- merge two telescopes X and Y
mergeTel
  : {n m : ℕ} (X : Telescope n) {A : Set} (Y : A → Telescope m)
  → (⟦ X ⟧telD → A)
  → Telescope (n + m)
mergeTel nil            Y f = Y (f tt)
mergeTel (cons S T) Y f = s ∈ S , mergeTel (T s) Y (λ t → f (s , t))


merge
  : {n m : ℕ}{X : Telescope n} {A : Set} {Y : A → Telescope m}
    {f : ⟦ X ⟧telD → A}
    (x : ⟦ X ⟧telD)
  → ⟦ Y (f x) ⟧telD
  → ⟦ mergeTel X Y f ⟧telD
merge {X = nil         } {f = f} x       t = t
merge {X = cons S T} {f = f} (s , x) t = s , merge x t


mergePrefix
  : {n m : ℕ}{X : Telescope n} {A : Set} {Y : A → Telescope m}
    {f : ⟦ X ⟧telD → A}
  → ⟦ mergeTel X Y f ⟧telD
  → ⟦ X ⟧telD
mergePrefix {X = nil         } t       = tt
mergePrefix {X = cons S T} (s , t) = s , mergePrefix t

mergeSuffix
  : {n m : ℕ}(X : Telescope n) {A : Set} (Y : A → Telescope m)
    {f : ⟦ X ⟧telD → A}
  → (t : ⟦ mergeTel X Y f ⟧telD)
  → ⟦ Y (f (mergePrefix t)) ⟧telD
mergeSuffix (nil         ) Y t       = t
mergeSuffix (cons S T) Y (s , t) = mergeSuffix (T s) Y t


shrinkMerge
  : ∀{ℓ}{n m : ℕ}{X : Telescope n} {A : Set} {Y : A → Telescope m}
    {f : ⟦ X ⟧telD → A}
    (P : ⟦ x ∈ A , Y x ⟧telD → Set ℓ)
    (x : ⟦ X ⟧telD)
    (y : ⟦ Y (f x) ⟧telD)
  → P ( f (mergePrefix {Y = Y} {f = f} (merge x y))
      , mergeSuffix X Y {f = f} (merge x y)
      )
  → P (f x    , y)
shrinkMerge {X = nil         } P x       y p = p
shrinkMerge {X = cons S T} P (s , x) y p = shrinkMerge P x y p

mergeShrink
  : ∀{ℓ}{n m : ℕ}{X : Telescope n} {A : Set} {Y : A → Telescope m}
    {f : ⟦ X ⟧telD → A}
    (P : ⟦ x ∈ A , Y x ⟧telD → Set ℓ)
    (x : ⟦ X ⟧telD)
    (y : ⟦ Y (f x) ⟧telD)
  → P (f x    , y)
  → P ( f (mergePrefix {Y = Y} {f = f} (merge x y))
      , mergeSuffix X Y {f = f} (merge x y)
      )
mergeShrink {X = nil}      P x       y p = p
mergeShrink {X = cons S T} P (s , x) y p = mergeShrink P x y p



-- insert a telescope at a given position in an input telescope
expandTel
  : {n m k : ℕ}(T : Telescope n){D : Set}{A : D → Set} (Δ : D → Telescope m) 
    (f : (d : D) → ⟦ Δ d ⟧telD → A d)
  → T [ k ]∶Σ[ D ] A
  → Telescope (k + (m + (n ∸ suc k)))
expandTel (cons A T) Δ f (here d)  = mergeTel (Δ d) T (f d)
expandTel (cons A T) Δ f (there k) = x ∈ A , expandTel (T x) Δ f (k x)

expandSort
  : ∀{ℓ}{n m k : ℕ}{T : Telescope n}{D : Set}{A : D → Set}{Δ : D → Telescope m}
    {f : (d : D) → ⟦ Δ d ⟧telD → A d}
    (p : T [ k ]∶Σ[ D ] A)
  → (⟦ T ⟧telD → Set ℓ)
  → (⟦ expandTel T Δ f p ⟧telD → Set ℓ)
expandSort {T = cons S T} {Δ = Δ} {f = f} (here d) X t
  = X ((f d (mergePrefix t)) , mergeSuffix (Δ d) T t) 
expandSort (there k) X (s , t) = expandSort (k s) (λ x → X (s , x)) t

expand
  : {n m k : ℕ}{T   : Telescope n}{D : Set}{A : D → Set}{Δ : D → Telescope m}
    {f   : (d : D) → ⟦ Δ d ⟧telD → A d}
    (s   : T [ k ]∶Σ[ D ] A)
    {d : D}
    {x   : A d}
    (d'   : ⟦ Δ d ⟧telD)
    (fd  : f d d' ≡ x)
    (t   : ⟦ T ⟧telD)
  → t Σ[ s ] ≡ (d , x)
  → ⟦ expandTel T Δ f s ⟧telD
expand (here d') d refl (s , t) refl = merge d t
expand (there k) d fd   (s , t) p    = s , expand (k s) d fd t p 

shrinkExpand
  : ∀{ℓ}{n m k : ℕ} {T : Telescope n}{D : Set}{A : D → Set}{Δ : D → Telescope m}
    {f : (d : D) → ⟦ Δ d ⟧telD → A d}
    (p : T [ k ]∶Σ[ D ] A)
    {d : D}
    {x   : A d}
    (d'   : ⟦ Δ d ⟧telD)
    (fd  : f d d' ≡ x)
    (X : ⟦ T ⟧telD → Set ℓ)
    (t : ⟦ T ⟧telD)
    (e : t Σ[ p ] ≡ (d , x))
  → expandSort p X (expand {f = f} p d' fd t e)
  → X t
shrinkExpand (here d') d refl X (_ , dt) refl t = shrinkMerge X d dt t
shrinkExpand (there p) d fd   X (s , dt) e t    = shrinkExpand (p s) d fd (λ x → X (s , x)) dt e t

data _[_]∶_ : {n : ℕ} → Telescope n → ℕ → Set → Set where
    here : ∀ {i : ℕ}{S : Set}{Δ : (s : S) → Telescope i} → (cons S Δ) [ zero ]∶ S
    there : ∀ {i : ℕ}{S T : Set}{Δ : (t : T) → Telescope (suc i)}{n : ℕ} 
            → ((t : T) → (Δ t) [ n ]∶ S) → (cons T Δ) [ suc n ]∶ S

_[_] : ∀ {n k : ℕ} {T : Telescope n} {A} → ⟦ T ⟧telD → T [ k ]∶ A → A
(s , _) [ here ]   = s
(s , t) [ there k ] = t [ k s ]

replaceTel
  : {n m : ℕ} {X : Set} (x : X) (T : Telescope (suc n)) (p : T [ m ]∶ X)
    → Telescope n
replaceTel x (cons S E) here = E x
replaceTel x (cons S E) (there p) = cons S (λ s → replaceTel x (E s) (p s))

replace 
  : {n m : ℕ} {X : Set}  {T : Telescope (suc n)} (p : T [ m ]∶ X)
    → (xs : ⟦ T ⟧telD)
    → ⟦ replaceTel (xs [ p ]) T p ⟧telD
replace here (s , xs) = xs
replace (there p) (s , xs) = s , replace (p s) xs

linvReplace 
  : {n m : ℕ} {X : Set}  {T : Telescope (suc n)} (x : X) (p : T [ m ]∶ X)
    → (xs : ⟦ replaceTel x T p ⟧telD)
    → ⟦ T ⟧telD
linvReplace x here xs = x , xs
linvReplace x (there p) (s , xs) = s , linvReplace x (p s) xs

isLinvReplace 
  : {n m : ℕ} {X : Set}  {T : Telescope (suc n)} (p : T [ m ]∶ X)
    → (xs : ⟦ T ⟧telD)
    → linvReplace (xs [ p ]) p (replace p xs) ≡ xs
isLinvReplace here (s , xs) = refl
isLinvReplace (there p) (s , xs) = subst (λ xs' → (s , xs') ≡ (s , xs)) (sym (isLinvReplace (p s) xs)) refl


moveBackTel
  : {n m : ℕ} (T : Telescope n) {X : Set} (p : T [ m ]∶ X)
    → (goal : Fin m)
    → Telescope n 
moveBackTel (cons S E) {X} p fzero = cons X (λ x → replaceTel x (cons S E) p)
moveBackTel (cons S E) (there p) (fsuc goal) = cons S λ s → moveBackTel (E s) (p s) goal 

moveBack
  : {n m : ℕ} {T : Telescope n} {X : Set} (p : T [ m ]∶ X)
    → (goal : Fin m)
    → (xs : ⟦ T ⟧telD)
    → ⟦ moveBackTel T p goal ⟧telD
moveBack {T = cons S E} p fzero (s , xs) = (s , xs) [ p ] , replace p (s , xs) 
moveBack (there p) (fsuc goal) (s , xs) = s , moveBack (p s) goal xs 

linvMoveBack
  : {n m : ℕ} {T : Telescope n} {X : Set} (p : T [ m ]∶ X)
    → (goal : Fin m)
    → (xs : ⟦ moveBackTel T p goal ⟧telD)
    → ⟦ T ⟧telD
linvMoveBack {T = cons S E} p fzero (s , xs) = linvReplace s p xs
linvMoveBack (there p) (fsuc goal) (s , xs) = s , linvMoveBack (p s) goal xs 

isLinvMoveBack
  : {n m : ℕ} {T : Telescope n} {X : Set} (p : T [ m ]∶ X)
    → (goal : Fin m)
    → (xs : ⟦ T ⟧telD)
    → linvMoveBack p goal (moveBack p goal xs) ≡ xs
isLinvMoveBack {T = cons S E} p fzero xs = isLinvReplace p xs
isLinvMoveBack (there p) (fsuc goal) (s , xs) = subst (λ xs' → (s , xs') ≡ (s , xs)) (sym (isLinvMoveBack (p s) goal xs)) refl

splitTel : {n : ℕ} (X : Telescope n) (m : Fin n)
    → Σ[ X ∈ Telescope (toℕ m) ] (⟦ X ⟧telD → Telescope (n ∸ (toℕ m)))
splitTel (cons S E) fzero = nil , (λ _ → cons S E)
splitTel (cons S E) (fsuc m) = cons S (λ s → proj₁ (splitTel (E s) m)) 
                                , (λ x → proj₂ (splitTel (E (proj₁ x)) m) (proj₂ x))


reorderTel : {n k : ℕ} (split : Fin n) (T : Telescope n) (goal : Fin k)
  → (p : (x : ⟦ proj₁ (splitTel T split) ⟧telD) → (Σ[ X ∈ Set ] ((proj₂ (splitTel T split)) x) [ k ]∶ X))
  → Telescope n
reorderTel fzero (cons S E) goal p = moveBackTel (cons S E) (proj₂ (p tt)) goal
reorderTel (fsuc split) (cons S E) goal p = cons S (λ s → reorderTel split (E s) goal (λ x → p (s , x)))

reorder : {n k : ℕ} (split : Fin n) {T : Telescope n} (goal : Fin k)
  → (p : (x : ⟦ proj₁ (splitTel T split) ⟧telD) → (Σ[ X ∈ Set ] ((proj₂ (splitTel T split)) x) [ k ]∶ X))
  → (xs : ⟦ T ⟧telD)
  → ⟦ reorderTel split T goal p ⟧telD
reorder fzero {cons S E} goal p xs = moveBack (proj₂ (p tt)) goal xs
reorder (fsuc split) {T = cons S E} goal p (s , xs) = s , reorder split goal (λ x → p (s , x)) xs 

linvReorder : {n k : ℕ} (split : Fin n) {T : Telescope n} (goal : Fin k)
  → (p : (x : ⟦ proj₁ (splitTel T split) ⟧telD) → (Σ[ X ∈ Set ] ((proj₂ (splitTel T split)) x) [ k ]∶ X))
  → (xs : ⟦ reorderTel split T goal p ⟧telD)
  → ⟦ T ⟧telD
linvReorder fzero {T = cons S E} goal p xs = linvMoveBack (proj₂ (p tt)) goal xs
linvReorder (fsuc split) {T = cons S E} goal p (s , xs) = s , linvReorder split goal (λ x → p (s , x)) xs 

isLinvReorder : {n k : ℕ} (split : Fin n) {T : Telescope n} (goal : Fin k)
  → (p : (x : ⟦ proj₁ (splitTel T split) ⟧telD) → (Σ[ X ∈ Set ] ((proj₂ (splitTel T split)) x) [ k ]∶ X))
  → (xs : ⟦ T ⟧telD)
  → linvReorder split goal p (reorder split goal p xs) ≡ xs
isLinvReorder fzero {T = cons S E} goal p xs = isLinvMoveBack (proj₂ (p tt)) goal xs
isLinvReorder (fsuc split) {T = cons S E} goal p (s , xs) = subst (λ xs' → (s , xs') ≡ (s , xs)) (sym (isLinvReorder split goal (λ x → p (s , x)) xs)) refl
