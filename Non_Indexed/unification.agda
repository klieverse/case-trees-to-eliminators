{-# OPTIONS --allow-unsolved-metas #-}
module Non_Indexed.unification where

open import Non_Indexed.datatypes
open import Non_Indexed.telescope

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Data.Sum
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Data.Empty
open import Function.Base using (id)
open import Agda.Builtin.Equality
open import Data.Fin using (Fin; fromℕ<; fromℕ; toℕ; raise; _≟_ ) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Vec using (Vec; []; _∷_)

private variable
  A     : Set
  t     : A

-- the solution rule
solution : (x : A)(e : t ≡ x) → ⊤
solution x e = tt

linvSolution : ⊤ → Σ[ x ∈ A ] (t ≡ x)
linvSolution {t = t} _ = t , refl

isLinvSolution : (x : A)(e : t ≡ x) → linvSolution (solution x e) ≡ (x , e)
isLinvSolution {t = t} x = J (λ x e → (t , refl) ≡ (x , e)) refl

solution' : (x : A)(e : x ≡ t) → ⊤
solution' x e = tt

linvSolution' : ⊤ → Σ[ x ∈ A ] (x ≡ t)
linvSolution' {t = t} _ = t , refl

isLinvSolution' : (x : A)(e : x ≡ t) → linvSolution' (solution' x e) ≡ (x , e)
isLinvSolution' {t = t} x = J' (λ x e → (t , refl) ≡ (x , e)) refl

-- Add move in telescope

data _[_]∶[_][_]_ : {n : ℕ} → (Δ : Telescope n) → ℕ → (D D' : Set) → (D → D' → Set) → Set₁ where
    here : ∀ {i : ℕ}{D D' : Set}{S : D → D' → Set} (d : D) {Δ : (d' : D')(s : S d d') → Telescope i} 
            → (cons D' (λ d' → cons (S d d') (Δ d'))) [ zero ]∶[ D ][ D' ] S
    there : ∀ {i : ℕ}{T D D' : Set}{S : D → D' → Set}{Δ : (t : T) → Telescope (suc (suc i))}{n : ℕ} 
        → ((t : T) → (Δ t) [ n ]∶[ D ][ D' ] S) → (cons T Δ) [ suc n ]∶[ D ][ D' ] S

doSolutionTel : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶[ A ][ A ] (λ t x → t ≡ x))
    → Telescope (i ∸ 2)
doSolutionTel {Δ = cons S E} (here d {Δ}) = Δ d refl
doSolutionTel {Δ = cons S E} (there p) = cons S (λ s → doSolutionTel (p s)) 

doSolution : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶[ A ][ A ] (λ t x → t ≡ x)) (xs : ⟦ Δ ⟧telD)
    → ⟦ doSolutionTel p ⟧telD
doSolution (here d {Δ}) (x , e , xs) = subst (λ ex → ⟦ Δ (proj₁ ex) (proj₂ ex) ⟧telD) (sym (isLinvSolution x e)) xs 
doSolution (there p) (x , xs) = x , doSolution (p x) xs 

linvDoSolution : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶[ A ][ A ] (λ t x → t ≡ x)) → ⟦ doSolutionTel p ⟧telD
    → ⟦ Δ ⟧telD
linvDoSolution (here d) xs = d , refl , xs
linvDoSolution (there p) (x , xs) = x , linvDoSolution (p x) xs

isLinvDoSolution : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶[ A ][ A ] (λ t x → t ≡ x)) (xs : ⟦ Δ ⟧telD)
    → linvDoSolution p (doSolution p xs) ≡ xs
isLinvDoSolution (here d {Δ}) (x , e , xs) = J (λ x' e' → (xs' : ⟦ Δ (proj₁ x') (proj₂ x') ⟧telD) → xs' ≡ subst (λ ex → ⟦ Δ (proj₁ ex) (proj₂ ex) ⟧telD) e' xs → (proj₁ x' , proj₂ x' , xs') ≡ (x , e , xs)) 
        (λ xs' e' → subst (λ xs' → (x , e , xs') ≡ (x , e , xs)) (sym e') refl) 
        (sym (isLinvSolution x e)) 
        (subst (λ ex → ⟦ Δ (proj₁ ex) (proj₂ ex) ⟧telD) (sym (isLinvSolution x e)) xs) 
        refl 
isLinvDoSolution (there p) (x , xs) = subst (λ xs' → (x , xs') ≡ (x , xs)) (sym (isLinvDoSolution (p x) xs)) refl


doSolutionTel' : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶[ A ][ A ] (λ t x → x ≡ t))
    → Telescope (i ∸ 2)
doSolutionTel' {Δ = cons S E} (here d {Δ}) = Δ d refl
doSolutionTel' {Δ = cons S E} (there p) = cons S (λ s → doSolutionTel' (p s)) 

doSolution' : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶[ A ][ A ] (λ t x → x ≡ t)) (xs : ⟦ Δ ⟧telD)
    → ⟦ doSolutionTel' p ⟧telD
doSolution' (here d {Δ}) (x , e , xs) = subst (λ ex → ⟦ Δ (proj₁ ex) (proj₂ ex) ⟧telD) (sym (isLinvSolution' x e)) xs 
doSolution' (there p) (x , xs) = x , doSolution' (p x) xs 

linvDoSolution' : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶[ A ][ A ] (λ t x → x ≡ t)) → ⟦ doSolutionTel' p ⟧telD
    → ⟦ Δ ⟧telD
linvDoSolution' (here d) xs = d , refl , xs
linvDoSolution' (there p) (x , xs) = x , linvDoSolution' (p x) xs

isLinvDoSolution' : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶[ A ][ A ] (λ t x → x ≡ t)) (xs : ⟦ Δ ⟧telD)
    → linvDoSolution' p (doSolution' p xs) ≡ xs
isLinvDoSolution' (here d {Δ}) (x , e , xs) = J (λ x' e' → (xs' : ⟦ Δ (proj₁ x') (proj₂ x') ⟧telD) → xs' ≡ subst (λ ex → ⟦ Δ (proj₁ ex) (proj₂ ex) ⟧telD) e' xs → (proj₁ x' , proj₂ x' , xs') ≡ (x , e , xs)) 
        (λ xs' e' → subst (λ xs' → (x , e , xs') ≡ (x , e , xs)) (sym e') refl) 
        (sym (isLinvSolution' x e)) 
        (subst (λ ex → ⟦ Δ (proj₁ ex) (proj₂ ex) ⟧telD) (sym (isLinvSolution' x e)) xs) 
        refl 
isLinvDoSolution' (there p) (x , xs) = subst (λ xs' → (x , xs') ≡ (x , xs)) (sym (isLinvDoSolution' (p x) xs)) refl


-- the deletion rule
deletion : (e : t ≡ t) → ⊤ 
deletion e = tt

linvDeletion : ⊤ → t ≡ t 
linvDeletion _ = refl

isLinvDeletion : (e : t ≡ t) → linvDeletion (deletion e) ≡ e 
isLinvDeletion refl = refl

doDeletionTel : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶Σ[ ⊤ ] (λ _ → t ≡ t))
    → Telescope (i ∸ 1)
doDeletionTel {Δ = cons S E} (here x {Δ = Δ}) = Δ refl
doDeletionTel {Δ = cons S E} (there p) = cons S (λ s → doDeletionTel (p s)) 

doDeletion : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶Σ[ ⊤ ] (λ _ → t ≡ t)) (xs : ⟦ Δ ⟧telD)
    → ⟦ doDeletionTel p ⟧telD
doDeletion (here tt {Δ = Δ}) (refl , xs) = xs
doDeletion (there p) (x , xs) = x , doDeletion (p x) xs 

linvDoDeletion : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶Σ[ ⊤ ] (λ _ → t ≡ t)) (xs : ⟦ doDeletionTel p ⟧telD)
    → ⟦ Δ ⟧telD
linvDoDeletion (here tt {Δ = Δ}) xs = refl , xs 
linvDoDeletion (there p) (x , xs) = x , linvDoDeletion (p x) xs 

isLinvDoDeletion : {i : ℕ} {Δ : Telescope i} {j : ℕ}
    (p : Δ [ j ]∶Σ[ ⊤ ] (λ _ → t ≡ t)) (xs : ⟦ Δ ⟧telD)
    → linvDoDeletion p (doDeletion p xs) ≡ xs
isLinvDoDeletion (here tt {Δ = Δ}) (refl , xs) = refl
isLinvDoDeletion (there p) (x , xs) = subst (λ e → (x , e) ≡ (x , xs)) (sym (isLinvDoDeletion (p x) xs)) refl


-- NoConfusion
private variable
  i j : ℕ

NoConfusionC : {D : DataDesc i}{C : ConDesc j} (x₁ x₂ : ⟦ C ⟧c (μ D)) → Telescope j
NoConfusionC {C = one'} _ _ = nil
NoConfusionC {D = D} {C = Σ' S C} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , NoConfusionC (subst (λ x → ⟦ C x ⟧c (μ D)) e xs₁) xs₂
NoConfusionC {C = ind×' C} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , NoConfusionC xs₁ xs₂

NoConfusion' : {D : DataDesc i} (x₁ x₂ : ⟦ D ⟧ (μ D)) → Dec (proj₁ x₁ ≡ proj₁ x₂) → Σ ℕ Telescope
NoConfusion' {D = D} x₁ x₂ (yes e) = proj₁ (D (proj₁ x₁)) , NoConfusionC (proj₂ x₁) (subst (λ x → ⟦ proj₂ (D x) ⟧c (μ D)) (sym e) (proj₂ x₂))
NoConfusion' x₁ x₂ (no _) = 1 , (_ ∈ ⊥ , nil)

NoConfusion : {D : DataDesc i} (x₁ x₂ : μ D) → Dec (conᵢ x₁ ≡ conᵢ x₂) → Σ ℕ Telescope
NoConfusion {D = D} = case-μ D (λ x₁' → (x₂' : μ D) → Dec (conᵢ x₁' ≡ conᵢ x₂') → Σ ℕ Telescope) 
        (λ x₁' → case-μ D (λ x₂' → Dec (proj₁ x₁' ≡ conᵢ x₂') → Σ ℕ Telescope) 
            (NoConfusion' x₁'))

-- no confusion 
noConfC : {D : DataDesc i}{C : ConDesc j} → (c : ⟦ C ⟧c (μ D)) → ⟦ NoConfusionC c c ⟧telD
noConfC {C = one'} c = tt
noConfC {C = Σ' S D} (c , cs) = refl , noConfC cs
noConfC {D = D} {C = ind×' C} (c , cs) = refl , noConfC cs

noConf' : {D : DataDesc i}(x : ⟦ D ⟧ (μ D)) → ⟦ proj₂ (NoConfusion ⟨ x ⟩ ⟨ x ⟩ (yes refl)) ⟧telD
noConf' (n , c) = noConfC c

noConf : {D : DataDesc i} (x₁ x₂ : μ D) (e : x₁ ≡ x₂) (f : Dec (conᵢ x₁ ≡ conᵢ x₂)) 
    → ⟦ proj₂ (NoConfusion x₁ x₂ f) ⟧telD
noConf {D = D} x₁ x₂ e = subst (λ x → (f : Dec (conᵢ x₁ ≡ conᵢ x)) → ⟦ proj₂ (NoConfusion x₁ x f) ⟧telD) e λ where
    (yes refl) → case-μ D (λ x' → ⟦ proj₂ (NoConfusion x' x' (yes refl)) ⟧telD) noConf' x₁ 
    (no x) → case-μ D (λ x' → (x : ¬ conᵢ x' ≡ conᵢ x') → ⟦ proj₂ (NoConfusion x' x' (no x)) ⟧telD) (λ d x → (x refl) , tt) x₁ x

-- left inverse no confusion 
linvNoConfC : {D : DataDesc i}{C : ConDesc j}
    → (x₁ x₂ : ⟦ C ⟧c (μ D)) → ⟦ NoConfusionC x₁ x₂ ⟧telD → x₁ ≡ x₂
linvNoConfC {C = one'} x₁ x₂ e = refl 
linvNoConfC {D = D} {C = Σ' S D'} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    = J (λ x₂ e → (xs₂ : ⟦ D' x₂ ⟧c (μ D)) → subst (λ x → ⟦ D' x ⟧c (μ D)) e xs₁ ≡ xs₂ → (x₁ , xs₁) ≡ (x₂ , xs₂)) 
        (λ xs₂ e₂ → subst (λ x → (x₁ , xs₁) ≡ (x₁ , x)) e₂ refl)
        e xs₂ (linvNoConfC (subst (λ s → ⟦ D' s ⟧c (μ D)) e xs₁) xs₂ es)
linvNoConfC {D = D} {C = ind×' C} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    = subst (λ xs₂ → (x₁ , xs₁) ≡ (x₂ , xs₂)) (linvNoConfC xs₁ xs₂ es) 
        (subst (λ x₂ → (x₁ , xs₁) ≡ (x₂ , xs₁)) e refl)
    
linvNoConf' : {D : DataDesc i} (x₁ x₂ : ⟦ D ⟧ (μ D))
     → (f : Dec (proj₁ x₁ ≡ proj₁ x₂)) → ⟦ proj₂ (NoConfusion ⟨ x₁ ⟩ ⟨ x₂ ⟩ f) ⟧telD → ⟨ x₁ ⟩ ≡ ⟨ x₂ ⟩
linvNoConf' (n₁ , x₁) (n₂ , x₂) (yes refl) e = cong (λ x → ⟨ n₁ , x ⟩) (linvNoConfC x₁ x₂ e) 
linvNoConf' x₁ x₂ (no d) e = ⊥-elim (proj₁ e)

linvNoConf : {D : DataDesc i} (x₁ x₂ : μ D)
    → (f : Dec (conᵢ x₁ ≡ conᵢ x₂)) → ⟦ proj₂ (NoConfusion x₁ x₂ f) ⟧telD → x₁ ≡ x₂
linvNoConf {D = D} 
    = case-μ D (λ x₁' → (x₂' : μ D) → (f' : Dec (conᵢ x₁' ≡ conᵢ x₂')) → ⟦ proj₂ (NoConfusion x₁' x₂' f') ⟧telD → x₁' ≡ x₂') 
        (λ x₁' → case-μ D (λ x₂' → (f' : Dec (proj₁ x₁' ≡ conᵢ x₂')) → ⟦ proj₂ (NoConfusion ⟨ x₁' ⟩ x₂' f') ⟧telD → ⟨ x₁' ⟩ ≡ x₂') 
            (linvNoConf' x₁'))

-- proof of left inverse no confusion
isLinvNoConfC : {D : DataDesc i}{C : ConDesc j} (x : ⟦ C ⟧c (μ D))
    → linvNoConfC x x (noConfC x) ≡ refl
isLinvNoConfC {C = one'} x = refl
isLinvNoConfC {D = D} {C = Σ' S E} (s , x) = subst (λ e → subst (λ x₁ → (s , x) ≡ (s , x₁)) e refl ≡ refl) (sym (isLinvNoConfC x)) refl
isLinvNoConfC {D = D}{C = ind×' C'} (u , x) = subst (λ e → subst (λ xs → (u , x) ≡ (u , xs)) e refl
      ≡ refl) (sym (isLinvNoConfC x)) refl 

isLinvNoConf' : {D : DataDesc i} {n : Fin i} (x : ⟦ proj₂ (D n) ⟧c (μ D)) 
    → linvNoConf ⟨ n , x ⟩ ⟨ n , x ⟩ (yes refl) (noConf ⟨ n , x ⟩ ⟨ n , x ⟩ refl (yes refl)) ≡ refl
isLinvNoConf' {D = D} {n} x = subst (λ e → cong (λ x₁ → ⟨ n , x₁ ⟩) e ≡ refl) (sym (isLinvNoConfC x)) refl 

isLinvNoConf : {D : DataDesc i} → (x₁ x₂ : μ D)
    → (e : x₁ ≡ x₂) → (f : Dec (conᵢ x₁ ≡ conᵢ x₂)) → linvNoConf x₁ x₂ f (noConf x₁ x₂ e f) ≡ e
isLinvNoConf {D = D} x₁ x₂ refl (yes refl) = case-μ D (λ x → linvNoConf x x (yes refl) (noConf x x refl (yes refl)) ≡ refl) 
    (λ x → isLinvNoConf' (proj₂ x)) x₁ 
isLinvNoConf {D = D} x₁ x₂ e (no f) = ⊥-elim (f (cong conᵢ e)) 


-- the injectivity rule 
injectivity : {D : DataDesc i} → (s t : μ D) 
    → (e' : conᵢ s ≡ conᵢ t)
    → (e : s ≡ t) → ⟦ proj₂ (NoConfusion s t (yes e')) ⟧telD
injectivity {D} s t e' e = noConf s t e (yes e') 

linvInjectivity : {D : DataDesc i} → (s t : μ D)
    → (e' : conᵢ s ≡ conᵢ t)
    → ⟦ proj₂ (NoConfusion s t (yes e')) ⟧telD
    → s ≡ t
linvInjectivity {D} s t e' e = linvNoConf s t (yes e') e 

isLinvinjectivity : {D : DataDesc i} → (s t : μ D) 
    → (e' : conᵢ s ≡ conᵢ t)
    → (e : s ≡ t) → linvInjectivity s t e' (injectivity s t e' e) ≡ e
isLinvinjectivity {D} s t e' e = isLinvNoConf s t e (yes e')

doInjectivityTel' : {D : DataDesc i} → (s t : μ D) 
    → (e' : conᵢ s ≡ conᵢ t)
    → proj₁ (NoConfusion s t (yes e')) ≡ conₙ s 
doInjectivityTel' {D = D} = case-μ D (λ s → (t : μ D) → (e' : (conᵢ s ≡ conᵢ t)) → proj₁ (NoConfusion s t (yes e')) ≡ conₙ s) 
            (λ s → case-μ D (λ t → (e' : (conᵢ ⟨ s ⟩ ≡ conᵢ t)) → proj₁ (NoConfusion ⟨ s ⟩ t (yes e')) ≡ conₙ ⟨ s ⟩) 
            (λ t e' → refl))    

doInjectivityTel : {D' : Set}{n i j k : ℕ}{D : DataDesc i} {Δ : Telescope n}
  → {s t : D' → μ D}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
  → Telescope (k + j + (n ∸ suc k))
doInjectivityTel {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) = subst (λ j → Telescope (j + i)) (trans (doInjectivityTel' (s d) (t d) (e' d)) (eℕ d)) 
    (mergeTel (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E (linvInjectivity (s d) (t d) (e' d))) 
doInjectivityTel {Δ = cons S E} {s} {t} e' eℕ (there x) = cons S (λ s → doInjectivityTel e' eℕ (x s))

doInjectivity : {D' : Set}{n i j k : ℕ}{D : DataDesc i}{Δ : Telescope n}
  → {s t : D' → μ D}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d'))) (xs : ⟦ Δ ⟧telD)
  → ⟦ doInjectivityTel e' eℕ p ⟧telD
doInjectivity {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) (e , xs) = J 
    (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E (linvInjectivity (s d) (t d) (e' d))) ⟧telD) 
    (merge (injectivity (s d) (t d) (e' d) e) (subst (λ e → ⟦ E e ⟧telD) (sym (isLinvinjectivity (s d) (t d) (e' d) e)) xs)) 
    (trans (doInjectivityTel' (s d) (t d) (e' d)) (eℕ d))
doInjectivity {Δ = cons S E} {s} {t} e' eℕ (there p) (x , xs) = x , doInjectivity e' eℕ (p x) xs 

linvDoInjectivity : {D' : Set}{n i j k : ℕ}{D : DataDesc i}{Δ : Telescope n}
  → {s t : D' → μ D}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d'))) (xs : ⟦ doInjectivityTel e' eℕ p ⟧telD)
  → ⟦ Δ ⟧telD
linvDoInjectivity {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) xs = (linvInjectivity (s d) (t d) (e' d) (mergePrefix xs')) 
    , mergeSuffix (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E xs'  where 
    
    xs' : ⟦ mergeTel (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E (linvInjectivity (s d) (t d) (e' d)) ⟧telD
    xs' = linvJ (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E (linvInjectivity (s d) (t d) (e' d))) ⟧telD) 
            (trans (doInjectivityTel' (s d) (t d) (e' d)) (eℕ d)) xs
    
linvDoInjectivity {Δ = cons S E} {s} {t} e' eℕ (there p) (x , xs) = x , linvDoInjectivity e' eℕ (p x) xs 

isLinvDoInjectivity : {D' : Set}{n i j k : ℕ}{D : DataDesc i}{Δ : Telescope n}
  → {s t : D' → μ D}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d'))) (xs : ⟦ Δ ⟧telD)
  → linvDoInjectivity e' eℕ p (doInjectivity e' eℕ p xs) ≡ xs
isLinvDoInjectivity {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) (e , xs) = goal where

    xs' : ⟦ mergeTel (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E (linvInjectivity (s d) (t d) (e' d)) ⟧telD 
    xs' = linvJ (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E (linvInjectivity (s d) (t d) (e' d))) ⟧telD) 
            (trans (doInjectivityTel' (s d) (t d) (e' d)) (eℕ d)) 
                (J (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E (linvInjectivity (s d) (t d) (e' d))) ⟧telD) 
                (merge (injectivity (s d) (t d) (e' d) e) (subst (λ e → ⟦ E e ⟧telD) (sym (isLinvinjectivity (s d) (t d) (e' d) e)) xs)) 
                (trans (doInjectivityTel' (s d) (t d) (e' d)) (eℕ d)))

    goal : (linvInjectivity (s d) (t d) (e' d) (mergePrefix xs'),
       mergeSuffix (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E xs')
      ≡ (e , xs)
    goal = subst (λ xs' → (linvInjectivity (s d) (t d) (e' d) (mergePrefix xs') ,  mergeSuffix (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E xs') ≡ (e , xs)) 
            (sym (isLinvJ ((λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E (linvInjectivity (s d) (t d) (e' d))) ⟧telD)) 
            (merge (injectivity (s d) (t d) (e' d) e) (subst (λ e → ⟦ E e ⟧telD) (sym (isLinvinjectivity (s d) (t d) (e' d) e)) xs)) 
            (trans (doInjectivityTel' (s d) (t d) (e' d)) (eℕ d)))) 
            (mergeShrink {f = linvInjectivity (s d) (t d) (e' d)} (λ ex → ex ≡ (e , xs))
                (injectivity (s d) (t d) (e' d) e) (subst (λ e → ⟦ E e ⟧telD) (sym (isLinvinjectivity (s d) (t d) (e' d) e)) xs) 
                (J (λ x' e' → (x' , subst (λ e → ⟦ E e ⟧telD) e' xs) ≡ (e , xs)) refl  (sym (isLinvinjectivity (s d) (t d) (e' d) e))))

isLinvDoInjectivity {Δ = cons S E} {s} {t} e' eℕ (there p) (x , xs) = subst (λ xs' → (x , xs') ≡ (x , xs)) (sym (isLinvDoInjectivity e' eℕ (p x) xs)) refl


-- the conflict rule
conflict : {D : DataDesc i} (s t : μ D)
    → (e' : ¬ (conᵢ s ≡ conᵢ t))
    → (e : s ≡ t)
    → ⊥
conflict {D = D} 
    = case-μ D (λ s → (t : μ D) → ¬ (conᵢ s ≡ conᵢ t) → s ≡ t → ⊥) 
            (λ s → case-μ D (λ t  → ¬ (conᵢ ⟨ s ⟩ ≡ conᵢ t) → ⟨ s ⟩ ≡ t → ⊥) 
            (λ t e' e → proj₁ (noConf ⟨ s ⟩ ⟨ t ⟩ e (no e')))) 

linvConflict : {D : DataDesc i} (s t : μ D)
    → (e' : ¬ (conᵢ s ≡ conᵢ t))
    → ⊥
    → s ≡ t
linvConflict {D = D}
    = case-μ D (λ s → (t : μ D) → ¬ (conᵢ s ≡ conᵢ t) → ⊥ → s ≡ t) 
        (λ s → case-μ D (λ t  → ¬ (conᵢ ⟨ s ⟩ ≡ conᵢ t) → ⊥ → ⟨ s ⟩ ≡ t) 
        (λ t e' b → linvNoConf ⟨ s ⟩ ⟨ t ⟩ (no e') (b , tt))) 

isLinvConflict : {D : DataDesc i} (s t : μ D)
    → (e' : ¬ (conᵢ s ≡ conᵢ t))
    → (e : s ≡ t)
    → linvConflict s t e' (conflict s t e' e) ≡ e
isLinvConflict {D = D}
    = case-μ D (λ s → (t : μ D) → (e' : ¬ (conᵢ s ≡ conᵢ t)) → (e : s ≡ t) → linvConflict s t e' (conflict s t e' e) ≡ e) 
            (λ s → case-μ D (λ t  → (e' : ¬ (conᵢ ⟨ s ⟩ ≡ conᵢ t)) → (e : ⟨ s ⟩ ≡ t) → linvConflict ⟨ s ⟩ t e' (conflict ⟨ s ⟩ t e' e) ≡ e) 
            (λ t e' e → isLinvNoConf ⟨ s ⟩ ⟨ t ⟩ e (no e'))) 

doConflictTel :  {i j : ℕ} {Δ : Telescope i} {D : DataDesc j}{D' : Set}
        → {s t : D' → μ D} {x : ℕ} (p : Δ [ x ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
        → (e' : (d : D') → ¬ (conᵢ (s d) ≡ conᵢ (t d)))
        → Telescope i
doConflictTel {Δ = cons E Δ} {s = s} {t = t} (here d) e' = b ∈ ⊥ , Δ (linvConflict (s d) (t d) (e' d) b)
doConflictTel {Δ = cons S E} (there p) e' = cons S (λ s → doConflictTel (p s) e') 

doConflict :  {i j : ℕ} {Δ : Telescope i} {D : DataDesc j}{D' : Set}
        → {s t : D' → μ D} {x : ℕ} (p : Δ [ x ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
        → (e' : (d : D') → ¬ (conᵢ (s d) ≡ conᵢ (t d))) (xs : ⟦ Δ ⟧telD)
        → ⟦ doConflictTel p e' ⟧telD
doConflict {Δ = cons E Δ} {s = s} {t = t} (here d) e' (x , xs) = conflict (s d) (t d) (e' d) x 
    , subst (λ e → ⟦ Δ e ⟧telD) (sym (isLinvConflict (s d) (t d) (e' d) x)) xs 
doConflict {Δ = cons S E} (there p) e' (x , xs) = x , doConflict (p x) e' xs

linvDoConflict : {i j : ℕ} {Δ : Telescope i} {D : DataDesc j}{D' : Set}
        → {s t : D' → μ D} {x : ℕ} (p : Δ [ x ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
        → (e' : (d : D') → ¬ (conᵢ (s d) ≡ conᵢ (t d))) (xs : ⟦ doConflictTel p e' ⟧telD)
        → ⟦ Δ ⟧telD
linvDoConflict {Δ = cons E Δ} {s = s} {t = t} (here d) e' (b , xs) = linvConflict (s d) (t d) (e' d) b , xs 
linvDoConflict {Δ = cons S E} (there p) e' (x , xs) = x , linvDoConflict (p x) e' xs

isLinvDoConflict :  {i j : ℕ} {Δ : Telescope i} {D : DataDesc j}{D' : Set}
        → {s t : D' → μ D} {x : ℕ} (p : Δ [ x ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
        → (e' : (d : D') → ¬ (conᵢ (s d) ≡ conᵢ (t d))) (xs : ⟦ Δ ⟧telD)
        → linvDoConflict p e' (doConflict p e' xs) ≡ xs
isLinvDoConflict {Δ = cons E Δ} {s = s} {t = t} (here d) e' (x , xs) 
    = J (λ x' e' → (xs' : ⟦ Δ x' ⟧telD) → xs' ≡ subst (λ x' → ⟦ Δ x' ⟧telD) e' xs → (x' , xs') ≡ (x , xs)) 
            (λ xs' e' → subst (λ xs' → (x , xs') ≡ (x , xs)) (sym e') refl) 
            (sym (isLinvConflict (s d) (t d) (e' d) x)) 
            (subst (λ x → ⟦ Δ x ⟧telD) (sym (isLinvConflict (s d) (t d) (e' d) x)) xs) 
            refl
isLinvDoConflict {Δ = cons S E} (there p) e' (x , xs) = subst (λ xs' → (x , xs') ≡ (x , xs)) (sym (isLinvDoConflict (p x) e' xs)) refl   