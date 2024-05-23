{-# OPTIONS --allow-unsolved-metas #-}
module One_Indexed.unification where

open import lib
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
  n m k : ℕ

-- the solution rule
solution : Σ[ x ∈ A ] (t ≡ x) → ⊤
solution _ = tt

solution' : ⊤ → Σ[ x ∈ A ] (t ≡ x)
solution' {t = t} _ = t , refl

solution'∘solution : (xe : Σ[ x ∈ A ] (t ≡ x)) → solution' (solution xe) ≡ xe
solution'∘solution {t = t} xe = J (λ x e → (t , refl) ≡ (x , e)) refl (proj₂ xe)

-- update telescope with solution rule that replaces occurences of x by t
doSolutionTel : {Δ : Telescope n} {X : Set} {A : X → Set}
    (p : Δ [ k ]∶Σ[ Σ[ x ∈ X ] (A x) ] (λ xa → A (proj₁ xa)) ∶ (λ t x → (proj₂ t) ≡ x))
    → Telescope (n + zero ∸ 2)
doSolutionTel p = updateTel₂ p nil (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) 


-- symmetric solution rule
solution₁ : Σ[ x ∈ A ] (x ≡ t) → ⊤
solution₁ _ = tt

solution₁' : ⊤ → Σ[ x ∈ A ] (x ≡ t)
solution₁' {t = t} _ = t , refl

solution₁'∘solution₁ : (xe : Σ[ x ∈ A ] (x ≡ t)) → solution₁' (solution₁ xe) ≡ xe
solution₁'∘solution₁ {t = t} xe = J₁ (λ x e → (t , refl) ≡ (x , e)) refl (proj₂ xe)

-- update telescope with solution rule that replaces occurences of x by t
doSolutionTel₁ : {Δ : Telescope n} {X : Set} {A : X → Set}
    (p : Δ [ k ]∶Σ[ Σ[ x ∈ X ] (A x) ] (λ xa → A (proj₁ xa)) ∶ (λ t x → x ≡ (proj₂ t))) 
    → Telescope (n + zero ∸ 2)
doSolutionTel₁ p = updateTel₂ p nil (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) 



K : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : x ≡ x → Set ℓ') → (p : P refl) → (e : x ≡ x) → P e
K P p refl = p

-- the deletion rule
deletion : (e : t ≡ t) → ⊤ 
deletion e = K (λ e → ⊤) tt e

deletion' : ⊤ → t ≡ t 
deletion' _ = refl

deletion'∘deletion : (e : t ≡ t) → deletion' (deletion e) ≡ e 
deletion'∘deletion e = K (λ e → deletion' (deletion e) ≡ e) refl e

-- update the telescope by removing t ≡ t and replacing occurences by refl
doDeletionTel : {Δ : Telescope n} {D : Set} {X : D → Set} 
    → {t : (d : D) → X d}  (p : Δ [ k ]∶Σ[ D ] (λ d → t d ≡ t d))
    → Telescope (n + zero ∸ 1)
doDeletionTel p = updateTel₁ p nil (λ _ → deletion) (λ _ → deletion') (λ _ → deletion'∘deletion)


-- the conflict rule
conflict : {D : DataDesc n} (s t : μ D)
    → (f : ¬ (conᵢ s ≡ conᵢ t))
    → (e : s ≡ t)
    → Σ[ b ∈ ⊥ ] ⊤
conflict s t f e = ⊥-elim (f (cong conᵢ e)) , tt

conflict' : {D : DataDesc n} (s t : μ D)
    → (f : ¬ (conᵢ s ≡ conᵢ t))
    → Σ[ b ∈ ⊥ ] ⊤
    → s ≡ t
conflict' s t f (b , tt) = ⊥-elim b

conflict'∘conflict : {D : DataDesc n} (s t : μ D)
    → (e' : ¬ (conᵢ s ≡ conᵢ t))
    → (e : s ≡ t)
    → conflict' s t e' (conflict s t e' e) ≡ e
conflict'∘conflict s t f e = ⊥-elim (f (cong conᵢ e))

-- update the telescope by replacing s ≡ t by ⊥
doConflictTel : {Δ : Telescope n} {D : DataDesc m}{D' : Set}
        → {s t : D' → μ D} (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
        → (e' : (d : D') → ¬ (conᵢ (s d) ≡ conᵢ (t d)))
        → Telescope (n + 1 ∸ 1)
doConflictTel {s = s} {t = t} p e' = updateTel₁ p (cons ⊥ (λ b → nil)) (λ d' → conflict (s d') (t d') (e' d')) 
    (λ d' → conflict' (s d') (t d') (e' d')) (λ d' → conflict'∘conflict (s d') (t d') (e' d')) 


-- injectivity rule
injectivityTelC : {D : DataDesc n}{C : ConDesc m} (x₁ x₂ : ⟦ C ⟧c (μ D)) → Telescope m
injectivityTelC {C = one'} _ _ = nil
injectivityTelC {D = D} {C = Σ' S C} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , injectivityTelC (subst (λ x → ⟦ C x ⟧c (μ D)) e xs₁) xs₂
injectivityTelC {C = ind×' C} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , injectivityTelC xs₁ xs₂

injectivityTel : {D : DataDesc n} (x₁ x₂ : μ D) → conᵢ x₁ ≡ conᵢ x₂ → Σ ℕ Telescope
injectivityTel {D = D} = case-μ D (λ x₁ → (x₂ : μ D) → conᵢ x₁ ≡ conᵢ x₂ → Σ ℕ Telescope) 
        (λ x₁ → case-μ D (λ x₂ → proj₁ x₁ ≡ conᵢ x₂ → Σ ℕ Telescope) 
            (λ x₂ e → proj₁ (D (proj₁ x₁)) , injectivityTelC (proj₂ x₁) (subst (λ x → ⟦ proj₂ (D x) ⟧c (μ D)) (sym e) (proj₂ x₂))))

injectivityC : {D : DataDesc n}{C : ConDesc m} → (c : ⟦ C ⟧c (μ D)) → ⟦ injectivityTelC c c ⟧telD
injectivityC {C = one'} c = tt
injectivityC {C = Σ' S D} (c , cs) = refl , injectivityC cs
injectivityC {D = D} {C = ind×' C} (c , cs) = refl , injectivityC cs

injectivity : {D : DataDesc n} (x₁ x₂ : μ D) (f : conᵢ x₁ ≡ conᵢ x₂) (e : x₁ ≡ x₂) 
    → ⟦ proj₂ (injectivityTel x₁ x₂ f) ⟧telD
injectivity {D = D} x₁ x₂ f e = J (λ x₂ e → (f : conᵢ x₁ ≡ conᵢ x₂) → ⟦ proj₂ (injectivityTel x₁ x₂ f) ⟧telD) 
    (λ f → K (λ f → ⟦ proj₂ (injectivityTel x₁ x₁ f) ⟧telD) 
        (case-μ D (λ x₁ → ⟦ proj₂ (injectivityTel x₁ x₁ refl) ⟧telD) (λ x₁ → injectivityC (proj₂ x₁)) 
    x₁) f) e f

-- left inverse injectivity
injectivityC' : {D : DataDesc n}{C : ConDesc m}
    → (x₁ x₂ : ⟦ C ⟧c (μ D)) → ⟦ injectivityTelC x₁ x₂ ⟧telD → x₁ ≡ x₂
injectivityC' {C = one'} x₁ x₂ e = refl 
injectivityC' {D = D} {C = Σ' S D'} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    = J (λ x₂ e → (xs₂ : ⟦ D' x₂ ⟧c (μ D)) → subst (λ x → ⟦ D' x ⟧c (μ D)) e xs₁ ≡ xs₂ → (x₁ , xs₁) ≡ (x₂ , xs₂)) 
        (λ xs₂ e₂ → subst (λ x → (x₁ , xs₁) ≡ (x₁ , x)) e₂ refl)
        e xs₂ (injectivityC' (subst (λ s → ⟦ D' s ⟧c (μ D)) e xs₁) xs₂ es)
injectivityC' {D = D} {C = ind×' C} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    = subst (λ xs₂ → (x₁ , xs₁) ≡ (x₂ , xs₂)) (injectivityC' xs₁ xs₂ es) 
        (subst (λ x₂ → (x₁ , xs₁) ≡ (x₂ , xs₁)) e refl)

injectivity' : {D : DataDesc n} (x₁ x₂ : μ D)
    → (f : conᵢ x₁ ≡ conᵢ x₂) → ⟦ proj₂ (injectivityTel x₁ x₂ f) ⟧telD → x₁ ≡ x₂
injectivity' {D = D} 
    = case-μ D (λ x₁ → (x₂ : μ D) → (f : conᵢ x₁ ≡ conᵢ x₂) → ⟦ proj₂ (injectivityTel x₁ x₂ f) ⟧telD → x₁ ≡ x₂) 
        (λ x₁ → case-μ D (λ x₂ → (f : proj₁ x₁ ≡ conᵢ x₂) → ⟦ proj₂ (injectivityTel ⟨ x₁ ⟩ x₂ f) ⟧telD → ⟨ x₁ ⟩ ≡ x₂) 
            (λ x₂ f → J (λ n₂ e → (x₂ : ⟦ proj₂ (D n₂) ⟧c (μ D)) → ⟦ proj₂ (injectivityTel ⟨ x₁ ⟩ ⟨ n₂ , x₂ ⟩ e) ⟧telD → ⟨ x₁ ⟩ ≡ ⟨ n₂ , x₂ ⟩) 
                (λ x₂ xs → cong (λ x → ⟨ proj₁ x₁ , x ⟩) (injectivityC' (proj₂ x₁) x₂ xs)) f (proj₂ x₂)))

-- proof of left inverse injectivity
injectivityC'∘injectivityC : {D : DataDesc n}{C : ConDesc m} (x : ⟦ C ⟧c (μ D))
    → injectivityC' x x (injectivityC x) ≡ refl
injectivityC'∘injectivityC {C = one'} x = refl
injectivityC'∘injectivityC {D = D} {C = Σ' S E} (s , x) = subst (λ e → subst (λ x₁ → (s , x) ≡ (s , x₁)) e refl ≡ refl) (sym (injectivityC'∘injectivityC x)) refl
injectivityC'∘injectivityC {D = D}{C = ind×' C'} (u , x) = subst (λ e → subst (λ xs → (u , x) ≡ (u , xs)) e refl
      ≡ refl) (sym (injectivityC'∘injectivityC x)) refl 

injectivity'∘injectivity : {D : DataDesc n} → (x₁ x₂ : μ D) → (f : conᵢ x₁ ≡ conᵢ x₂)
    → (e : x₁ ≡ x₂) → injectivity' x₁ x₂ f (injectivity x₁ x₂ f e) ≡ e
injectivity'∘injectivity {D = D} x₁ x₂ f e = J (λ x₂ e → (f : conᵢ x₁ ≡ conᵢ x₂) → injectivity' x₁ x₂ f (injectivity x₁ x₂ f e) ≡ e) 
    (λ f → K (λ f → injectivity' x₁ x₁ f (injectivity x₁ x₁ f refl) ≡ refl) 
        (case-μ D (λ x₁ → injectivity' x₁ x₁ refl (injectivity x₁ x₁ refl refl) ≡ refl) 
            (λ x₁ → cong (cong (λ x → ⟨ proj₁ x₁ , x ⟩)) (injectivityC'∘injectivityC (proj₂ x₁))) x₁) f) e f


-- update the telescope by replacing s ≡ t by equivalences of all the constructor arguments
doInjectivityTelLength : {D : DataDesc n} → (s t : μ D) 
    → (f : conᵢ s ≡ conᵢ t)
    → proj₁ (injectivityTel s t f) ≡ conₙ s 
doInjectivityTelLength {D = D} = case-μ D (λ s → (t : μ D) → (f : (conᵢ s ≡ conᵢ t)) → proj₁ (injectivityTel s t f) ≡ conₙ s) 
            (λ s → case-μ D (λ t → (f : (conᵢ ⟨ s ⟩ ≡ conᵢ t)) → proj₁ (injectivityTel ⟨ s ⟩ t f) ≡ conₙ ⟨ s ⟩) 
            (λ t f → refl))   

doinjectivityTel : {D' : Set}{j : ℕ}{D : DataDesc m} {Δ : Telescope n}
  → {s t : D' → μ D}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
  → Telescope (k + j + (n ∸ suc k))
doinjectivityTel {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) = subst (λ j → Telescope (j + i)) (trans (doInjectivityTelLength (s d) (t d) (e' d)) (eℕ d)) 
    (mergeTel (proj₂ (injectivityTel (s d) (t d) (e' d))) E (injectivity' (s d) (t d) (e' d))) 
doinjectivityTel {Δ = cons S E} {s} {t} e' eℕ (there x) = cons S (λ s → doinjectivityTel e' eℕ (x s))

doInjectivity : {D' : Set}{j : ℕ}{D : DataDesc m}{Δ : Telescope n}
  → {s t : D' → μ D}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d'))) (xs : ⟦ Δ ⟧telD)
  → ⟦ doinjectivityTel e' eℕ p ⟧telD
doInjectivity {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) (e , xs) = J 
    (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (injectivityTel (s d) (t d) (e' d))) E (injectivity' (s d) (t d) (e' d))) ⟧telD) 
    (merge (injectivity (s d) (t d) (e' d) e) (subst (λ e → ⟦ E e ⟧telD) (sym (injectivity'∘injectivity (s d) (t d) (e' d) e)) xs)) 
    (trans (doInjectivityTelLength (s d) (t d) (e' d)) (eℕ d))
doInjectivity {Δ = cons S E} {s} {t} e' eℕ (there p) (x , xs) = x , doInjectivity e' eℕ (p x) xs 

doInjectivity' : {D' : Set}{j : ℕ}{D : DataDesc m}{Δ : Telescope n}
  → {s t : D' → μ D}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d'))) (xs : ⟦ doinjectivityTel e' eℕ p ⟧telD)
  → ⟦ Δ ⟧telD
doInjectivity' {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) xs = (injectivity' (s d) (t d) (e' d) (mproj₁ xs')) 
    , mproj₂ {X = (proj₂ (injectivityTel (s d) (t d) (e' d)))} {Y = E} xs'  where 
    
    xs' : ⟦ mergeTel (proj₂ (injectivityTel (s d) (t d) (e' d))) E (injectivity' (s d) (t d) (e' d)) ⟧telD
    xs' = J' (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (injectivityTel (s d) (t d) (e' d))) E (injectivity' (s d) (t d) (e' d))) ⟧telD) 
            (trans (doInjectivityTelLength (s d) (t d) (e' d)) (eℕ d)) xs
    
doInjectivity' {Δ = cons S E} {s} {t} e' eℕ (there p) (x , xs) = x , doInjectivity' e' eℕ (p x) xs 

doInjectivity'∘doInjectivity : {D' : Set}{j : ℕ}{D : DataDesc m}{Δ : Telescope n}
  → {s t : D' → μ D}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d'))) (xs : ⟦ Δ ⟧telD)
  → doInjectivity' e' eℕ p (doInjectivity e' eℕ p xs) ≡ xs
doInjectivity'∘doInjectivity {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) (e , xs) = goal where

    xs' : ⟦ mergeTel (proj₂ (injectivityTel (s d) (t d) (e' d))) E (injectivity' (s d) (t d) (e' d)) ⟧telD 
    xs' = J' (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (injectivityTel (s d) (t d) (e' d))) E (injectivity' (s d) (t d) (e' d))) ⟧telD) 
            (trans (doInjectivityTelLength (s d) (t d) (e' d)) (eℕ d)) 
                (J (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (injectivityTel (s d) (t d) (e' d))) E (injectivity' (s d) (t d) (e' d))) ⟧telD) 
                (merge (injectivity (s d) (t d) (e' d) e) (subst (λ e → ⟦ E e ⟧telD) (sym (injectivity'∘injectivity (s d) (t d) (e' d) e)) xs)) 
                (trans (doInjectivityTelLength (s d) (t d) (e' d)) (eℕ d)))

    goal : (injectivity' (s d) (t d) (e' d) (mproj₁ xs'),
       mproj₂ {X = (proj₂ (injectivityTel (s d) (t d) (e' d)))} {Y = E} xs')
      ≡ (e , xs)
    goal = subst (λ xs' → (injectivity' (s d) (t d) (e' d) (mproj₁ xs') ,  mproj₂ {X = (proj₂ (injectivityTel (s d) (t d) (e' d)))} {Y = E} xs') ≡ (e , xs)) 
            (sym (J'∘J ((λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (injectivityTel (s d) (t d) (e' d))) E (injectivity' (s d) (t d) (e' d))) ⟧telD)) 
            (merge (injectivity (s d) (t d) (e' d) e) (subst (λ e → ⟦ E e ⟧telD) (sym (injectivity'∘injectivity (s d) (t d) (e' d) e)) xs)) 
            (trans (doInjectivityTelLength (s d) (t d) (e' d)) (eℕ d)))) 
            (subst (λ axs → (injectivity' (s d) (t d) (e' d) (proj₁ axs) , proj₂ axs) ≡ (e , xs)) (mproj∘merge (injectivity (s d) (t d) (e' d) e) (subst (λ e₁ → ⟦ E e₁ ⟧telD)
            (sym (injectivity'∘injectivity (s d) (t d) (e' d) e)) xs)) 
            (J (λ x' e' → (x' , subst (λ e → ⟦ E e ⟧telD) e' xs) ≡ (e , xs)) refl  (sym (injectivity'∘injectivity (s d) (t d) (e' d) e)))) 
       
doInjectivity'∘doInjectivity {Δ = cons S E} {s} {t} e' eℕ (there p) (x , xs) = subst (λ xs' → (x , xs') ≡ (x , xs)) (sym (doInjectivity'∘doInjectivity e' eℕ (p x) xs)) refl 