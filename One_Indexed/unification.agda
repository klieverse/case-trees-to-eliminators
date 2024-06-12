{-# OPTIONS --safe #-}
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
  cₙ aₙ  : ℕ 
  n k   : ℕ

-- the solution rule
solution : Σ[ x ∈ A ] (t ≡ x) → ⊤
solution _ = tt

solution' : ⊤ → Σ[ x ∈ A ] (t ≡ x)
solution' {t = t} _ = t , refl

solution'∘solution : (xe : Σ[ x ∈ A ] (t ≡ x)) → solution' (solution xe) ≡ xe
solution'∘solution xe = J (λ x e → solution' (solution (x , e)) ≡ (x , e)) refl (proj₂ xe)

-- update telescope with solution rule that replaces occurences of x by t
doSolutionTel : {Δ : Telescope n} {B : A → Set}
    (p : Δ [ k ]∶Σ[ Σ[ a ∈ A ] (B a) ] (λ t → B (proj₁ t)) ∶ (λ t x → (proj₂ t) ≡ x))
    → Telescope (n + zero ∸ 2)
doSolutionTel p = updateTel₂ p (λ _ → nil) (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) 


-- symmetric solution rule
solution₁ : Σ[ x ∈ A ] (x ≡ t) → ⊤
solution₁ _ = tt

solution₁' : ⊤ → Σ[ x ∈ A ] (x ≡ t)
solution₁' {t = t} _ = t , refl

solution₁'∘solution₁ : (xe : Σ[ x ∈ A ] (x ≡ t)) → solution₁' (solution₁ xe) ≡ xe
solution₁'∘solution₁ {t = t} xe = J₁ (λ x e → (t , refl) ≡ (x , e)) refl (proj₂ xe)

-- update telescope with solution rule that replaces occurences of x by t
doSolutionTel₁ : {Δ : Telescope n} {B : A → Set}
    (p : Δ [ k ]∶Σ[ Σ[ a ∈ A ] (B a) ] (λ t → B (proj₁ t)) ∶ (λ t x → x ≡ (proj₂ t))) 
    → Telescope (n + zero ∸ 2)
doSolutionTel₁ p = updateTel₂ p (λ _ → nil) (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) 



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
doDeletionTel : {Δ : Telescope n}{B : A → Set}{f : (a : A) → B a}  
    → (p : Δ [ k ]∶Σ[ A ] (λ a → f a ≡ f a))
    → Telescope (n + zero ∸ 1)
doDeletionTel p = updateTel₁ p (λ _ → nil) (λ _ → deletion) (λ _ → deletion') (λ _ → deletion'∘deletion)


-- the conflict rule
conflict : {D : DataDesc cₙ} {x y : μ D} 
    → (f : ¬ (conᵢ x ≡ conᵢ y)) (e : x ≡ y) → Σ[ b ∈ ⊥ ] ⊤
conflict f e = ⊥-elim (f (cong conᵢ e)) , tt

conflict' : {D : DataDesc cₙ}{x y : μ D} 
    → (f : ¬ (conᵢ x ≡ conᵢ y)) → Σ[ b ∈ ⊥ ] ⊤ → x ≡ y
conflict' f (b , tt) = ⊥-elim b

conflict'∘conflict : {D : DataDesc cₙ} {x y : μ D} 
    → (f : ¬ (conᵢ x ≡ conᵢ y)) → (e : x ≡ y)
    → conflict' f (conflict f e) ≡ e
conflict'∘conflict f e = ⊥-elim (f (cong conᵢ e))

-- update the telescope by replacing s ≡ t by ⊥
doConflictTel : {Δ : Telescope n} {D : DataDesc cₙ}
        → {x y : A → μ D} (p : Δ [ k ]∶Σ[ A ] (λ a → x a ≡ y a))
        → (f : (a : A) → ¬ (conᵢ (x a) ≡ conᵢ (y a)))
        → Telescope (n + 1 ∸ 1)
doConflictTel p f = updateTel₁ p (λ _ → cons ⊥ (λ b → nil)) (λ a → conflict (f a)) 
    (λ a → conflict' (f a)) (λ a → conflict'∘conflict (f a)) 


-- injectivity rule telescope
injectivityTelC : {X : Set}{C : ConDesc aₙ} (x y : ⟦ C ⟧c X) → Telescope aₙ
injectivityTelC         {C = one'} _ _ = nil
injectivityTelC {X = X} {C = Σ' S C } (x , xs) (y , ys) = e ∈ x ≡ y , injectivityTelC (subst (λ x → ⟦ C x ⟧c X) e xs) ys
injectivityTelC         {C = ind×' C} (x , xs) (y , ys) = e ∈ x ≡ y , injectivityTelC xs ys

injectivityTel : {D : DataDesc cₙ} {x y : μ D} → conᵢ x ≡ conᵢ y → Telescope (conₙ x)
injectivityTel {D = D} {x} {y} = case-μ D (λ x → (y : μ D) → conᵢ x ≡ conᵢ y → Telescope (conₙ x)) 
        (λ x → case-μ D (λ y → proj₁ x ≡ conᵢ y → Telescope (proj₁ (D (proj₁ x)))) 
            (λ y e → injectivityTelC (proj₂ x) (subst (λ x → ⟦ proj₂ (D x) ⟧c (μ D)) (sym e) (proj₂ y)))) x y


-- injectivity rule
injectivityC : {X : Set}{C : ConDesc aₙ} → (x : ⟦ C ⟧c X) → ⟦ injectivityTelC x x ⟧telD
injectivityC {C = one'} x = tt
injectivityC {C = Σ' S D } (x , xs) = refl , injectivityC xs
injectivityC {C = ind×' C} (x , xs) = refl , injectivityC xs

injectivity : {D : DataDesc aₙ} {x y : μ D} (f : conᵢ x ≡ conᵢ y) (e : x ≡ y) 
    → ⟦ injectivityTel {x = x} {y = y} f ⟧telD
injectivity {D = D} {x} f e = J (λ y e → (f : conᵢ x ≡ conᵢ y) → ⟦ injectivityTel {x = x} {y = y} f ⟧telD) 
    (λ f → K (λ f → ⟦ injectivityTel {x = x} f ⟧telD) 
        (case-μ D (λ x → ⟦ injectivityTel {x = x} {y = x} refl ⟧telD) (λ x → injectivityC (proj₂ x)) 
    x) f) e f

-- left inverse injectivity
injectivityC' : {X : Set}{C : ConDesc aₙ}
    → (x y : ⟦ C ⟧c X) → ⟦ injectivityTelC x y ⟧telD → x ≡ y
injectivityC' {C = one'} x y e = refl 
injectivityC' {X = X} {C = Σ' S D'} (x , xs) (y , ys) (e , es) 
    = Σ-create e (injectivityC' (subst (λ s → ⟦ D' s ⟧c X) e xs) ys es) 
injectivityC' {C = ind×' C} (x , xs) (y , ys) (e , es) 
    = ×-create e (injectivityC' xs ys es)

injectivity' : {D : DataDesc cₙ} {x y : μ D}
    → (f : conᵢ x ≡ conᵢ y) → ⟦ injectivityTel {x = x} {y = y} f ⟧telD → x ≡ y
injectivity' {D = D} {x} {y}
    = case-μ D (λ x → (y : μ D) → (f : conᵢ x ≡ conᵢ y) → ⟦ injectivityTel {x = x} {y = y} f ⟧telD → x ≡ y) 
        (λ x → case-μ D (λ y → (f : proj₁ x ≡ conᵢ y) → ⟦ injectivityTel {x = ⟨ x ⟩} {y = y} f ⟧telD → ⟨ x ⟩ ≡ y) 
            (λ y f → J (λ n₂ e → (y : ⟦ proj₂ (D n₂) ⟧c (μ D)) → ⟦ injectivityTel {x = ⟨ x ⟩} {y = ⟨ n₂ , y ⟩} e ⟧telD → ⟨ x ⟩ ≡ ⟨ n₂ , y ⟩) 
                (λ y xs → cong (λ xs → ⟨ proj₁ x , xs ⟩) (injectivityC' (proj₂ x) y xs)) f (proj₂ y))) x y

-- proof of left inverse injectivity
injectivityC'∘injectivityC : {X : Set}{C : ConDesc aₙ} (x : ⟦ C ⟧c X)
    → injectivityC' x x (injectivityC x) ≡ refl
injectivityC'∘injectivityC {C = one'} x = refl
injectivityC'∘injectivityC {X = X} {C = Σ' S E} (x , xs) 
    = subst (λ e → Σ-create (refl {x = x}) e ≡ refl) (sym (injectivityC'∘injectivityC xs)) refl 
injectivityC'∘injectivityC {C = ind×' C'} (x , xs) 
    = subst (λ e → ×-create refl e ≡ refl) (sym (injectivityC'∘injectivityC xs)) refl 
    

injectivity'∘injectivity : {D : DataDesc cₙ} {x y : μ D} (f : conᵢ x ≡ conᵢ y)
    → (e : x ≡ y) → injectivity' f (injectivity f e) ≡ e
injectivity'∘injectivity {D = D} {x} {y} f e = J (λ y e → (f : conᵢ x ≡ conᵢ y) → injectivity' f (injectivity f e) ≡ e) 
    (λ f → K (λ f → injectivity' f (injectivity {x = x} f refl) ≡ refl) 
        (case-μ D (λ x → injectivity' {x = x} refl (injectivity {x = x} refl refl) ≡ refl) 
            (λ x → cong (cong (λ xs → ⟨ proj₁ x , xs ⟩)) (injectivityC'∘injectivityC (proj₂ x))) x) f) e f


-- update the telescope by replacing s ≡ t by equivalences of all the constructor arguments
doInjectivityTel : {Δ : Telescope n}{D : DataDesc cₙ}
  → {x y : A → μ D}(f : (a : A) → conᵢ (x a) ≡ conᵢ (y a)) 
  → {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
  → (p : Δ [ k ]∶Σ[ A ] (λ a → x a ≡ y a))
  → Telescope (n + aₙ' ∸ 1)
doInjectivityTel {x = x} {y = y} f eℕ p = updateTel₁ p (λ a → subst Telescope (eℕ a) (injectivityTel {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (injectivity {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a)  e)) 
    (λ a e → subst (λ e' → injectivity' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity'∘injectivity {x = x a} {y = y a} (f a) e))

doInjectivity : {Δ : Telescope n}{D : DataDesc cₙ}
  → {x y : A → μ D}(f : (a : A) → conᵢ (x a) ≡ conᵢ (y a)) 
  → {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
  → (p : Δ [ k ]∶Σ[ A ] (λ a → x a ≡ y a))
  → (xs : ⟦ Δ ⟧telD)
  → ⟦ doInjectivityTel f eℕ p ⟧telD
doInjectivity {x = x} {y = y} f eℕ p xs = update₁ p (λ a → subst Telescope (eℕ a) (injectivityTel {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (injectivity {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a)  e)) 
    (λ a e → subst (λ e' → injectivity' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity'∘injectivity {x = x a} {y = y a} (f a) e)) xs

doInjectivity' : {Δ : Telescope n}{D : DataDesc cₙ}
  → {x y : A → μ D}(f : (a : A) → conᵢ (x a) ≡ conᵢ (y a)) 
  → {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
  → (p : Δ [ k ]∶Σ[ A ] (λ a → x a ≡ y a))
  → ⟦ doInjectivityTel f eℕ p ⟧telD
  → ⟦ Δ ⟧telD
doInjectivity' {x = x} {y = y} f eℕ p xs = update₁' p (λ a → subst Telescope (eℕ a) (injectivityTel {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (injectivity {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a)  e)) 
    (λ a e → subst (λ e' → injectivity' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity'∘injectivity {x = x a} {y = y a} (f a) e)) xs

doInjectivity'∘doInjectivity : {Δ : Telescope n}{D : DataDesc cₙ}
  → {x y : A → μ D}(f : (a : A) → conᵢ (x a) ≡ conᵢ (y a)) 
  → {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
  → (p : Δ [ k ]∶Σ[ A ] (λ a → x a ≡ y a))
  → (xs : ⟦ Δ ⟧telD)
  → doInjectivity' f eℕ p (doInjectivity f eℕ p xs) ≡ xs
doInjectivity'∘doInjectivity {x = x} {y = y} f eℕ p xs = update₁'∘update₁ p (λ a → subst Telescope (eℕ a) (injectivityTel {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (injectivity {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a)  e)) 
    (λ a e → subst (λ e' → injectivity' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity'∘injectivity {x = x a} {y = y a} (f a) e)) xs