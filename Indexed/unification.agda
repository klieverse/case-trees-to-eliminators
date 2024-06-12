{-# OPTIONS --safe #-}
module Indexed.unification where

open import Indexed.datatypes
open import Non_Indexed.telescope 
open import lib

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Data.Sum
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.String
open import Data.Empty
open import Agda.Builtin.Equality
open import Data.Fin using (Fin; fromℕ<; fromℕ; toℕ; raise; _≟_ ) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

private variable
  A       : Set
  t       : A
  cₙ aₙ iₙ : ℕ 
  is      : Telescope iₙ
  n k     : ℕ

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
conflict : {D : DataDesc is cₙ}{d₁ d₂ : ⟦ is ⟧telD} 
    → {x : μ D d₁}{y : μ D d₂} (f : ¬ (conᵢ x ≡ conᵢ y))
    → Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e x ≡ y)
    → Σ[ b ∈ ⊥ ] ⊤
conflict f (ed , ex) = ⊥-elim (f (cong (λ x → conᵢ (proj₂ x)) (Σ-create ed ex))) , tt

conflict' :{D : DataDesc is cₙ}{d₁ d₂ : ⟦ is ⟧telD} 
    → {x : μ D d₁}{y : μ D d₂} (f : ¬ (conᵢ x ≡ conᵢ y))
    → Σ[ b ∈ ⊥ ] ⊤
    → Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e x ≡ y)
conflict' f (b , tt) = ⊥-elim b

conflict'∘conflict : {D : DataDesc is cₙ}{d₁ d₂ : ⟦ is ⟧telD} 
    → {x : μ D d₁}{y : μ D d₂} (f : ¬ (conᵢ x ≡ conᵢ y))
    → (e : Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e x ≡ y))
    → conflict' f (conflict f e) ≡ e
conflict'∘conflict f (ed , ex) = ⊥-elim (f (cong (λ x → conᵢ (proj₂ x)) (Σ-create ed ex)))

-- update the telescope by replacing (d₁ ≡ d₂)(x ≡ y) by ⊥
doConflictTel : {Δ : Telescope n} {D : DataDesc is cₙ}
    → {d₁ : A → ⟦ is ⟧telD} {d₂ : A → ⟦ is ⟧telD} 
    → {x : (a : A) → μ D (d₁ a)} {y : (a : A) → μ D (d₂ a)}
    → (p : Δ [ k ]∶Σ[ A ] (λ a → d₁ a ≡ d₂ a ) ∶ (λ a e → subst (μ D) e (x a) ≡ y a))
    → (f : (a : A) → ¬ (conᵢ (x a) ≡ conᵢ (y a)))
    → Telescope (n + 1 ∸ 2)
doConflictTel p f = updateTel₂ p (λ _ → cons ⊥ (λ b → nil)) (λ a → conflict (f a)) 
    (λ a → conflict' (f a)) (λ a → conflict'∘conflict (f a))


-- injectivity rule telescope
injectivityTelC : {X : ⟦ is ⟧telD → Set}{C : ConDesc is aₙ} {d₁ d₂ : ⟦ is ⟧telD} 
  → ⟦ C ⟧c X d₁ → ⟦ C ⟧c X d₂ → Telescope aₙ
injectivityTelC {C = one' x} {d₁} {d₂} x₁ x₂ = nil
injectivityTelC {X = X} {C = Σ' S C} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , injectivityTelC (subst (λ x → ⟦ C x ⟧c X d₁) e xs₁) xs₂
injectivityTelC {C = ×' x C} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , injectivityTelC xs₁ xs₂

injectivityTel : {D : DataDesc is cₙ} {d₁ d₂ : ⟦ is ⟧telD}
        → {x : μ D d₁} {y : μ D d₂} → (conᵢ x ≡ conᵢ y) → Telescope (conₙ x)
injectivityTel {D = D} {d₁} {d₂} {x} {y} e = case-μ D (λ d₁ x → (y : μ D d₂) → (conᵢ x ≡ conᵢ y) → Telescope (conₙ x)) 
    (λ d₁ x y e → case-μ D (λ d₂ y → (proj₁ x ≡ conᵢ y) → Telescope (proj₁ (D (proj₁ x)))) 
        (λ d₂ y e → injectivityTelC (proj₂ x) (subst (λ x → ⟦ proj₂ (D x) ⟧c (μ D) d₂) (sym e) (proj₂ y))) d₂ y e) 
    d₁ x y e

-- injectivity rule
injectivityC : {X : ⟦ is ⟧telD → Set}{C : ConDesc is aₙ} {d : ⟦ is ⟧telD} 
    → (x : ⟦ C ⟧c X d) → ⟦ injectivityTelC x x ⟧telD
injectivityC {C = one' v} x = tt
injectivityC {C = Σ' S D'} (x , xs) = refl , injectivityC xs 
injectivityC {C = ×' d' C} (x , xs) = refl , injectivityC xs

injectivity : {D : DataDesc is cₙ}{d₁ d₂ : ⟦ is ⟧telD} {x : μ D d₁} {y : μ D d₂}
    → (f : conᵢ x ≡ conᵢ y) (e : Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e x ≡ y)) 
    → ⟦ injectivityTel {x = x} {y = y} f ⟧telD
injectivity {D = D} {d₁} {d₂} {x} {y} f (ed , ex) = J (λ dy e → (f : conᵢ x ≡ conᵢ (proj₂ dy)) → ⟦ injectivityTel {x = x} {y = proj₂ dy} f ⟧telD) 
        (λ f → K (λ f → ⟦ injectivityTel {x = x} {y = x} f ⟧telD) 
            (case-μ D (λ d₁ x → ⟦ injectivityTel {x = x} {y = x} refl ⟧telD) (λ d₁ e → injectivityC (proj₂ e)) 
        d₁ x) f) (Σ-create ed ex) f


injectivityWithoutK : {D : DataDesc is cₙ}{d₁ d₂ : ⟦ is ⟧telD} {x : μ D d₁} {y : μ D d₂}
    → (e : Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e x ≡ y)) → ⟦ injectivityTel {x = x} {y = y} (cong (λ dx → conᵢ (proj₂ dx)) (Σ-create (proj₁ e) (proj₂ e))) ⟧telD
injectivityWithoutK {D = D} {d₁} {d₂} {x} {y} (ed , ex) = J (λ dy e → ⟦ injectivityTel {x = x} {y = proj₂ dy} (cong (λ dx → conᵢ (proj₂ dx)) e) ⟧telD) 
    (case-μ D (λ d₁ x → ⟦ injectivityTel {x = x} {y = x} refl ⟧telD) (λ d₁ x → injectivityC (proj₂ x)) d₁ x) (Σ-create ed ex) 


-- left inverse injectivity
injectivityC' : {X : ⟦ is ⟧telD → Set}{C : ConDesc is aₙ}{d₁ d₂ : ⟦ is ⟧telD}
    → (x₁ : ⟦ C ⟧c X d₁) → (x₂ : ⟦ C ⟧c X d₂) → ⟦ injectivityTelC x₁ x₂ ⟧telD
    → (d₁ , x₁) ≡ (d₂ , x₂)
injectivityC' {C = one' v} {d₁} {d₂} x₁ x₂ tt 
    = J₁ (λ v e → (x₂ : v ≡ d₂) → (d₁ , e) ≡ (d₂ , x₂)) (J (λ d₂ e → (d₁ , refl) ≡ (d₂ , e)) refl) x₁ x₂ 
injectivityC' {X = X} {C = Σ' S D'} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    =  ΣΣ-create (linvΣ₁' e (injectivityC' (subst (λ x → ⟦ D' x ⟧c X d₁) e xs₁) xs₂ es)) 
        e (linvΣ₂' e (injectivityC' (subst (λ x → ⟦ D' x ⟧c X d₁) e xs₁) xs₂ es)) 
injectivityC' {C = ×' d C} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    = Σ×-create (linvΣ₁ (injectivityC' xs₁ xs₂ es)) e (linvΣ₂ (injectivityC' xs₁ xs₂ es)) 

injectivity' : {D : DataDesc is cₙ}{d₁ d₂ : ⟦ is ⟧telD} {x : μ D d₁} {y : μ D d₂}
    → (f : conᵢ x ≡ conᵢ y)
    → ⟦ injectivityTel {x = x} {y = y} f ⟧telD
    → Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e x ≡ y)
injectivity' {D = D} {d₁} {d₂} {x} {y} f xs = case-μ D (λ d₁ x → (y : μ D d₂) → (f : conᵢ x ≡ conᵢ y) 
    → ⟦ injectivityTel {x = x} {y = y} f ⟧telD → Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e x ≡ y)) 
    (λ d₁ x y f xs → case-μ D (λ d₂ y → (f : proj₁ x ≡ conᵢ y) → ⟦ injectivityTel {x = ⟨ x ⟩} {y = y} f ⟧telD 
        → Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e ⟨ x ⟩ ≡ y)) 
            (λ d₂ y f xs → J (λ n₂ f → (y : ⟦ proj₂ (D n₂) ⟧c (μ D) d₂) → ⟦ injectivityTel {x = ⟨ x ⟩} {y = ⟨ n₂ , y ⟩} f ⟧telD  
                → Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e ⟨ proj₁ x , proj₂ x ⟩ ≡ ⟨ n₂ , y ⟩)) 
                    (λ y xs → (linvΣ₁ (cong (λ where (d , y) → (d , ⟨ proj₁ x , y ⟩))(injectivityC' (proj₂ x) y xs)) , 
                        linvΣ₂ (cong (λ where (d , y) → (d , ⟨ proj₁ x , y ⟩))(injectivityC' (proj₂ x) y xs)))) 
                f (proj₂ y) xs) 
    d₂ y f xs) d₁ x y f xs


-- proof of left inverse injectivity
injectivityC'∘injectivityC : {X : ⟦ is ⟧telD → Set}{C : ConDesc is aₙ}{d : ⟦ is ⟧telD}
    → (x : ⟦ C ⟧c X d) → injectivityC' x x (injectivityC x) ≡ refl
injectivityC'∘injectivityC {C = one' v} {d} x = J (λ d x → J₁ (λ v₁ e → (x₂ : v₁ ≡ d) → (d , e) ≡ (d , x₂)) (J (λ d₂ e → (d , refl {x = d}) ≡ (d₂ , e)) refl) x x ≡ refl) refl x --  refl
injectivityC'∘injectivityC {X = X} {C = Σ' S E} {d} (s , x) = subst (λ e → ΣΣ-create (linvΣ₁' {C = λ d s → ⟦ E s ⟧c X d} refl e) refl
      (linvΣ₂' refl e) ≡ refl) (sym (injectivityC'∘injectivityC x)) refl
injectivityC'∘injectivityC {C = ×' d' C'} {d} (u , x) =  subst (λ e → Σ×-create (linvΣ₁ e) refl
      (linvΣ₂ e) ≡ refl) (sym (injectivityC'∘injectivityC x)) refl

injectivity'∘injectivity : {D : DataDesc is cₙ}{d₁ d₂ : ⟦ is ⟧telD} {x : μ D d₁} {y : μ D d₂}
    → (f : conᵢ x ≡ conᵢ y) (e : Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e x ≡ y)) 
    → injectivity' f (injectivity f e) ≡ e
injectivity'∘injectivity {is = is} {D = D} {d₁} {d₂} {x} {y} f (ed , ex) = J (λ d₂ ed → (y : μ D d₂) (f : conᵢ x ≡ conᵢ y)(ex : subst (μ D) ed x ≡ y) → injectivity' f (injectivity f (ed , ex)) ≡ (ed , ex)) 
    (λ y f ex → J (λ y ex → (f : conᵢ x ≡ conᵢ y) → injectivity' f (injectivity f (refl , ex)) ≡ (refl , ex)) 
        (λ f → K (λ f → injectivity' f (injectivity {x = x} f (refl , refl)) ≡ (refl , refl))
        (case-μ D (λ d₁ x → injectivity' {x = x} refl (injectivity {x = x} refl (refl , refl)) ≡ (refl , refl)) 
            (λ d₁ x → subst (λ xs → (_,_ {B = λ e → subst (μ D) e ⟨ x ⟩ ≡ ⟨ x ⟩} (linvΣ₁ (cong (λ { (d , y) → d , ⟨ proj₁ x , y ⟩ }) xs)) 
             (linvΣ₂ (cong (λ { (d , y) → d , ⟨ proj₁ x , y ⟩ }) xs))) 
            ≡ (refl , refl)) (sym (injectivityC'∘injectivityC (proj₂ x))) refl)
            d₁ x) f) 
        ex f)
    ed y f ex 
    

injectivity'∘injectivityWithoutK : {D : DataDesc is cₙ}{d₁ d₂ : ⟦ is ⟧telD} {x : μ D d₁} {y : μ D d₂}
    → (e : Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e x ≡ y)) → injectivity' (cong (λ dx → conᵢ (proj₂ dx)) (Σ-create (proj₁ e) (proj₂ e))) (injectivityWithoutK e) ≡ e
injectivity'∘injectivityWithoutK {is = is} {D = D} {d₁} {d₂} {x} {y} (ed , ex) = J (λ d₂ ed → (y : μ D d₂) (ex : subst (μ D) ed x ≡ y) → injectivity' (cong (λ dx → conᵢ (proj₂ dx)) (Σ-create ed ex)) (injectivityWithoutK (ed , ex)) ≡ (ed , ex)) 
    (λ y ex → J (λ y ex → injectivity' (cong (λ dx → conᵢ {D = D} {d = proj₁ dx} (proj₂ dx)) (Σ-create (refl {x = d₁}) ex)) (injectivityWithoutK (refl , ex)) ≡ (refl , ex)) 
        (case-μ D (λ d₁ x → injectivity' {x = x} refl (injectivityWithoutK {x = x} (refl , refl)) ≡ (refl , refl)) 
            (λ d₁ x → subst (λ xs → (_,_ {B = λ e → subst (μ D) e ⟨ x ⟩ ≡ ⟨ x ⟩} (linvΣ₁ (cong (λ { (d , y) → d , ⟨ proj₁ x , y ⟩ }) xs)) 
             (linvΣ₂ (cong (λ { (d , y) → d , ⟨ proj₁ x , y ⟩ }) xs))) 
            ≡ (refl , refl)) (sym (injectivityC'∘injectivityC (proj₂ x))) refl)
            d₁ x) 
        ex)
    ed y ex 

-- update the telescope by replacing (d₁ ≡ d₂)(x ≡ y) by equivalences of all the constructor arguments 
doinjectivityTel : {Δ : Telescope n} {D : DataDesc is cₙ}
    {d₁ : A → ⟦ is ⟧telD} {d₂ : A → ⟦ is ⟧telD} 
    {x : (a : A) → μ D (d₁ a)} {y : (a : A) → μ D (d₂ a)}
    {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
    (p : Δ [ k ]∶Σ[ A ] (λ a → d₁ a ≡ d₂ a) ∶ (λ a e → subst (μ D) e (x a) ≡ y a))
    (f : (a : A) → (conᵢ (x a) ≡ conᵢ (y a)))
    → Telescope (n + aₙ' ∸ 2)
doinjectivityTel {d₁ = d₁} {d₂} {x} {y} eℕ p f = updateTel₂ p (λ a → subst Telescope (eℕ a) (injectivityTel {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (injectivity {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a) e)) 
    (λ a e → subst (λ e' → injectivity' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity'∘injectivity {x = x a} {y = y a} (f a) e))

doInjectivity : {Δ : Telescope n} {D : DataDesc is cₙ}
    {d₁ : A → ⟦ is ⟧telD} {d₂ : A → ⟦ is ⟧telD} 
    {x : (a : A) → μ D (d₁ a)} {y : (a : A) → μ D (d₂ a)}
    {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
    (p : Δ [ k ]∶Σ[ A ] (λ a → d₁ a ≡ d₂ a) ∶ (λ a e → subst (μ D) e (x a) ≡ y a))
    (f : (a : A) → (conᵢ (x a) ≡ conᵢ (y a)))
    → (xs : ⟦ Δ ⟧telD)
    → ⟦ doinjectivityTel eℕ p f ⟧telD
doInjectivity {d₁ = d₁} {d₂} {x} {y} eℕ p f = update₂ p (λ a → subst Telescope (eℕ a) (injectivityTel {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (injectivity {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a) e)) 
    (λ a e → subst (λ e' → injectivity' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity'∘injectivity {x = x a} {y = y a} (f a) e))


doInjectivity' : {Δ : Telescope n} {D : DataDesc is cₙ}
    {d₁ : A → ⟦ is ⟧telD} {d₂ : A → ⟦ is ⟧telD} 
    {x : (a : A) → μ D (d₁ a)} {y : (a : A) → μ D (d₂ a)}
    {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
    (p : Δ [ k ]∶Σ[ A ] (λ a → d₁ a ≡ d₂ a) ∶ (λ a e → subst (μ D) e (x a) ≡ y a))
    (f : (a : A) → (conᵢ (x a) ≡ conᵢ (y a)))
    → ⟦ doinjectivityTel eℕ p f ⟧telD
    → ⟦ Δ ⟧telD
doInjectivity' {d₁ = d₁} {d₂} {x} {y} eℕ p f = update₂' p (λ a → subst Telescope (eℕ a) (injectivityTel {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (injectivity {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a) e)) 
    (λ a e → subst (λ e' → injectivity' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity'∘injectivity {x = x a} {y = y a} (f a) e))

doInjectivity'∘doInjectivity :  {Δ : Telescope n} {D : DataDesc is cₙ}
    {d₁ : A → ⟦ is ⟧telD} {d₂ : A → ⟦ is ⟧telD} 
    {x : (a : A) → μ D (d₁ a)} {y : (a : A) → μ D (d₂ a)}
    {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
    (p : Δ [ k ]∶Σ[ A ] (λ a → d₁ a ≡ d₂ a) ∶ (λ a e → subst (μ D) e (x a) ≡ y a))
    (f : (a : A) → (conᵢ (x a) ≡ conᵢ (y a))) (xs : ⟦ Δ ⟧telD)
    → doInjectivity' eℕ p f (doInjectivity eℕ p f xs) ≡ xs
doInjectivity'∘doInjectivity  {d₁ = d₁} {d₂} {x} {y} eℕ p f = update₂'∘update₂ p (λ a → subst Telescope (eℕ a) (injectivityTel {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (injectivity {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a) e)) 
    (λ a e → subst (λ e' → injectivity' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity'∘injectivity {x = x a} {y = y a} (f a) e))


-- injectivity rule for datatypes with no indices
injectivityTel₁ : {D : DataDesc nil cₙ} {x y : μ D tt} → conᵢ x ≡ conᵢ y → Telescope (conₙ x)
injectivityTel₁ {D = D} {x} {y} e = case-μ D (λ _ x → (y : μ D tt) → conᵢ x ≡ conᵢ y → Telescope (conₙ x)) 
        (λ _ x → case-μ D (λ _ y → proj₁ x ≡ conᵢ y → Telescope (proj₁ (D (proj₁ x)))) 
            (λ _ y e → injectivityTelC (proj₂ x) (subst (λ x → ⟦ proj₂ (D x) ⟧c (μ D) tt) (sym e) (proj₂ y))) tt) 
            tt x y e

injectivity₁ : {D : DataDesc nil cₙ} {x y : μ D tt} (f : conᵢ x ≡ conᵢ y) (e : x ≡ y) 
    → ⟦ injectivityTel₁ {x = x} {y = y} f ⟧telD
injectivity₁ {D = D} {x} {y} f e = J (λ y e → (f : conᵢ x ≡ conᵢ y) → ⟦ injectivityTel₁ {x = x} {y = y} f ⟧telD) 
    (λ f → K (λ f → ⟦ injectivityTel₁ {x = x} {y = x} f ⟧telD) 
        (case-μ D (λ _ x → ⟦ injectivityTel₁ {x = x} {y = x} refl ⟧telD) (λ _ x → injectivityC (proj₂ x)) tt
    x) f) e f

-- left inverse injectivity
injectivityC₁' : {X : ⟦ nil ⟧telD → Set}{C : ConDesc nil aₙ}
    → (x y : ⟦ C ⟧c X tt) → ⟦ injectivityTelC x y ⟧telD → x ≡ y
injectivityC₁' {C = one' tt} refl refl e = refl 
injectivityC₁' {X = X} {C = Σ' S D'} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    = Σ-create e (injectivityC₁' (subst (λ s → ⟦ D' s ⟧c X tt) e xs₁) xs₂ es) 
injectivityC₁' {C = ×' tt C} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    = ×-create e (injectivityC₁' xs₁ xs₂ es) 

injectivity₁' : {D : DataDesc nil cₙ} {x y : μ D tt}
    → (f : conᵢ x ≡ conᵢ y) → ⟦ injectivityTel₁ {x = x} {y = y} f ⟧telD → x ≡ y
injectivity₁' {D = D} {x} {y}
    = case-μ D (λ _ x → (y : μ D tt) → (f : conᵢ x ≡ conᵢ y) → ⟦ injectivityTel₁ {x = x} {y = y} f ⟧telD → x ≡ y) 
        (λ _ x → case-μ D (λ _ y → (f : proj₁ x ≡ conᵢ y) → ⟦ injectivityTel₁ {x = ⟨ x ⟩} {y = y} f ⟧telD → ⟨ x ⟩ ≡ y) 
            (λ _ y f → J (λ n₂ e → (y : ⟦ proj₂ (D n₂) ⟧c (μ D) tt) → ⟦ injectivityTel₁ {x = ⟨ x ⟩} {y = ⟨ n₂ , y ⟩} e ⟧telD → ⟨ x ⟩ ≡ ⟨ n₂ , y ⟩) 
                (λ y e → cong (λ xs → ⟨ proj₁ x , xs ⟩) (injectivityC₁' (proj₂ x) y e)) f (proj₂ y)) tt) tt x y

-- proof of left inverse injectivity
injectivityC₁'∘injectivityC : {X : ⟦ nil ⟧telD → Set}{C : ConDesc nil aₙ} (x : ⟦ C ⟧c X tt)
    → injectivityC₁' x x (injectivityC x) ≡ refl
injectivityC₁'∘injectivityC {C = one' tt} refl = refl
injectivityC₁'∘injectivityC {C = Σ' S E} (s , x) = subst (λ e → subst (λ x₁ → (s , x) ≡ (s , x₁)) e refl ≡ refl) (sym (injectivityC₁'∘injectivityC x)) refl
injectivityC₁'∘injectivityC {C = ×' tt C'} (u , x) = subst (λ e → subst (λ xs → (u , x) ≡ (u , xs)) e refl
      ≡ refl) (sym (injectivityC₁'∘injectivityC x)) refl 

injectivity₁'∘injectivity₁ : {D : DataDesc nil cₙ} {x y : μ D tt} → (f : conᵢ x ≡ conᵢ y)
    → (e : x ≡ y) → injectivity₁' {x = x} {y = y} f (injectivity₁ {x = x} {y = y} f e) ≡ e
injectivity₁'∘injectivity₁ {D = D} {x} {y} f e = J (λ y e → (f : conᵢ x ≡ conᵢ y) → injectivity₁' {x = x} {y = y} f (injectivity₁ {x = x} {y = y} f e) ≡ e) 
    (λ f → K (λ f → injectivity₁' {x = x} {y = x} f (injectivity₁ {x = x} {y = x} f refl) ≡ refl) 
        (case-μ D (λ _ x → injectivity₁' {x = x} {y = x} refl (injectivity₁ {x = x} {y = x} refl refl) ≡ refl) 
            (λ _ x → cong (cong (λ xs → ⟨ proj₁ x , xs ⟩)) (injectivityC₁'∘injectivityC (proj₂ x))) tt x) f) e f

-- update telescope
doinjectivityTel₁ :  {Δ : Telescope n} {D : DataDesc nil cₙ} {x y : A → μ D tt}
    {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
    (p : Δ [ k ]∶Σ[ A ] (λ a → (x a) ≡ y a))
    (f : (a : A) → (conᵢ (x a) ≡ conᵢ (y a)))
  → Telescope (n + aₙ' ∸ 1)
doinjectivityTel₁ {x = x} {y} eℕ p f = updateTel₁ p (λ a → subst Telescope (eℕ a) (injectivityTel₁ {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) (injectivity₁ {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity₁' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a) e)) 
    (λ a e → subst (λ e' → injectivity₁' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity₁ {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity₁'∘injectivity₁ {x = x a} {y = y a} (f a) e))

doInjectivity₁ : {Δ : Telescope n} {D : DataDesc nil cₙ} {x y : A → μ D tt}
    {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
    (p : Δ [ k ]∶Σ[ A ] (λ a → (x a) ≡ y a))
    (f : (a : A) → (conᵢ (x a) ≡ conᵢ (y a))) (xs : ⟦ Δ ⟧telD)
  → ⟦ doinjectivityTel₁ eℕ p f ⟧telD
doInjectivity₁ {x = x} {y} eℕ p f = update₁ p (λ a → subst Telescope (eℕ a) (injectivityTel₁ {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) (injectivity₁ {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity₁' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a) e)) 
    (λ a e → subst (λ e' → injectivity₁' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity₁ {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity₁'∘injectivity₁ {x = x a} {y = y a} (f a) e))

doInjectivity₁' : {Δ : Telescope n} {D : DataDesc nil cₙ} {x y : A → μ D tt}
    {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
    (p : Δ [ k ]∶Σ[ A ] (λ a → (x a) ≡ y a))
    (f : (a : A) → (conᵢ (x a) ≡ conᵢ (y a))) (xs : ⟦ doinjectivityTel₁ eℕ p f ⟧telD)
  → ⟦ Δ ⟧telD
doInjectivity₁' {x = x} {y} eℕ p f = update₁' p (λ a → subst Telescope (eℕ a) (injectivityTel₁ {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) (injectivity₁ {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity₁' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a) e)) 
    (λ a e → subst (λ e' → injectivity₁' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity₁ {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity₁'∘injectivity₁ {x = x a} {y = y a} (f a) e))

doInjectivity₁'∘doInjectivity₁ : {Δ : Telescope n} {D : DataDesc nil cₙ} {x y : A → μ D tt}
    {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
    (p : Δ [ k ]∶Σ[ A ] (λ a → (x a) ≡ y a))
    (f : (a : A) → (conᵢ (x a) ≡ conᵢ (y a))) (xs : ⟦ Δ ⟧telD)
  → doInjectivity₁' eℕ p f (doInjectivity₁ eℕ p f xs) ≡ xs
doInjectivity₁'∘doInjectivity₁ {x = x} {y} eℕ p f = update₁'∘update₁ p (λ a → subst Telescope (eℕ a) (injectivityTel₁ {x = x a} {y = y a} (f a))) 
    (λ a e → J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) (injectivity₁ {x = x a} {y = y a} (f a) e) (eℕ a)) 
    (λ a e → injectivity₁' {x = x a} {y = y a} (f a) (J' (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) (eℕ a) e)) 
    (λ a e → subst (λ e' → injectivity₁' {x = x a} {y = y a} (f a) e' ≡ e) 
        (sym (J'∘J (λ _ eℕ → ⟦ subst Telescope eℕ (injectivityTel₁ {x = x a} {y = y a} (f a)) ⟧telD) 
        (injectivity₁ {x = x a} {y = y a} (f a) e) (eℕ a))) (injectivity₁'∘injectivity₁ {x = x a} {y = y a} (f a) e))

-- reverse solution rule for HO unification
doSolution←Tel : {Δ : Telescope n} {A' : Set} (B : A' → Set)
    → (f : A → A')
    → {x y : (a : A) → B (f a)} 
    → (p : Δ [ k ]∶Σ[ A ] (λ a → x a ≡ y a)) 
    → Telescope (n + 3 ∸ 1)
doSolution←Tel B f {x} {y} p = updateTel₁ p (λ a → e ∈ f a ≡ f a , p ∈ e ≡ refl , x ∈ subst B e (x a) ≡ y a , nil) 
    (λ a xs → refl , refl , xs , tt) 
    (λ a xs → subst (λ e → subst B e (x a) ≡ (y a)) (proj₁ (proj₂ xs)) (proj₁ (proj₂ (proj₂ xs))))
    (λ a xs → refl) 

doSolution← : {Δ : Telescope n} {A' : Set} (B : A' → Set)
    → (f : A → A')
    → {x y : (a : A) → B (f a)} 
    → (p : Δ [ k ]∶Σ[ A ] (λ a → x a ≡ y a)) (xs : ⟦ Δ ⟧telD)
    → ⟦ doSolution←Tel B f p ⟧telD
doSolution← B f {x} {y} p = update₁ p (λ a → e ∈ f a ≡ f a , p ∈ e ≡ refl , x ∈ subst B e (x a) ≡ y a , nil) 
    (λ a xs → refl , refl , xs , tt) 
    (λ a xs → subst (λ e → subst B e (x a) ≡ (y a)) (proj₁ (proj₂ xs)) (proj₁ (proj₂ (proj₂ xs))))
    (λ a xs → refl) 

doSolution'← : {Δ : Telescope n} {A' : Set} (B : A' → Set)
    → (f : A → A')
    → {x y : (a : A) → B (f a)} 
    → (p : Δ [ k ]∶Σ[ A ] (λ a → x a ≡ y a)) → ⟦ doSolution←Tel B f p ⟧telD
    → ⟦ Δ ⟧telD
doSolution'← B f {x} {y} p = update₁' p (λ a → e ∈ f a ≡ f a , p ∈ e ≡ refl , x ∈ subst B e (x a) ≡ y a , nil) 
    (λ a xs → refl , refl , xs , tt) 
    (λ a xs → subst (λ e → subst B e (x a) ≡ (y a)) (proj₁ (proj₂ xs)) (proj₁ (proj₂ (proj₂ xs))))
    (λ a xs → refl) 

doSolution'∘doSolution← : {Δ : Telescope n} {A' : Set} (B : A' → Set)
    → (f : A → A')
    → {x y : (a : A) → B (f a)} 
    → (p : Δ [ k ]∶Σ[ A ] (λ a → x a ≡ y a)) → (xs : ⟦ Δ ⟧telD)
    → doSolution'← B f p (doSolution← B f p xs) ≡ xs
doSolution'∘doSolution← B f {x} {y} p = update₁'∘update₁ p (λ a → e ∈ f a ≡ f a , p ∈ e ≡ refl , x ∈ subst B e (x a) ≡ y a , nil) 
    (λ a xs → refl , refl , xs , tt) 
    (λ a xs → subst (λ e → subst B e (x a) ≡ (y a)) (proj₁ (proj₂ xs)) (proj₁ (proj₂ (proj₂ xs))))
    (λ a xs → refl) 