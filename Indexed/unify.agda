{-# OPTIONS --safe #-}
module Indexed.unify where 

open import Indexed.datatypes
open import Non_Indexed.telescope 
open import Indexed.unification
open import lib

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Agda.Builtin.Unit
open import Data.Empty
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_)
open import Data.Nat.Properties using (+-comm)
open import Data.Fin using (Fin; fromℕ; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Nullary using (Dec; yes; no; ¬_)

private variable
  n m k : ℕ
  cₙ iₙ : ℕ
  A : Set
  Δ : Telescope n
  is : Telescope iₙ

data Unification : (Δ : Telescope n) → Set₁ where 
    -- end of unification
    UEnd : (Δ : Telescope n) → Unification Δ

    -- (x : X) (x ≡ t) ≃ ()
    Usolution : {B : A → Set}
        → (p : Δ [ k ]∶Σ[ Σ[ a ∈ A ] (B a) ] (λ t → B (proj₁ t)) ∶ (λ t x → (proj₂ t) ≡ x))
        → Unification (doSolutionTel p)
        → Unification Δ

    -- (x : X) (t ≡ x) ≃ ()
    Usolution₁ : {B : A → Set}
        → (p : Δ [ k ]∶Σ[ Σ[ a ∈ A ] (B a) ] (λ t → B (proj₁ t)) ∶ (λ t x → x ≡ (proj₂ t))) 
        → Unification (doSolutionTel₁ p)
        → Unification Δ
    
    -- (t ≡ t) ≃ ()
    UDeletion : {B : A → Set}{f : (a : A) → B a}  
        → (p : Δ [ k ]∶Σ[ A ] (λ a → f a ≡ f a))
        → Unification (doDeletionTel p)
        → Unification Δ
    
    -- (d₁ ≡ d₂)(c x ≡ c y) ≃ (x ≡ y)
    UInjectivity : {D : DataDesc is cₙ}{d₁ : A → ⟦ is ⟧telD} {d₂ : A → ⟦ is ⟧telD} 
        → {x : (a : A) → μ D (d₁ a)} {y : (a : A) → μ D (d₂ a)} 
        → (p : Δ [ k ]∶Σ[ A ] (λ a → d₁ a ≡ d₂ a ) ∶ (λ a e → subst (μ D) e (x a) ≡ y a))
        → {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
        → (f : (a : A) → (conᵢ (x a) ≡ conᵢ (y a)))
        → Unification (doinjectivityTel eℕ p f)
        → Unification Δ

    -- (c x ≡ c y) ≃ (x ≡ y)
    UInjectivity₁ : {D : DataDesc nil cₙ} {x y : (a : A) → μ D tt}
        → (p : Δ [ k ]∶Σ[ A ] (λ a → (x a) ≡ y a))
        → {aₙ' : ℕ}(eℕ : (a : A) → conₙ (x a) ≡ aₙ')
        → (f : (a : A) → (conᵢ (x a) ≡ conᵢ (y a)))
        → Unification (doinjectivityTel₁ eℕ p f)
        → Unification Δ

    -- (d₁ ≡ d₂)(c₁ x ≡ c₂ y) ≃ ⊥
    UConflict : {D : DataDesc is cₙ} {d₁ : A → ⟦ is ⟧telD} {d₂ : A → ⟦ is ⟧telD} 
        → {x : (a : A) → μ D (d₁ a)} {y : (a : A) → μ D (d₂ a)}
        → (p : Δ [ k ]∶Σ[ A ] (λ a → d₁ a ≡ d₂ a ) ∶ (λ a e → subst (μ D) e (x a) ≡ y a))
        → (f : (a : A) → ¬ (conᵢ (x a) ≡ conᵢ (y a)))
        → Unification (doConflictTel p f)
        → Unification Δ
    
    -- move item at goal back if it is not dependent on items after split
    UReorder : (split : Fin n) (goal : Fin k)
        → (p : (x : ⟦ proj₁ (splitTel split Δ) ⟧telD) 
            → (Σ[ X ∈ Set ] ((proj₂ (splitTel split Δ)) x) [ k ]∶Σ[ ⊤ ] (λ _ → X)))
        → Unification (reorderTel split Δ goal p) 
        → Unification Δ

    -- (a₁ , b₁) ≡ (a₂ , b₂) ≃ (a₁ ≡ a₂)(b₁ ≡ b₂)
    USplitΣ : {B : A → Set} {C : (a : A) → B a → Set}
        → (BC₁ : (a : A) → Σ (B a) (C a)) → (BC₂ : (a : A) → Σ (B a) (C a))
        → (p : Δ [ k ]∶Σ[ A ] (λ a → BC₁ a ≡ BC₂ a))
        → Unification (splitΣTel BC₁ BC₂ p)
        → Unification Δ
    
    -- (a₁ ≡ a₂) ≃ (a₁ , tt) ≡ (a₂ , tt)
    UCombineΣ : {B : A → Set} (B₁ : (a : A) → B a) (B₂ : (a : A) → B a)
        → (p : Δ [ k ]∶Σ[ A ] (λ a → B₁ a ≡ B₂ a))
        → Unification (combineΣTel B₁ B₂ p)
        → Unification Δ

    -- replace elements Y₁ x if it is equivalent to another element Y₂ x
    UReplaceElem : {B₁ B₂ : A → Set} 
        → (p : Δ [ k ]∶Σ[ A ] B₁) (f : (a : A) → B₁ a ≡ B₂ a)
        → Unification (replaceInTel B₁ B₂ Δ p f)
        → Unification Δ

    -- apply a custom rule for which you have the functions f, f', and f'∘f
    UAddRule₁ : {X : Set}{A : X → Set}
        → (p : Δ [ k ]∶Σ[ X ] (λ x → A x)) 
        → (fTel : (x : X) → Telescope m)
        → (f : (x : X) → A x → ⟦ fTel x ⟧telD)
        → (f' : (x : X) → ⟦ fTel x ⟧telD → A x)
        → (f'∘f : (x : X) → (a : A x) → f' x (f x a) ≡ a)
        → Unification (updateTel₁ p fTel f f' f'∘f)
        → Unification Δ
    
    -- apply a custom rule for which you have the functions f, f', and f'∘f for consecutive elements
    UAddRule₂ : {X : Set}{A : X → Set}{B : (x : X)(a : A x) → Set}
        → (p : Δ [ k ]∶Σ[ X ] (λ x → A x) ∶ (λ x a → B x a)) 
        → (fTel : (x : X) → Telescope m)
        → (f : (x : X) → Σ[ a ∈ A x ] (B x a) → ⟦ fTel x ⟧telD)
        → (f' : (x : X) → ⟦ fTel x ⟧telD → Σ[ a ∈ A x ] (B x a))
        → (f'∘f : (x : X) → (e : Σ[ a ∈ A x ] (B x a)) → f' x (f x e) ≡ e)
        → Unification (updateTel₂ p fTel f f' f'∘f)
        → Unification Δ
        
    -- (x y : B a)(x ≡ y) ≃ (x y : B a)(e : a ≡ a)(e ≡ refl)(subst B e x ≡ y)
    U←Solution : {A' : Set} (B : A' → Set)
        → (f : A → A')
        → {x y : (a : A) → B (f a)} 
        → (p : Δ [ k ]∶Σ[ A ] (λ a → x a ≡ y a))
        → Unification (doSolution←Tel B f p)
        → Unification Δ


unifyTel : {Δ : Telescope n} (u : Unification Δ) 
    → Σ ℕ Telescope
unifyTel (UEnd Δ) = _ , Δ
unifyTel (Usolution p u) = unifyTel u
unifyTel (Usolution₁ p u) = unifyTel u
unifyTel (UDeletion p u) = unifyTel u
unifyTel (UInjectivity p eℕ f u) = unifyTel u
unifyTel (UInjectivity₁ p eℕ f u) = unifyTel u
unifyTel (UConflict p f u) = unifyTel u
unifyTel (UReorder split goal p u) = unifyTel u
unifyTel (USplitΣ AB₁ AB₂ p u) = unifyTel u
unifyTel (UCombineΣ A₁ A₂ p u) = unifyTel u
unifyTel (UReplaceElem p f u) = unifyTel u
unifyTel (UAddRule₁ p fTel f f' f'∘f u) = unifyTel u
unifyTel (UAddRule₂ p fTel f f' f'∘f u) = unifyTel u
unifyTel (U←Solution A f p u) = unifyTel u

unify : {Δ : Telescope n} (u : Unification Δ) (xs : ⟦ Δ ⟧telD)
    → ⟦ proj₂ (unifyTel u) ⟧telD
unify (UEnd _) xs = xs
unify (Usolution p u) xs = unify u (update₂ p (λ _ → nil) (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) xs)
unify (Usolution₁ p u) xs = unify u (update₂ p (λ _ → nil) (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) xs)
unify (UDeletion p u) xs = unify u (update₁ p (λ _ → nil) (λ xa → deletion) (λ xa → deletion') (λ xa → deletion'∘deletion) xs)
unify (UInjectivity p eℕ f u) xs = unify u (doInjectivity eℕ p f xs)
unify (UInjectivity₁ p eℕ f u) xs = unify u (doInjectivity₁ eℕ p f xs)
unify (UConflict p f u) xs = unify u (update₂ p (λ _ → cons ⊥ (λ b → nil)) (λ a → conflict (f a)) 
    (λ a → conflict' (f a)) (λ a → conflict'∘conflict (f a)) xs)
unify (UReorder split goal p u) xs = unify u (reorder split goal p xs)
unify (USplitΣ AB₁ AB₂ p u) xs = unify u (splitΣ AB₁ AB₂ p xs)
unify (UCombineΣ A₁ A₂ p u) xs = unify u (combineΣ A₁ A₂ p xs)
unify (UReplaceElem p f u) xs = unify u (replaceIn p f xs)
unify (UAddRule₁ p fTel f f' f'∘f u) xs = unify u (update₁ p fTel f f' f'∘f xs)
unify (UAddRule₂ p fTel f f' f'∘f u) xs = unify u (update₂ p fTel f f' f'∘f xs)
unify (U←Solution A f p u) xs = unify u (doSolution← A f p xs)

unify' : {Δ : Telescope n} (u : Unification Δ) (xs : ⟦ proj₂ (unifyTel u) ⟧telD)
    → ⟦ Δ ⟧telD
unify' (UEnd _) xs = xs
unify' (Usolution p u) xs = update₂' p (λ _ → nil) (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) (unify' u xs)
unify' (Usolution₁ p u) xs = update₂' p (λ _ → nil) (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) (unify' u xs)
unify' (UDeletion p u) xs = update₁' p (λ _ → nil) (λ xa → deletion) (λ xa → deletion') (λ xa → deletion'∘deletion) (unify' u xs)
unify' (UInjectivity p eℕ f u) xs = doInjectivity' eℕ p f (unify' u xs)
unify' (UInjectivity₁ p eℕ f u) xs = doInjectivity₁' eℕ p f (unify' u xs)
unify' (UConflict p f u) xs = update₂' p (λ _ → cons ⊥ (λ b → nil)) (λ a → conflict (f a)) 
    (λ a → conflict' (f a)) (λ a → conflict'∘conflict (f a)) (unify' u xs)
unify' (UReorder split goal p u) xs = reorder' split goal p (unify' u xs)
unify' (USplitΣ AB₁ AB₂ p u) xs = splitΣ' AB₁ AB₂ p (unify' u xs)
unify' (UCombineΣ A₁ A₂ p u) xs = combineΣ' A₁ A₂ p (unify' u xs)
unify' (UReplaceElem p f u) xs = replaceIn' p f (unify' u xs)
unify' (UAddRule₁ p fTel f f' f'∘f u) xs = update₁' p fTel f f' f'∘f (unify' u xs)
unify' (UAddRule₂ p fTel f f' f'∘f u) xs = update₂' p fTel f f' f'∘f (unify' u xs)
unify' (U←Solution A f p u) xs = doSolution'← A f p (unify' u xs)

unify'∘unify : {Δ : Telescope n} (u : Unification Δ) (xs : ⟦ Δ ⟧telD)
    → unify' u (unify u xs) ≡ xs
unify'∘unify (UEnd _) xs = refl
unify'∘unify (Usolution p u) xs = subst (λ xs' → update₂' p (λ _ → nil) (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) xs' ≡ xs) 
    (sym (unify'∘unify u ((update₂ p (λ _ → nil) (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) xs)))) 
    (update₂'∘update₂ p (λ _ → nil) (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) xs)
unify'∘unify (Usolution₁ p u) xs = subst (λ xs' → update₂' p (λ _ → nil) (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) xs' ≡ xs) 
    (sym (unify'∘unify u ((update₂ p (λ _ → nil) (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) xs)))) 
    (update₂'∘update₂ p (λ _ → nil) (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) xs)
unify'∘unify (UDeletion p u) xs = subst (λ xs' → update₁' p (λ _ → nil) (λ xa → deletion) (λ xa → deletion') (λ xa → deletion'∘deletion) xs' ≡ xs) 
    (sym (unify'∘unify u ((update₁ p (λ _ → nil) (λ xa → deletion) (λ xa → deletion') (λ xa → deletion'∘deletion) xs)))) 
    (update₁'∘update₁ p (λ _ → nil) (λ xa → deletion) (λ xa → deletion') (λ xa → deletion'∘deletion) xs)
unify'∘unify (UInjectivity p eℕ f u) xs = subst (λ xs' → doInjectivity' eℕ p f xs' ≡ xs) (sym (unify'∘unify u (doInjectivity eℕ p f xs))) (doInjectivity'∘doInjectivity eℕ p f xs)
unify'∘unify (UInjectivity₁ p eℕ f u) xs = subst (λ xs' → doInjectivity₁' eℕ p f xs' ≡ xs) (sym (unify'∘unify u (doInjectivity₁ eℕ p f xs))) (doInjectivity₁'∘doInjectivity₁ eℕ p f xs)
unify'∘unify (UConflict p f u) xs = subst (λ xs' → update₂' p (λ _ → cons ⊥ (λ b → nil)) (λ a → conflict (f a)) 
    (λ a → conflict' (f a)) (λ a → conflict'∘conflict (f a)) xs' ≡ xs) 
    (sym (unify'∘unify u ((update₂ p (λ _ → cons ⊥ (λ b → nil)) (λ a → conflict (f a)) 
    (λ a → conflict' (f a)) (λ a → conflict'∘conflict (f a)) xs)))) 
    (update₂'∘update₂ p (λ _ → cons ⊥ (λ b → nil)) (λ a → conflict (f a)) 
    (λ a → conflict' (f a)) (λ a → conflict'∘conflict (f a)) xs) 
unify'∘unify (UReorder split goal p u) xs = subst (λ xs' → reorder' split goal p xs' ≡ xs) (sym (unify'∘unify u (reorder split goal p xs))) (reorder'∘reorder split goal p xs)
unify'∘unify (USplitΣ AB₁ AB₂ p u) xs = subst (λ xs' → splitΣ' AB₁ AB₂ p xs' ≡ xs) (sym (unify'∘unify u (splitΣ AB₁ AB₂ p xs))) (splitΣ'∘splitΣ AB₁ AB₂ p xs)
unify'∘unify (UCombineΣ A₁ A₂ p u) xs = subst (λ xs' → combineΣ' A₁ A₂ p xs' ≡ xs) (sym (unify'∘unify u (combineΣ A₁ A₂ p xs))) (combineΣ'∘combineΣ A₁ A₂ p xs)
unify'∘unify (UReplaceElem p f u) xs = subst (λ xs' → replaceIn' p f xs' ≡ xs) (sym (unify'∘unify u (replaceIn p f xs))) (replaceIn'∘replaceIn p f xs)
unify'∘unify (UAddRule₁ p fTel f f' f'∘f u) xs = subst (λ xs' → update₁' p fTel f f' f'∘f xs' ≡ xs) (sym (unify'∘unify u (update₁ p fTel f f' f'∘f xs))) (update₁'∘update₁ p fTel f f' f'∘f xs)
unify'∘unify (UAddRule₂ p fTel f f' f'∘f u) xs = subst (λ xs' → update₂' p fTel f f' f'∘f xs' ≡ xs) (sym (unify'∘unify u (update₂ p fTel f f' f'∘f xs))) (update₂'∘update₂ p fTel f f' f'∘f xs)
unify'∘unify (U←Solution A f p u) xs = subst (λ xs' → doSolution'← A f p xs' ≡ xs) (sym (unify'∘unify u (doSolution← A f p xs))) (doSolution'∘doSolution← A f p xs)


-- example application conflict
Δconflict : (X : Set) → Telescope 5
Δconflict X = n ∈ μ NatD tt , x ∈ X , xs ∈ μ (VecD X) (n , tt) ,
            e₁ ∈ (suc₁ n , tt) ≡ (zero' , tt) ,
            e₂ ∈ (subst (μ (VecD X)) e₁ (cons₁ X n x xs)) ≡ nil' ,
            nil

Δconflict₁ : (X : Set) → Telescope 4
Δconflict₁ X = n ∈ μ NatD tt , x ∈ X , xs ∈ μ (VecD X) (n , tt) ,
                b ∈ ⊥ , nil

unifyConflict : (X : Set) → Unification (Δconflict X)
unifyConflict X = UConflict 
    {A = Σ[ n ∈ μ NatD tt ] (Σ[ x ∈ X ] (μ (VecD X) (n , tt)))} 
    {d₁ = λ where (n , x , xs) → (suc₁ n , tt)}
    {d₂ = λ _ → (zero' , tt)}
    {x = λ where (n , x , xs) → cons₁ X n x xs}
    {y = λ _ → nil'}
    (there λ n → there λ x → there λ xs → here (n , x , xs)) 
    (λ x ()) 
    (UEnd (Δconflict₁ X))


-- example application injectivity
Δinjectivity : (X : Set) → Telescope 8
Δinjectivity X = n ∈ μ NatD tt , m ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (m , tt) ,
            e₁ ∈ (suc₁ n , tt) ≡ (suc₁ m , tt) ,
            e₂ ∈ subst (μ (VecD X)) e₁ (cons₁ X n x xs) ≡ cons₁ X m y ys , nil

Δinjectivity₁ : (X : Set) → Telescope 9
Δinjectivity₁ X = n ∈ μ NatD tt , m ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (m , tt) ,
                e₁ ∈ n ≡ m , 
                e₂ ∈ proj₁ (subst (λ n' →
                    ⟦ Σ' X (λ x₂ → ×' (n' , tt) (one' (suc' n' , tt))) ⟧c (μ (VecD X))
                        (suc₁ n , tt)) 
                            e₁ (x , xs , refl {x = (suc' n) , tt})) ≡ y , 
                e₃ ∈ proj₁ (subst (λ x → ⟦ ×' (proj₁
                                (subst  (λ x₁ → ⟦ snd (VecD X x₁) ⟧c (μ (VecD X))
                                    (suc₁ m , tt )) (sym (refl {x = f1})) (m , y , ys , refl {x = (suc' m) , tt})) , tt)
                                (one' (suc' (proj₁ (subst (λ x₁ →
                                    ⟦ snd (VecD X x₁) ⟧c (μ (VecD X)) (suc₁ m , tt ))
                                        (sym (refl {x = f1})) (m , y , ys , refl {x = (suc' m) , tt}))) , tt)) ⟧c
                                (μ (VecD X)) (suc₁ n , tt ))
                                e₂ (snd (subst (λ x → ⟦ Σ' X (λ x₁ → ×' (x , tt) 
                                    (one' (suc' x , tt))) ⟧c (μ (VecD X)) (suc₁ n , tt))
                            e₁ (x , xs , refl {x = (suc' n) , tt})))) 
                        ≡ proj₁ (snd (snd (subst (λ x → ⟦ snd (VecD X x) ⟧c (μ (VecD X)) (suc₁ m , tt))
                                (sym (refl {x = f1})) (m , y , ys , refl {x = (suc' m) , tt})))) , nil

Δinjectivity₂ : (X : Set) → Telescope 9 
Δinjectivity₂ X = n ∈ μ NatD tt , m ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (m , tt) ,
                e₁ ∈ n ≡ m , e₂ ∈ x ≡ y , e₃ ∈ subst (λ n → μ (VecD X) (n , tt)) e₁ xs ≡ ys , nil

unifyInjectivity : (X : Set) → Unification (Δinjectivity X)
unifyInjectivity X = UInjectivity 
        {A = Σ[ n ∈ μ NatD tt ] (Σ[ x ∈ X ] (Σ[ xs ∈ μ (VecD X) (n , tt) ] (Σ[ m ∈ μ NatD tt ] (Σ[ y ∈ X ] (μ (VecD X) (m , tt))))))} 
        {d₁ = λ where (n , x , xs , m , y , ys) → (suc₁ n , tt)}
        {d₂ = λ where (n , x , xs , m , y , ys) → (suc₁ m , tt)}
        {x = λ where (n , x , xs , m , y , ys) → cons₁ X n x xs}
        {y = λ where (n , x , xs , m , y , ys) → cons₁ X m y ys}
        (there λ n → there λ m → there λ x → there λ y → there λ xs → there λ ys 
            → here (n , x , xs , m , y , ys)) 
        (λ x → refl) (λ x → refl) 
    (UReplaceElem (there λ n → there λ m → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
                → here (n , m , x , y , xs , ys , e₁))  (λ where 
                    (n , m , x , y , xs , ys , e₁) → J (λ _ e₁ → (proj₁ (subst (λ n' →
                        Σ-syntax X (λ s → μ (VecD X) (n' , tt) × (suc' n' , tt) ≡ (suc₁ n , tt))) e₁ (x , xs , refl))
                            ≡ y) ≡ (x ≡ y)) refl e₁) 
        (UReplaceElem (there λ n → there λ m → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ → there λ e₂
                → here (n , m , x , y , xs , ys , e₁ , e₂)) (λ where 
                (n , m , x , y , xs , ys , e₁ , e₂) → J (λ y e₂ → (proj₁ (subst
                    (λ x₁ → μ (VecD X) (m , tt) × (suc' m , tt) ≡ (suc₁ n , tt))
                    (subst id (sym (J (λ z e₃ → (proj₁
                    (subst (λ n' → Σ-syntax X
                    (λ s → μ (VecD X) (n' , tt) × (suc' n' , tt) ≡ (suc₁ n , tt)))
                        e₃ (x , xs , refl)) ≡ y) ≡ (x ≡ y)) refl e₁)) e₂)
                            (snd (subst (λ x₁ → Σ-syntax X
                                (λ s → μ (VecD X) (x₁ , tt) × (suc' x₁ , tt) ≡ (suc₁ n , tt )))
                                    e₁ (x , xs , refl)))) ≡ ys)
                    ≡ (subst (λ n₁ → μ (VecD X) (n₁ , tt)) e₁ xs ≡ ys)) 
                    (J (λ m e₁ → (ys : μ (VecD X) (m , tt)) → (proj₁
                    (subst (λ x₁ → μ (VecD X) (m , tt) × (suc' m , tt) ≡ (suc₁ n , tt))
                        (subst id
                        (sym
                        (J
                        (λ z e₃ →
                            (proj₁
                            (subst
                                (λ n' →
                                Σ-syntax X
                                (λ s → μ (VecD X) (n' , tt) × (suc' n' , tt) ≡ (suc₁ n , tt)))
                                e₃ (x , xs , refl))
                            ≡ x)
                            ≡ (x ≡ x))
                        refl e₁))
                        refl)
                        (snd
                        (subst
                        (λ x₁ →
                            Σ-syntax X
                            (λ s → μ (VecD X) (x₁ , tt) × (suc' x₁ , tt) ≡ (suc₁ n , tt)))
                        e₁ (x , xs , refl))))
                    ≡ ys)
                    ≡ (subst (λ n₁ → μ (VecD X) (n₁ , tt)) e₁ xs ≡ ys)) (λ _ → refl) e₁ ys)
                    e₂)
            (UEnd (Δinjectivity₂ X))))
    
