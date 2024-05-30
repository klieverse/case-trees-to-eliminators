module Indexed.HOUnification where
    
open import Indexed.datatypes 
open import Non_Indexed.telescope
open import Indexed.unification
open import Indexed.casetrees
open import Indexed.translation
open import Indexed.unify
open import lib

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Unit.Base
open import Data.Empty
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ<; toℕ) renaming (zero to fzero; suc to fsuc)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)


injectivity⊤ : (e : tt ≡ tt) → ⊤
injectivity⊤ e = tt

injectivity⊤' : ⊤ → tt ≡ tt
injectivity⊤' e = refl

injectivity⊤'∘injectivity⊤ : (e : tt ≡ tt)
    → injectivity⊤' (injectivity⊤ e) ≡ e 
injectivity⊤'∘injectivity⊤ e = J (λ _ e → injectivity⊤' (injectivity⊤ e) ≡ e) refl e 


unifyxs : {n : ℕ} {Δ : Telescope n} (u : Unification Δ) (xs ys : ⟦ Δ ⟧telD)
  → xs ≡ ys
  → unify u xs ≡ unify u ys 
unifyxs u xs ys e = cong (unify u) e

unifyxs' : {n : ℕ}{Δ : Telescope n} (u : Unification Δ) (xs ys : ⟦ Δ ⟧telD)
  → unify u xs ≡ unify u ys 
  → xs ≡ ys
unifyxs' u xs ys e = subst (λ e → e ≡ ys) (unify'∘unify u xs) 
  (subst (λ e → unify' u (unify u xs) ≡ e) (unify'∘unify u ys) 
      (cong (unify' u) e)) 

unifyxs'∘unifyxs : {n : ℕ}{Δ : Telescope n} (u : Unification Δ) (xs ys : ⟦ Δ ⟧telD)
  → (e : xs ≡ ys) 
  → unifyxs' u xs ys (unifyxs u xs ys e) ≡ e 
unifyxs'∘unifyxs u xs ys e = subst∘subst e (unify u) (unify' u) (unify'∘unify u) 

mergexs : {n m : ℕ} {X : Telescope n} {S : Set} {Y : S → Telescope m}
    {f : ⟦ X ⟧telD → S}
  → (x₁ x₂ : ⟦ X ⟧telD) (y₁ : ⟦ Y (f x₁) ⟧telD) (y₂ : ⟦ Y (f x₂) ⟧telD)
  → (x₁ , y₁) ≡ (x₂ , y₂) 
  → merge {X = X} {Y = Y} {f = f} x₁ y₁ ≡ merge x₂ y₂
mergexs x₁ x₂ y₁ y₂ e = cong (λ x → merge (proj₁ x) (snd x)) e 

mergexs' : {n m : ℕ} {X : Telescope n} {S : Set} {Y : S → Telescope m}
    {f : ⟦ X ⟧telD → S}
  → (x₁ x₂ : ⟦ X ⟧telD) (y₁ : ⟦ Y (f x₁) ⟧telD) (y₂ : ⟦ Y (f x₂) ⟧telD)
  → merge {X = X} {Y = Y} {f = f} x₁ y₁ ≡ merge x₂ y₂
  → (x₁ , y₁) ≡ (x₂ , y₂) 
mergexs' {X = X} {S} {Y} {f} x₁ x₂ y₁ y₂ e = subst (λ e → e ≡ (x₂ , y₂)) (sym (mproj∘merge {X = X} {Y = Y} {f = f} x₁ y₁)) 
  (subst (λ e → (mproj₁ (merge {X = X} {Y = Y} {f = f} x₁ y₁) , 
          mproj₂ {X = X} {Y = Y} {f = f} (merge {X = X} {Y = Y} {f = f} x₁ y₁)) ≡ e) (sym (mproj∘merge {X = X} {Y = Y} {f = f} x₂ y₂)) (cong (λ x → (mproj₁ x , mproj₂ {X = X} {Y = Y} {f = f} x)) e))

mergexs'∘mergexs : {n m : ℕ} {X : Telescope n} {S : Set} {Y : S → Telescope m}
    {f : ⟦ X ⟧telD → S}
  → (x₁ x₂ : ⟦ X ⟧telD) (y₁ : ⟦ Y (f x₁) ⟧telD) (y₂ : ⟦ Y (f x₂) ⟧telD)
  → (e : (x₁ , y₁) ≡ (x₂ , y₂))
  → mergexs' {Y = Y} {f = f} x₁ x₂ y₁ y₂ (mergexs {Y = Y} {f = f} x₁ x₂ y₁ y₂ e) ≡ e
mergexs'∘mergexs {X = X} {S} {Y} {f} x₁ x₂ y₁ y₂ e = subst∘subst e (λ a → merge {X = X} {Y = Y} {f = f} (proj₁ a) (proj₂ a)) (λ x → (mproj₁ x , mproj₂ {X = X} {Y = Y} {f = f} x))
  (λ a → sym (mproj∘merge {X = X} {Y = Y} {f = f} (proj₁ a) (proj₂ a))) 

HOUnification₁ : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → Σ[ e ∈ u ≡ v ] (subst (λ v₁ → a (f' v₁) ≡ b (f' v₁)) e r ≡ s)
    → unify f (merge u (r , tt)) ≡ unify f (merge v (s , tt))
HOUnification₁ a b f' f u v r s (e , xs) = unifyxs f (merge u (r , tt)) (merge v (s , tt)) 
  (mergexs u v (r , tt) (s , tt) (cong (λ x → (proj₁ x , proj₂ x , tt)) (Σ-create e xs)))

HOUnification₁' : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → unify f (merge u (r , tt)) ≡ unify f (merge v (s , tt))
    → Σ[ e ∈ u ≡ v ] (subst (λ v₁ → a (f' v₁) ≡ b (f' v₁)) e r ≡ s)
HOUnification₁' {Δ = Δ} a b f' f u v r s e = linvΣ₁ ex , linvΣ₂ ex where 

  ex : (u , r) ≡ (v , s) 
  ex = cong (λ x → proj₁ x , proj₁ (snd x)) (mergexs' u v (r , tt) (s , tt) (unifyxs' f (merge u (r , tt)) (merge v (s , tt)) e))
   
HOUnification₁'∘HOUnification₁' : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → (ex : Σ[ e ∈ u ≡ v ] (subst (λ v₁ → a (f' v₁) ≡ b (f' v₁)) e r ≡ s)) 
    → HOUnification₁' {Δ = Δ} a b f' f u v r s (HOUnification₁ a b f' f u v r s ex) ≡ ex 
HOUnification₁'∘HOUnification₁'  {Δ = Δ} a b f' f u v r s (e , xs) = goal where 
  
  goal₃ : (linvΣ₁ (Σ-create e xs) , linvΣ₂ (Σ-create e xs)) ≡ (e , xs)
  goal₃ = Σ-create (isLinvΣ₁ e xs) (isLinvΣ₂ e xs) 

  goal₂' : (cong (λ x → proj₁ x , proj₁ (snd x)) (cong (λ x → (proj₁ x , proj₂ x , tt)) (Σ-create e xs))) ≡ Σ-create e xs 
  goal₂' = J (λ x e → cong (λ x → proj₁ x , proj₁ (snd x)) (cong (λ x → (proj₁ x , proj₂ x , tt)) e) ≡ e) refl (Σ-create e xs)

  goal₂ : (linvΣ₁ (cong (λ x → proj₁ x , proj₁ (snd x)) (cong (λ x → (proj₁ x , proj₂ x , tt)) (Σ-create e xs))) , 
    linvΣ₂ (cong (λ x → proj₁ x , proj₁ (snd x)) (cong (λ x → (proj₁ x , proj₂ x , tt)) (Σ-create e xs)))) ≡ (e , xs)
  goal₂ = subst (λ e₁ → (linvΣ₁ e₁ , linvΣ₂ e₁) ≡ (e , xs)) 
      (sym goal₂') goal₃

  goal₁ : (linvΣ₁ (cong (λ x → proj₁ x , proj₁ (snd x)) (mergexs' u v (r , tt) (s , tt) 
    (mergexs u v (r , tt) (s , tt) (cong (λ x → (proj₁ x , proj₂ x , tt)) (Σ-create e xs))))) , 
    linvΣ₂ (cong (λ x → proj₁ x , proj₁ (snd x)) (mergexs' u v (r , tt) (s , tt) 
    (mergexs u v (r , tt) (s , tt) (cong (λ x → (proj₁ x , proj₂ x , tt)) (Σ-create e xs)))))) ≡ (e , xs)
  goal₁ = subst (λ e₁ → (linvΣ₁ (cong (λ x → proj₁ x , proj₁ (snd x)) e₁) , 
    linvΣ₂ (cong (λ x → proj₁ x , proj₁ (snd x)) e₁)) ≡ (e , xs)) 
    (sym (mergexs'∘mergexs u v (r , tt) (s , tt) (cong (λ x → (proj₁ x , proj₂ x , tt)) (Σ-create e xs)))) 
    goal₂

  goal : (linvΣ₁ (cong (λ x → proj₁ x , proj₁ (snd x)) (mergexs' u v (r , tt) (s , tt) (unifyxs' f (merge u (r , tt)) (merge v (s , tt)) (unifyxs f (merge u (r , tt)) (merge v (s , tt)) 
    (mergexs u v (r , tt) (s , tt) (cong (λ x → (proj₁ x , proj₂ x , tt)) (Σ-create e xs))))))) , 
    linvΣ₂ (cong (λ x → proj₁ x , proj₁ (snd x)) (mergexs' u v (r , tt) (s , tt) (unifyxs' f (merge u (r , tt)) (merge v (s , tt)) (unifyxs f (merge u (r , tt)) (merge v (s , tt)) 
    (mergexs u v (r , tt) (s , tt) (cong (λ x → (proj₁ x , proj₂ x , tt)) (Σ-create e xs)))))))) ≡ (e , xs)
  goal = subst (λ e₁ → (linvΣ₁ (cong (λ x → proj₁ x , proj₁ (snd x)) (mergexs' u v (r , tt) (s , tt) e₁)) , 
    linvΣ₂ (cong (λ x → proj₁ x , proj₁ (snd x)) (mergexs' u v (r , tt) (s , tt) e₁))) ≡ (e , xs)) 
      (sym (unifyxs'∘unifyxs f (merge u (r , tt)) (merge v (s , tt)) 
    (mergexs u v (r , tt) (s , tt) (cong (λ x → (proj₁ x , proj₂ x , tt)) (Σ-create e xs))))) goal₁


HOUnification : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → Σ[ e ∈ u ≡ v ] (subst (λ ab → proj₁ ab ≡ proj₂ ab) (Π-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e) 
    → unify f (merge u (r , tt)) ≡ unify f (merge v (s , tt))
HOUnification a b f' f u v r s (e , xs) = HOUnification₁ a b f' f u v r s (e , cong→subst id (λ x → a (f' x) ≡ b (f' x)) e r s 
    (Π-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs))) 
    
HOUnification' : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → unify f (merge {X = Δ} {Y = (λ x → (p ∈ a x ≡ b x , nil))} {f = f'} u (r , tt)) ≡ unify f (merge v (s , tt))
    → Σ[ e ∈ u ≡ v ] (subst (λ ab → proj₁ ab ≡ proj₂ ab) (Π-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e) 
HOUnification' {Δ = Δ} a b f' f u v r s e = e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s 
  (Π-cong→create e' r s (subst→cong id (λ x → a (f' x) ≡ b (f' x)) e' r s xs')) where  

    e' : u ≡ v 
    e' = proj₁ (HOUnification₁' a b f' f u v r s e)

    xs' : subst (λ v₁ → a (f' v₁) ≡ b (f' v₁)) e' r ≡ s
    xs' = proj₂ (HOUnification₁' a b f' f u v r s e)

HOUnification'∘HOUnification : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → (e : Σ[ e ∈ u ≡ v ] (subst (λ ab → proj₁ ab ≡ proj₂ ab) (Π-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e))
    → HOUnification' a b f' f u v r s (HOUnification a b f' f u v r s e) ≡ e
HOUnification'∘HOUnification {Δ = Δ} {X} {Y} a b f' f u v r s (e , xs) = goal where 

  e' : u ≡ v 
  e' = e

  xs' : subst (λ v₁ → a (f' v₁) ≡ b (f' v₁)) e' r ≡ s
  xs' = cong→subst id (λ x → a (f' x) ≡ b (f' x)) e r s 
    (Π-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs))

  goal₃ : (e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s 
    (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs)) ≡ (e , xs)
  goal₃ = subst (λ e₁ → (e' , e₁) ≡ (e , xs)) (sym (flipSquare∘flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs)) refl

  goal₂ : (e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s 
    (Π-cong→create {a = λ xs → a (f' xs)} {b = λ xs → b (f' xs)} {f' = id} e' r s (Π-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs)))) ≡ (e , xs)
  goal₂ = subst (λ e₁ → (e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s  e₁) ≡ (e , xs)) 
            (sym (Π-cong→create∘Π-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs))) goal₃

  goal₁ : (e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s 
    (Π-cong→create e' r s (subst→cong id (λ x → a (f' x) ≡ b (f' x)) e' r s (cong→subst id (λ x → a (f' x) ≡ b (f' x)) e r s 
    (Π-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs)))))) ≡ (e , xs)
  goal₁ = subst (λ e₁ → (e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s 
    (Π-cong→create e' r s e₁)) ≡ (e , xs)) (sym (subst→cong∘cong→subst {f = id} {P = λ x → a (f' x) ≡ b (f' x)} e r s (Π-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs)))) goal₂

  goal : (proj₁ (HOUnification₁' a b f' f u v r s (HOUnification₁ a b f' f u v r s (e' , xs'))) , 
    flipSquare (cong (λ xs → a (f' xs)) (proj₁ (HOUnification₁' a b f' f u v r s (HOUnification₁ a b f' f u v r s (e' , xs'))))) (cong (λ xs → b (f' xs)) (proj₁ (HOUnification₁' a b f' f u v r s (HOUnification₁ a b f' f u v r s (e' , xs'))))) r s 
    (Π-cong→create (proj₁ (HOUnification₁' a b f' f u v r s (HOUnification₁ a b f' f u v r s (e' , xs')))) r s (subst→cong id (λ x → a (f' x) ≡ b (f' x)) (proj₁ (HOUnification₁' a b f' f u v r s (HOUnification₁ a b f' f u v r s (e' , xs')))) r s (proj₂ (HOUnification₁' a b f' f u v r s (HOUnification₁ a b f' f u v r s (e' , xs'))))))
    ) ≡ (e , xs)
  goal = subst (λ e₁ → (proj₁ e₁ , 
    flipSquare (cong (λ xs → a (f' xs)) (proj₁ e₁)) (cong (λ xs → b (f' xs)) (proj₁ e₁)) r s 
    (Π-cong→create (proj₁ e₁) r s (subst→cong id (λ x → a (f' x) ≡ b (f' x)) (proj₁ e₁) r s (proj₂ e₁)))
    ) ≡ (e , xs)) (sym (HOUnification₁'∘HOUnification₁' a b f' f u v r s (e' , xs'))) goal₁





ΔHOUnification : (X : Set) → Telescope 6 
ΔHOUnification X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e ∈ cons₁ X n x xs ≡ cons₁ X n y ys , nil

ΔHOUnification₁ : (X : Set) → Telescope 8 
ΔHOUnification₁ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₁ ∈ (suc₁ n , tt) ≡ (suc₁ n , tt) ,
            p ∈ e₁ ≡ refl ,
            e ∈ subst (μ (VecD X)) e₁ (cons₁ X n x xs) ≡ cons₁ X n y ys , nil

ΔHOUnification₂ : (X : Set) → Telescope 8 
ΔHOUnification₂ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₁ ∈ (suc₁ n , tt) ≡ (suc₁ n , tt) ,
            e ∈ subst (μ (VecD X)) e₁ (cons₁ X n x xs) ≡ cons₁ X n y ys ,
            p ∈ e₁ ≡ refl , nil

ΔHOUnification₃ : (X : Set) → Telescope 9
ΔHOUnification₃ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
    e₁ ∈ n ≡ n , 
    e₂ ∈ proj₁ (subst (λ n' →
            ⟦ Σ' X (λ x₂ → ×' (n' , tt) (one' (suc' n' , tt))) ⟧c (μ (VecD X))
                (suc₁ n , tt)) 
                    e₁ (x , xs , refl {x = (suc' n) , tt})) ≡ y , 
    e₃ ∈ proj₁ (subst (λ x → ⟦ ×' (proj₁ 
            (subst (λ x₁ →  ⟦ snd (VecD X x₁) ⟧c (μ (VecD X))
                (suc₁ n , tt)) (sym (refl {x = f1})) (n , y , ys , refl {x = (suc' n) , tt})) , tt)
            (one' (suc' (proj₁ (subst (λ x₁ → 
                ⟦ snd (VecD X x₁) ⟧c (μ (VecD X)) (suc₁ n , tt))
                    (sym (refl {x = f1})) (n , y , ys , refl {x = (suc' n) , tt}))) , tt)) ⟧c
            (μ (VecD X)) (suc₁ n , tt))
        e₂ (snd (subst (λ x → ⟦ Σ' X (λ x₁ → ×' (x , tt) (one' (suc' x , tt))) ⟧c (μ (VecD X))
            (suc₁ n , tt))
        e₁ (x , xs , refl {x = (suc' n) , tt}))))
            ≡ proj₁ (snd (snd (subst (λ x → ⟦ snd (VecD X x) ⟧c (μ (VecD X)) (suc₁ n , tt))
            (sym (refl {x = f1})) (n , y , ys , refl {x = (suc' n) , tt})))) , 
    p ∈ linvΣ₁ (injectivity'K (cons₁ X n x xs ) (cons₁ X n y ys ) refl (e₁ , e₂ , e₃ , tt))
            ≡ refl , 
    nil


ΔHOUnification₄ : (X : Set) → Telescope 9
ΔHOUnification₄ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₁ ∈ n ≡ n , 
            p  ∈ cong (λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ ,
            e₂ ∈ x ≡ y , 
            e₃ ∈ subst (λ n → μ (VecD X) (n , tt)) e₁ xs ≡ ys , nil



ΔHOUnification₅ₗ : (X : Set)(n : μ NatD tt) → Telescope 2
ΔHOUnification₅ₗ X n = w ∈ μ NatD tt , p ∈ (_,_ {B = λ x₁ → ⊤} (suc₁ w) tt) ≡ (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt) , nil

HOUnify₅ₗ : (X : Set)(n : μ NatD tt) → Unification (ΔHOUnification₅ₗ X n)
HOUnify₅ₗ X n = USplitΣ (λ w → _,_ {B = λ x₁ → ⊤} (suc₁ w) tt) (λ w → _,_ {B = λ x₁ → ⊤} (suc₁ n) tt) (there λ w → here w) 
    (UInjectivity₁ {x₁ = λ where (n , w) → suc₁ w } {x₂ = λ where (n , w) → suc₁ n } 
        (there λ w → here (n , w)) (λ _ → refl) (λ _ → refl) 
        (Usolution₁ {X = ⊤} (here (tt , n)) 
            (UAddRule₁ (here tt) nil (λ _ → injectivity⊤) (λ _ → injectivity⊤') (λ _ → injectivity⊤'∘injectivity⊤) 
                (UEnd nil)))) 

ΔHOUnification₅ : (X : Set) → Telescope 9
ΔHOUnification₅ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₁ ∈ (n , tt) ≡ (n , tt) , 
            p  ∈ cong (λ ntt → (_,_ {B = λ x₁ → ⊤} (suc₁ (proj₁ ntt)) tt)) e₁ ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ ,
            e₂ ∈ x ≡ y , 
            e₃ ∈ subst (μ (VecD X)) e₁ xs ≡ ys , nil

ΔHOUnification₄' : (X : Set) → Telescope 9
ΔHOUnification₄' X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₁ ∈ (n , tt) ≡ (n , tt) , 
            p  ∈ cong (λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) (cong proj₁ e₁) ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) (cong proj₁ e₁) ,
            e₂ ∈ x ≡ y , 
            e₃ ∈ subst (λ n → μ (VecD X) (n , tt)) (cong proj₁ e₁) xs ≡ ys , nil


ΔHOUnification₆ : (X : Set) → Telescope 7
ΔHOUnification₆ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₂ ∈ x ≡ y , e₃ ∈ xs ≡ ys , nil

ΔHOUnification₇ : (X : Set) → Telescope 3
ΔHOUnification₇ X = n ∈ μ NatD tt , x ∈ X , xs ∈ μ (VecD X) (n , tt) , nil

HOUnify₆ : (X : Set) → Unification (ΔHOUnification₆ X)
HOUnify₆ X = UReorder f3 f0 (λ _ → _ , there λ xs → there λ ys → here tt) 
                (Usolution (there λ n → there λ x → here (tt , x)) 
                    (Usolution (there λ n → there λ x → there λ xs → here (n , xs)) 
                        (UEnd (ΔHOUnification₇ X))))


HOUnify₅ : (X : Set) → Unification (ΔHOUnification₅ X)
HOUnify₅ X = UAddRule₂ (there λ n → there λ x → there λ y → there λ xs → there λ ys → here n) 
    (e ∈ tt ≡ tt , nil) (λ x e → HOUnification (λ ntt → suc₁ (proj₁ ntt) , tt) (λ _ → suc₁ x , tt) id (HOUnify₅ₗ X x) (x , tt) (x , tt) refl refl e , tt) 
        (λ x xs → HOUnification' (λ ntt → suc₁ (proj₁ ntt) , tt) (λ _ → suc₁ x , tt) id (HOUnify₅ₗ X x) (x , tt) (x , tt) refl refl (proj₁ xs)) 
        (λ x e → HOUnification'∘HOUnification (λ ntt → suc₁ (proj₁ ntt) , tt) (λ _ → suc₁ x , tt) id (HOUnify₅ₗ X x) (x , tt) (x , tt) refl refl e) 
    (UAddRule₁ (there λ n → there λ x → there λ y → there λ xs → there λ ys → here tt) nil 
        (λ _ → injectivity⊤) (λ _ → injectivity⊤') (λ _ → injectivity⊤'∘injectivity⊤) 
            (HOUnify₆ X))  

HOUnify₄' : (X : Set) → Unification (ΔHOUnification₄' X)
HOUnify₄' X = {!   !}

HOUnify₄ : (X : Set) → Unification (ΔHOUnification₄ X)
HOUnify₄ X = UCombineΣ (λ n → n) (λ n → n) (there λ n → there λ x → there λ y → there λ xs → there λ ys → here n) 
    (HOUnify₄' X) 
    
HOUnify₃ : (X : Set) → Unification (ΔHOUnification₃ X)
HOUnify₃ X = UReplaceElem {Y₂ = λ where (n , x , xs , e₁ , y) → x ≡ y} (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
                → here (n , x , xs , e₁ , y))  (λ where 
                    (n , x , xs , refl , y) → refl) 
                (UReplaceElem {Y₂ = λ where (n , x , xs , y , ys , e₁ , e₂) → subst (λ n → μ (VecD X) (n , tt)) e₁ xs ≡ ys} 
                    (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
                    → there λ e₂ → here (n , x , xs , y , ys , e₁ , e₂)) (λ where 
                        (n , x , xs , y , ys , refl , refl) → refl)
                    (UReplaceElem {Y₂ = λ { (n , x , xs , y , ys , e₁ , e₂ , e₃) → cong (λ n → (suc₁ n , tt)) e₁ ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ }} 
                        (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
                            → there λ e₂ → there λ e₃ → here (n , x , xs , y , ys , e₁ , e₂ , e₃)) 
                        (λ where (n , x , xs , y , ys , refl , refl , refl) → refl)
                    (UReorder f6 f0 (λ x → _ , there λ e₂ → there λ e₃ → here tt) 
                        (HOUnify₄ X))))

HOUnify₂ : (X : Set) → Unification (ΔHOUnification₂ X)
HOUnify₂ X = UInjectivity 
    {X = Σ[ n ∈ μ NatD tt ] (Σ[ x ∈ X ] (Σ[ xs ∈ μ (VecD X) (n , tt) ] (Σ[ y ∈ X ] (μ (VecD X) (n , tt)))))} 
    {d₁ = λ where (n , x , xs , y , ys) → (suc₁ n , tt)}
    {d₂ = λ where (n , x , xs , y , ys) → (suc₁ n , tt)}
    {x₁ = λ where (n , x , xs , y , ys) → cons₁ X n x xs}
    {x₂ = λ where (n , x , xs , y , ys) → cons₁ X n y ys}
    (there λ n → there λ x → there λ y → there λ xs → there λ ys 
        → here (n , x , xs , y , ys)) 
    (λ x → refl) (λ x → refl) 
    (HOUnify₃ X)

HOUnify₁ : (X : Set) → Unification (ΔHOUnification₁ X)
HOUnify₁ X = UReorder f6 f0 (λ x → _ , (there λ p → here tt)) 
                (HOUnify₂ X)


HOUnify : (X : Set) → Unification (ΔHOUnification X)
HOUnify X = U←Solution (μ (VecD X)) (λ where (n , x , y , xs , ys) → (suc₁ n , tt)) 
                {s = λ where (n , x , y , xs , ys) → cons₁ X n x xs}
                {t = λ where (n , x , y , xs , ys) → cons₁ X n y ys}
                (there λ n → there λ x → there λ y → there λ xs → there λ ys → here (n , x , y , xs , ys)) 
                (HOUnify₁ X)   