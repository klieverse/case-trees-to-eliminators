{-# OPTIONS --safe #-}
module Indexed.HDUnification where
    
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

private variable
  n m : ℕ
  Δ : Telescope n


-- allow to remove tt ≡ tt from telescope without K
injectivity⊤ : (e : tt ≡ tt) → ⊤
injectivity⊤ e = tt

injectivity⊤' : ⊤ → tt ≡ tt
injectivity⊤' e = refl

injectivity⊤'∘injectivity⊤ : (e : tt ≡ tt)
    → injectivity⊤' (injectivity⊤ e) ≡ e 
injectivity⊤'∘injectivity⊤ e = J (λ _ e → injectivity⊤' (injectivity⊤ e) ≡ e) refl e 

-- xs ≡ ys ≃ unify u xs ≡ unify u ys
unifyxs : (u : Unification Δ) (xs ys : ⟦ Δ ⟧telD)
  → xs ≡ ys → unify u xs ≡ unify u ys 
unifyxs u xs ys e = cong (unify u) e

unifyxs' : (u : Unification Δ) (xs ys : ⟦ Δ ⟧telD)
  → unify u xs ≡ unify u ys → xs ≡ ys
unifyxs' u xs ys e = subst (λ e → e ≡ ys) (unify'∘unify u xs) 
  (subst (λ e → unify' u (unify u xs) ≡ e) (unify'∘unify u ys) 
      (cong (unify' u) e)) 

unifyxs'∘unifyxs : {n : ℕ}{Δ : Telescope n} (u : Unification Δ) (xs ys : ⟦ Δ ⟧telD)
  → (e : xs ≡ ys) → unifyxs' u xs ys (unifyxs u xs ys e) ≡ e 
unifyxs'∘unifyxs u xs ys e = subst∘subst e (unify u) (unify' u) (unify'∘unify u) 

-- (x₁ , y₁) ≡ (x₂ , y₂) ≃ merge x₁ y₁ ≡ merge x₂ y₂
mergexs : {X : Telescope n} {S : Set} {Y : S → Telescope m}
    {f : ⟦ X ⟧telD → S}
  → (x₁ x₂ : ⟦ X ⟧telD) (y₁ : ⟦ Y (f x₁) ⟧telD) (y₂ : ⟦ Y (f x₂) ⟧telD)
  → (x₁ , y₁) ≡ (x₂ , y₂) 
  → merge {X = X} {Y = Y} {f = f} x₁ y₁ ≡ merge x₂ y₂
mergexs x₁ x₂ y₁ y₂ e = cong (λ x → merge (proj₁ x) (snd x)) e 

mergexs' : {X : Telescope n} {S : Set} {Y : S → Telescope m}
    {f : ⟦ X ⟧telD → S}
  → (x₁ x₂ : ⟦ X ⟧telD) (y₁ : ⟦ Y (f x₁) ⟧telD) (y₂ : ⟦ Y (f x₂) ⟧telD)
  → merge {X = X} {Y = Y} {f = f} x₁ y₁ ≡ merge x₂ y₂
  → (x₁ , y₁) ≡ (x₂ , y₂) 
mergexs' {X = X} {S} {Y} {f} x₁ x₂ y₁ y₂ e = subst (λ e → e ≡ (x₂ , y₂)) (sym (mproj∘merge {X = X} {Y = Y} {f = f} x₁ y₁)) 
  (subst (λ e → (mproj₁ (merge {X = X} {Y = Y} {f = f} x₁ y₁) , 
          mproj₂ {X = X} {Y = Y} {f = f} (merge {X = X} {Y = Y} {f = f} x₁ y₁)) ≡ e) (sym (mproj∘merge {X = X} {Y = Y} {f = f} x₂ y₂)) (cong (λ x → (mproj₁ x , mproj₂ {X = X} {Y = Y} {f = f} x)) e))

mergexs'∘mergexs : {X : Telescope n} {S : Set} {Y : S → Telescope m}
    {f : ⟦ X ⟧telD → S}
  → (x₁ x₂ : ⟦ X ⟧telD) (y₁ : ⟦ Y (f x₁) ⟧telD) (y₂ : ⟦ Y (f x₂) ⟧telD)
  → (e : (x₁ , y₁) ≡ (x₂ , y₂))
  → mergexs' {Y = Y} {f = f} x₁ x₂ y₁ y₂ (mergexs {Y = Y} {f = f} x₁ x₂ y₁ y₂ e) ≡ e
mergexs'∘mergexs {X = X} {S} {Y} {f} x₁ x₂ y₁ y₂ e = subst∘subst e (λ a → merge {X = X} {Y = Y} {f = f} (proj₁ a) (proj₂ a)) (λ x → (mproj₁ x , mproj₂ {X = X} {Y = Y} {f = f} x))
  (λ a → sym (mproj∘merge {X = X} {Y = Y} {f = f} (proj₁ a) (proj₂ a))) 


-- (e : u ≡ v)(p : r ≡ s) ≃ unify f (u , r) ≡ unify f (v , s)
HDUnification₁ : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → Σ[ e ∈ u ≡ v ] (subst (λ v₁ → a (f' v₁) ≡ b (f' v₁)) e r ≡ s)
    → unify f (merge u (r , tt)) ≡ unify f (merge v (s , tt))
HDUnification₁ a b f' f u v r s (e , xs) = unifyxs f (merge u (r , tt)) (merge v (s , tt)) 
  (mergexs u v (r , tt) (s , tt) (cong (λ x → (proj₁ x , proj₂ x , tt)) (Σ-create e xs)))

HDUnification₁' : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → unify f (merge u (r , tt)) ≡ unify f (merge v (s , tt))
    → Σ[ e ∈ u ≡ v ] (subst (λ v₁ → a (f' v₁) ≡ b (f' v₁)) e r ≡ s)
HDUnification₁' {Δ = Δ} a b f' f u v r s e = linvΣ₁ ex , linvΣ₂ ex where 

  ex : (u , r) ≡ (v , s) 
  ex = cong (λ x → proj₁ x , proj₁ (snd x)) (mergexs' u v (r , tt) (s , tt) (unifyxs' f (merge u (r , tt)) (merge v (s , tt)) e))
   
HDUnification₁'∘HDUnification₁' : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → (ex : Σ[ e ∈ u ≡ v ] (subst (λ v₁ → a (f' v₁) ≡ b (f' v₁)) e r ≡ s)) 
    → HDUnification₁' {Δ = Δ} a b f' f u v r s (HDUnification₁ a b f' f u v r s ex) ≡ ex 
HDUnification₁'∘HDUnification₁'  {Δ = Δ} a b f' f u v r s (e , xs) = goal where 
  
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


HDUnification : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → Σ[ e ∈ u ≡ v ] (subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e) 
    → unify f (merge u (r , tt)) ≡ unify f (merge v (s , tt))
HDUnification a b f' f u v r s (e , xs) = HDUnification₁ a b f' f u v r s (e , cong→subst id (λ x → a (f' x) ≡ b (f' x)) e r s 
    (×-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs))) 
    
HDUnification' : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → unify f (merge {X = Δ} {Y = (λ x → (p ∈ a x ≡ b x , nil))} {f = f'} u (r , tt)) ≡ unify f (merge v (s , tt))
    → Σ[ e ∈ u ≡ v ] (subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e) 
HDUnification' {Δ = Δ} a b f' f u v r s e = e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s 
  (×-cong→create e' r s (subst→cong id (λ x → a (f' x) ≡ b (f' x)) e' r s xs')) where  

    e' : u ≡ v 
    e' = proj₁ (HDUnification₁' a b f' f u v r s e)

    xs' : subst (λ v₁ → a (f' v₁) ≡ b (f' v₁)) e' r ≡ s
    xs' = proj₂ (HDUnification₁' a b f' f u v r s e)

HDUnification'∘HDUnification : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → (e : Σ[ e ∈ u ≡ v ] (subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e))
    → HDUnification' a b f' f u v r s (HDUnification a b f' f u v r s e) ≡ e
HDUnification'∘HDUnification {Δ = Δ} {X} {Y} a b f' f u v r s (e , xs) = goal where 

  e' : u ≡ v 
  e' = e

  xs' : subst (λ v₁ → a (f' v₁) ≡ b (f' v₁)) e' r ≡ s
  xs' = cong→subst id (λ x → a (f' x) ≡ b (f' x)) e r s 
    (×-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs))

  goal₃ : (e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s 
    (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs)) ≡ (e , xs)
  goal₃ = subst (λ e₁ → (e' , e₁) ≡ (e , xs)) (sym (flipSquare∘flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs)) refl

  goal₂ : (e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s 
    (×-cong→create {a = λ xs → a (f' xs)} {b = λ xs → b (f' xs)} {f' = id} e' r s (×-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs)))) ≡ (e , xs)
  goal₂ = subst (λ e₁ → (e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s  e₁) ≡ (e , xs)) 
            (sym (×-cong→create∘×-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs))) goal₃

  goal₁ : (e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s 
    (×-cong→create e' r s (subst→cong id (λ x → a (f' x) ≡ b (f' x)) e' r s (cong→subst id (λ x → a (f' x) ≡ b (f' x)) e r s 
    (×-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs)))))) ≡ (e , xs)
  goal₁ = subst (λ e₁ → (e' , flipSquare (cong (λ xs → a (f' xs)) e') (cong (λ xs → b (f' xs)) e') r s 
    (×-cong→create e' r s e₁)) ≡ (e , xs)) (sym (subst→cong∘cong→subst {f = id} {P = λ x → a (f' x) ≡ b (f' x)} e r s (×-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs)))) goal₂

  goal : (proj₁ (HDUnification₁' a b f' f u v r s (HDUnification₁ a b f' f u v r s (e' , xs'))) , 
    flipSquare (cong (λ xs → a (f' xs)) (proj₁ (HDUnification₁' a b f' f u v r s (HDUnification₁ a b f' f u v r s (e' , xs'))))) (cong (λ xs → b (f' xs)) (proj₁ (HDUnification₁' a b f' f u v r s (HDUnification₁ a b f' f u v r s (e' , xs'))))) r s 
    (×-cong→create (proj₁ (HDUnification₁' a b f' f u v r s (HDUnification₁ a b f' f u v r s (e' , xs')))) r s (subst→cong id (λ x → a (f' x) ≡ b (f' x)) (proj₁ (HDUnification₁' a b f' f u v r s (HDUnification₁ a b f' f u v r s (e' , xs')))) r s (proj₂ (HDUnification₁' a b f' f u v r s (HDUnification₁ a b f' f u v r s (e' , xs'))))))
    ) ≡ (e , xs)
  goal = subst (λ e₁ → (proj₁ e₁ , 
    flipSquare (cong (λ xs → a (f' xs)) (proj₁ e₁)) (cong (λ xs → b (f' xs)) (proj₁ e₁)) r s 
    (×-cong→create (proj₁ e₁) r s (subst→cong id (λ x → a (f' x) ≡ b (f' x)) (proj₁ e₁) r s (proj₂ e₁)))
    ) ≡ (e , xs)) (sym (HDUnification₁'∘HDUnification₁' a b f' f u v r s (e' , xs'))) goal₁



pConv : {n : μ NatD tt}(e₁ : (n , tt) ≡ (n , tt))
  → cong (λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) (cong proj₁ e₁) ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) (cong proj₁ e₁)
  → cong (λ ntt → (_,_ {B = λ x₁ → ⊤} (suc₁ (proj₁ ntt)) tt)) e₁ ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁
pConv {n} e₁ e = cong∘cong→cong {a = λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)} {b = λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)} {f' = proj₁} e₁ refl refl e

pConv' : {n : μ NatD tt}(e₁ : (n , tt) ≡ (n , tt))
  → cong (λ ntt → (_,_ {B = λ x₁ → ⊤} (suc₁ (proj₁ ntt)) tt)) e₁ ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁
  → cong (λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) (cong proj₁ e₁) ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) (cong proj₁ e₁)
pConv' {n} e₁ e = cong→cong∘cong {a = λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)} {b = λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)} {f' = proj₁} e₁ refl refl e

pConv'∘pConv : {n : μ NatD tt}(e₁ : (n , tt) ≡ (n , tt))
  → (e : cong (λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) (cong proj₁ e₁) ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) (cong proj₁ e₁))
  → pConv' e₁ (pConv e₁ e) ≡ e
pConv'∘pConv {n} e₁ e = cong→cong∘cong∘cong∘cong→cong {a = λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)} {b = λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)} {f' = proj₁} e₁ refl refl e




e₃Conv : {X : Set}{n m : μ NatD tt}{xs : μ (VecD X) (n , tt)}{ys : μ (VecD X) (m , tt)}(e₁ : (n , tt) ≡ (m , tt))
  → subst (λ n → μ (VecD X) (n , tt)) (cong proj₁ e₁) xs ≡ ys → subst (μ (VecD X)) e₁ xs ≡ ys
e₃Conv {X} {n} {m} {xs} {ys} e₁ e = J (λ mt e₁ → (ys : μ (VecD X) mt) → subst (λ n → μ (VecD X) (n , tt)) (cong proj₁ e₁) xs ≡ ys → subst (μ (VecD X)) e₁ xs ≡ ys) 
  (λ _ e → e) e₁ ys e

e₃Conv' : {X : Set}{n m : μ NatD tt}{xs : μ (VecD X) (n , tt)}{ys : μ (VecD X) (m , tt)}(e₁ : (n , tt) ≡ (m , tt))
  → subst (μ (VecD X)) e₁ xs ≡ ys → subst (λ n → μ (VecD X) (n , tt)) (cong proj₁ e₁) xs ≡ ys
e₃Conv' {X} {n} {m} {xs} {ys} e₁ e = J (λ mt e₁ → (ys : μ (VecD X) mt) → subst (μ (VecD X)) e₁ xs ≡ ys → subst (λ n → μ (VecD X) (n , tt)) (cong proj₁ e₁) xs ≡ ys) 
  (λ _ e → e) e₁ ys e

e₃Conv'∘e₃Conv : {X : Set}{n m : μ NatD tt}{xs : μ (VecD X) (n , tt)}{ys : μ (VecD X) (m , tt)}(e₁ : (n , tt) ≡ (m , tt))
  → (e : subst (λ n → μ (VecD X) (n , tt)) (cong proj₁ e₁) xs ≡ ys)
  → e₃Conv' e₁ (e₃Conv e₁ e) ≡ e
e₃Conv'∘e₃Conv {X} {n} {m} {xs} {ys} e₁ e = J (λ mt e₁ → (ys : μ (VecD X) mt) → (e : subst (λ n → μ (VecD X) (n , tt)) (cong proj₁ e₁) xs ≡ ys)
  → e₃Conv' e₁ (e₃Conv e₁ e) ≡ e) (λ _ _ → refl) e₁ ys e


-- Higher Dimensional Unification Example: 
-- (n : μ NatD tt)(x y : X)(xs ys : μ (VecD X) (n , tt)) (e : cons n x xs ≡ cons n y ys) 
--    ≃ (n : μ NatD tt) (x : X) (xs : μ (VecD X) (n , tt))

-- Step 1: Generalizing the Indices
ΔHDUnification₁ : (X : Set) → Telescope 6 
ΔHDUnification₁ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
  e ∈ cons₁ X n x xs ≡ cons₁ X n y ys , nil

-- Step 2: Injectivity Rule
ΔHDUnification₂ : (X : Set) → Telescope 8 
ΔHDUnification₂ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
  e₁ ∈ (suc₁ n , tt) ≡ (suc₁ n , tt) , e ∈ subst (μ (VecD X)) e₁ (cons₁ X n x xs) ≡ cons₁ X n y ys ,
  p ∈ e₁ ≡ refl , nil

-- Step 3: Lowering the Dimension of the Equations
ΔLUnification : (X : Set)(n : μ NatD tt) → Telescope 2
ΔLUnification X n = w ∈ μ NatD tt , p ∈ (_,_ {B = λ x₁ → ⊤} (suc₁ w) tt) ≡ (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt) , nil

-- Step 4: Lifting Unifiers to a Higher Dimension
ΔHDUnification₄ : (X : Set) → Telescope 9
ΔHDUnification₄ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
  e₁ ∈ n ≡ n , p ∈ cong (λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ ,
  e₂ ∈ x ≡ y , e₃ ∈ subst (λ n → μ (VecD X) (n , tt)) e₁ xs ≡ ys , nil

-- Step 5: Solving with Solution
ΔHDUnification₅ : (X : Set) → Telescope 7
ΔHDUnification₅ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
  e₂ ∈ x ≡ y , e₃ ∈ xs ≡ ys , nil

-- Result:
ΔHDUnificationEnd : (X : Set) → Telescope 3
ΔHDUnificationEnd X = n ∈ μ NatD tt , x ∈ X , xs ∈ μ (VecD X) (n , tt) , nil


-- Step 5: Solving with Solution
-- (n : μ NatD tt)(x y : X)(xs ys : μ (VecD X) (n , tt))(e₂ : x ≡ y)(e₃ : xs ≡ y)
-- ≃
-- (n : μ NatD tt)(x : X)(xs : μ (VecD X) (n , tt))
HDUnify₅ : (X : Set) → Unification (ΔHDUnification₅ X)
HDUnify₅ X = UReorder f3 f0 (λ _ → _ , there λ xs → there λ ys → here tt) 
                (Usolution (there λ n → there λ x → here (tt , x)) 
                    (Usolution (there λ n → there λ x → there λ xs → here (n , xs)) 
                        (UEnd (ΔHDUnificationEnd X))))

-- Step 3: Lowering the Dimension of the Equations
-- (w : μ NatD tt)(p : (suc₁ w , tt) ≡ (suc₁ n , tt)) ≃ ()
LUnify : (X : Set)(n : μ NatD tt) → Unification (ΔLUnification X n)
LUnify X n 
    -- (w : μ NatD tt)(p : (suc₁ w , tt) ≡ (suc₁ n , tt)) ≃ (w : μ NatD tt)(p : suc₁ w ≡ suc₁ n) (p' : tt ≡ tt)
  = USplitΣ (λ w → _,_ {B = λ x₁ → ⊤} (suc₁ w) tt) (λ w → _,_ {B = λ x₁ → ⊤} (suc₁ n) tt) (there λ w → here w) 
    -- (w : μ NatD tt)(p : suc₁ w ≡ suc₁ n)(p' : tt ≡ tt) ≃ (w : μ NatD tt)(p : w ≡ n)(p' : tt ≡ tt)
    (UInjectivity₁ {x = λ where (n , w) → suc₁ w } {y = λ where (n , w) → suc₁ n } 
        (there λ w → here (n , w)) (λ _ → refl) (λ _ → refl) 
    -- (w : μ NatD tt)(p : w ≡ n)(p' : tt ≡ tt) ≃ (p' : tt ≡ tt)    
    (Usolution₁ {A = ⊤} (here (tt , n)) 
    -- (p' : tt ≡ tt) ≃ ()  
    (UAddRule₁ (here tt) (λ _ → nil) (λ _ → injectivity⊤) (λ _ → injectivity⊤') (λ _ → injectivity⊤'∘injectivity⊤) 
        (UEnd nil)))) 

-- Step 4: Lifting Unifiers to a Higher Dimension
-- (n : μ NatD tt)(x y : X)(xs ys : μ (VecD X) (n , tt))(e₁ : n ≡ n)
-- (p : cong (λ n → suc n , tt) e₁ ≡ cong (λ _ → suc n , tt) e₁)(e₂ : x ≡ y)(e₃ : subst (λ n → μ (VecD X) (n , tt)) e₁ xs ≡ ys)
-- ≃
-- (n : μ NatD tt)(x y : X)(xs ys : μ (VecD X) (n , tt))(e₂ : x ≡ y)(e₃ : xs ≡ y)
HDUnify₄ : (X : Set) → Unification (ΔHDUnification₄ X)
HDUnify₄ X = UCombineΣ (λ n → n) (λ n → n) (there λ n → there λ x → there λ y → there λ xs → there λ ys → here n) 
  (UAddRule₁ (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ → here (n , e₁)) 
    (λ where (n , e₁) → p ∈ cong (λ ntt → (_,_ {B = λ x₁ → ⊤} (suc₁ (proj₁ ntt)) tt)) e₁ ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ , nil) 
    (λ x p → pConv (proj₂ x) p , tt) (λ x p → pConv' (proj₂ x) (proj₁ p)) (λ x p → pConv'∘pConv (proj₂ x) p) 
  (UAddRule₁ (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ → there λ p → there λ e₂ → here (n , xs , ys , e₁)) 
    (λ where (n , xs , ys , e₁) → e₃ ∈ subst (μ (VecD X)) e₁ xs ≡ ys , nil) 
    (λ where (n , xs , ys , e₁) e₃ → e₃Conv e₁ e₃ , tt) 
    (λ where (n , xs , ys , e₁) (e₃ , tt) → e₃Conv' e₁ e₃) 
    (λ where (n , xs , ys , e₁) e₃ → e₃Conv'∘e₃Conv e₁ e₃) 
  (UAddRule₂ (there λ n → there λ x → there λ y → there λ xs → there λ ys → here n) 
    (λ _ → e ∈ tt ≡ tt , nil) (λ x e → HDUnification (λ ntt → suc₁ (proj₁ ntt) , tt) (λ _ → suc₁ x , tt) id (LUnify X x) (x , tt) (x , tt) refl refl e , tt) 
      (λ x xs → HDUnification' (λ ntt → suc₁ (proj₁ ntt) , tt) (λ _ → suc₁ x , tt) id (LUnify X x) (x , tt) (x , tt) refl refl (proj₁ xs)) 
      (λ x e → HDUnification'∘HDUnification (λ ntt → suc₁ (proj₁ ntt) , tt) (λ _ → suc₁ x , tt) id (LUnify X x) (x , tt) (x , tt) refl refl e) 
  (UAddRule₁ (there λ n → there λ x → there λ y → there λ xs → there λ ys → here tt) (λ _ → nil) 
    (λ _ → injectivity⊤) (λ _ → injectivity⊤') (λ _ → injectivity⊤'∘injectivity⊤) 
      (HDUnify₅ X))))) 


-- Step 2: The Injectivity Rule
-- (n : μ NatD tt)(x y : X)(xs ys : μ (VecD X) (n , tt))(e₁ : (suc₁ n , tt) ≡ (suc₁ n , tt))
-- (e : subst (μ (VecD X)) e₁ (cons n x xs) ≡ cons n y ys)(p : e₁ ≡ refl)
-- ≃
-- (n : μ NatD tt)(x y : X)(xs ys : μ (VecD X) (n , tt))(e₁ : n ≡ n)
-- (p : cong (λ n → suc n , tt) e₁ ≡ cong (λ _ → suc n , tt) e₁)(e₂ : x ≡ y)(e₃ : subst (λ n → μ (VecD X) (n , tt)) e₁ xs ≡ ys)
HDUnify₂ : (X : Set) → Unification (ΔHDUnification₂ X)
HDUnify₂ X = UInjectivity 
    {A = Σ[ n ∈ μ NatD tt ] (Σ[ x ∈ X ] (Σ[ xs ∈ μ (VecD X) (n , tt) ] (Σ[ y ∈ X ] (μ (VecD X) (n , tt)))))} 
    {d₁ = λ where (n , x , xs , y , ys) → (suc₁ n , tt)}
    {d₂ = λ where (n , x , xs , y , ys) → (suc₁ n , tt)}
    {x = λ where (n , x , xs , y , ys) → cons₁ X n x xs}
    {y = λ where (n , x , xs , y , ys) → cons₁ X n y ys}
    (there λ n → there λ x → there λ y → there λ xs → there λ ys 
        → here (n , x , xs , y , ys)) 
    (λ x → refl) (λ x → refl) 
    (UReplaceElem {B₂ = λ where (n , x , xs , e₁ , y) → x ≡ y} (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
        → here (n , x , xs , e₁ , y))  (λ where 
            (n , x , xs , refl , y) → refl) 
    (UReplaceElem {B₂ = λ where (n , x , xs , y , ys , e₁ , e₂) → subst (λ n → μ (VecD X) (n , tt)) e₁ xs ≡ ys} 
        (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
        → there λ e₂ → here (n , x , xs , y , ys , e₁ , e₂)) (λ where 
            (n , x , xs , y , ys , refl , refl) → refl)
    (UReplaceElem {B₂ = λ { (n , x , xs , y , ys , e₁ , e₂ , e₃) → cong (λ n → (suc₁ n , tt)) e₁ ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ }} 
        (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
            → there λ e₂ → there λ e₃ → here (n , x , xs , y , ys , e₁ , e₂ , e₃)) 
        (λ where (n , x , xs , y , ys , refl , refl , refl) → refl)
    (UReorder f6 f0 (λ x → _ , there λ e₂ → there λ e₃ → here tt) 
        (HDUnify₄ X)))))

-- Step 1: Generalizing the Indices
-- (n : μ NatD tt)(x y : X)(xs ys : μ (VecD X) (n , tt)) (e : cons n x xs ≡ cons n y ys) 
--    ≃ (n : μ NatD tt) (x : X) (xs : μ (VecD X) (n , tt))
HDUnify₁ : (X : Set) → Unification (ΔHDUnification₁ X)
HDUnify₁ X 
    -- (n : μ NatD tt)(x y : X)(xs ys : μ (VecD X) (n , tt))(e : cons n x xs ≡ cons n y ys) ≃ (n : μ NatD tt)(x y : X)(xs ys : μ (VecD X) (n , tt))
    -- (e₁ : (suc₁ n , tt) ≡ (suc₁ n , tt))(p : e₁ ≡ refl)(e : subst (μ (VecD X)) e₁ (cons n x xs) ≡ cons n y ys)
  = U←Solution (μ (VecD X)) (λ where (n , x , y , xs , ys) → (suc₁ n , tt)) 
      {x = λ where (n , x , y , xs , ys) → cons₁ X n x xs} {y = λ where (n , x , y , xs , ys) → cons₁ X n y ys}
      (there λ n → there λ x → there λ y → there λ xs → there λ ys → here (n , x , y , xs , ys)) 
    -- (n : μ NatD tt)(x y : X)(xs ys : μ (VecD X) (n , tt))(e₁ : (suc₁ n , tt) ≡ (suc₁ n , tt))
    -- (p : e₁ ≡ refl)(e : subst (μ (VecD X)) e₁ (cons n x xs) ≡ cons n y ys) 
    -- ≃
    -- (n : μ NatD tt)(x y : X)(xs ys : μ (VecD X) (n , tt))(e₁ : (suc₁ n , tt) ≡ (suc₁ n , tt))
    -- (e : subst (μ (VecD X)) e₁ (cons n x xs) ≡ cons n y ys)(p : e₁ ≡ refl)
    (UReorder f6 f0 (λ x → _ , (there λ p → here tt)) 
    (HDUnify₂ X))    
