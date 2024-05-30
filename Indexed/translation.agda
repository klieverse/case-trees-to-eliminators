{-# OPTIONS --allow-unsolved-metas #-}
module Indexed.translation where 

open import Non_Indexed.telescope
open import Indexed.datatypes
open import Indexed.casetrees
open import Indexed.unify
open import lib

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product 
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Data.Empty
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Agda.Builtin.String
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ<; fromℕ; toℕ; raise) renaming (zero to fzero; suc to fsuc)

private variable
  ℓ : Level
  n : ℕ

eval : {Δ : Telescope n}{T : ⟦ Δ ⟧telD → Set ℓ} → 
  (ct : CaseTree Δ T) (args : ⟦ Δ ⟧telD) 
  → T args 
eval (leaf f) args = f args
eval {Δ = Δ} {T} (node {is = is} {D = D} p bs) args 
    = case-μ D (λ d' x' → (d' , x') ≡ (d , ret) → T args) cs d ret refl where 

  d : ⟦ is ⟧telD 
  d = proj₁ (args Σ[ p ])

  -- value that we split on
  ret : μ D d 
  ret = proj₂ (args Σ[ p ])

  -- from a constructor instantiation that is equivalent to the value 
  -- that we split on get the return type
  cs : (d' : ⟦ is ⟧telD) (x : ⟦ D ⟧ (μ D) d') → (d' , ⟨ x ⟩) ≡ (d , ret) → T args
  cs d' (k , xs) e = subst T (subst (λ xs → shrink p xs ≡ args) (sym (unify'∘unify (proj₁ (bs k)) (expand p (λ ys → ⟨ k , telToCon ys ⟩) args
        (conToTel (subst (⟦ proj₂ (D k) ⟧c (μ D)) qd xs)) q))) (shrink∘expand p args _ q)) r where 
  
    qd : d' ≡ d 
    qd = cong proj₁ e

    q : ⟨ k , telToCon (conToTel (subst (⟦ proj₂ (D k) ⟧c (μ D)) qd xs)) ⟩ ≡ ret 
    q = J (λ dret e → ⟨ k , telToCon (conToTel (subst (⟦ proj₂ (D k) ⟧c (μ D)) (cong proj₁ e) xs)) ⟩ ≡ (proj₂ dret)) 
          (cong (λ x → ⟨ k , x ⟩) (telToCon∘conToTel xs)) e
    
    -- recursively evaluate the case tree
    r : T (shrink p (unify' (proj₁ (bs k)) (unify (proj₁ (bs k)) (expand p (λ ys → ⟨ k , telToCon ys ⟩) args
            (conToTel (subst (⟦ proj₂ (D k) ⟧c (μ D)) qd xs)) q)))) 
    r = eval (proj₂ (bs k)) (unify (proj₁ (bs k)) (expand p (λ ys → ⟨ k , telToCon ys ⟩) args 
        (conToTel (subst (⟦ proj₂ (D k) ⟧c (μ D)) qd xs)) q))



-- example translation Flip function
≡Flip : {A : Set} (w x y z : A) (t : μ (≡D w) (x , tt)) (b : μ (≡D y) (z , tt)) 
  → (l : μ (≡D w) (y , tt)) (r : μ (≡D x) (z , tt)) 
  → (s : μ (SquareD w) (x , y , z , t , b , l , r , tt))
  → {ret : μ (SquareD w) (y , x , z , l , r , t , b , tt)}
  → eval (CTFlip w) (x , y , z , t , b , l , r , s , tt) ≡ flip w x y z t b l r s
≡Flip w .w .w .w ⟨ f0 , refl ⟩ ⟨ f0 , refl  ⟩ ⟨ f0 , refl  ⟩ ⟨ f0 , refl ⟩ ⟨ f0 , refl ⟩ = refl
