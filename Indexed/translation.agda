{-# OPTIONS --allow-unsolved-metas #-}
module Indexed.translation where 

open import Non_Indexed.telescope
open import Indexed.datatypes
open import Indexed.casetrees
open import Indexed.unify

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
  ℓ   : Level
  n m : ℕ

eval : {Δ : Telescope n}{T : ⟦ Δ ⟧telD → Set ℓ} → 
  (ct : CaseTree Δ T) (args : ⟦ Δ ⟧telD) 
  → T args 
eval (leaf f) args = f args
eval {Δ = Δ} {T} (node {IΔ = IΔ} {D = D} p bs) args 
    = case-μ D (λ d' x' → (d' , x') ≡ (d , ret) → T args) cs d ret refl where 

  d : ⟦ IΔ ⟧telD 
  d = proj₁ (args Σ[ p ])

  -- value that we split on
  ret : μ D d 
  ret = proj₂ (args Σ[ p ])

  -- from a constructor instantiation that is equivalent to the value 
  -- that we split on get the return type
  cs : (d' : ⟦ IΔ ⟧telD) (x' : ⟦ D ⟧ (μ D) d') → (d' , ⟨ x' ⟩) ≡ (d , ret) → T args
  cs d' (k , xs) e = shrinkExpand p (conToTel xs) q T args (sym e) r where

    q : ⟨ k , telToCon (conToTel xs) ⟩ ≡ ⟨ k , xs ⟩
    q = cong (λ x → ⟨ k , x ⟩) (telToCon∘conToTel xs)

    -- recursively evaluate the case tree
    r : expandSort p T (expand p (conToTel xs) q args (sym e))
    r = subst (expandSort p T) (unify'∘unify (proj₁ (bs k)) (expand p (conToTel xs) q args (sym e))) 
          (eval (proj₂ (bs k)) _)


-- example translation Flip function
≡Flip : {A : Set} (w x y z : A) (t : μ (≡D w) (x , tt)) (b : μ (≡D y) (z , tt)) 
  → (l : μ (≡D w) (y , tt)) (r : μ (≡D x) (z , tt)) 
  → (s : μ (SquareD w) (x , y , z , t , b , l , r , tt))
  → {ret : μ (SquareD w) (y , x , z , l , r , t , b , tt)}
  → flip w x y z t b l r s ≡ ret 
  → eval (CTFlip w) (x , y , z , t , b , l , r , s , tt) ≡ ret
≡Flip w .w .w .w ⟨ fzero , refl ⟩ ⟨ fzero , refl  ⟩ ⟨ fzero , refl  ⟩ ⟨ fzero , refl ⟩ ⟨ fzero , refl ⟩ refl = refl
