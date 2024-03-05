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

eval : ∀{ℓ} {i : ℕ}{Δ : Telescope i}{T : ⟦ Δ ⟧telD → Set ℓ} → CaseTree Δ T → (t : ⟦ Δ ⟧telD) → T t 
eval (leaf f) t = f t
eval {ℓ} {Δ = Δ} {T} (node {IΔ = IΔ} {D = D} i f) t 
        = case-μ D (λ d x → (d , x) ≡ t Σ[ i ] → T t) cs (proj₁ (t Σ[ i ])) (proj₂ (t Σ[ i ])) refl where 

    cs : (d : ⟦ IΔ ⟧telD) (x : ⟦ D ⟧ (μ D) d) → (d , ⟨ x ⟩) ≡ (t Σ[ i ]) → T t
    cs d (k , x) e = shrinkExpand i (conToTel x) p T t (sym e) r where

            p : ⟨ k , telToCon (conToTel x) ⟩ ≡ ⟨ k , x ⟩
            p = cong (λ x → ⟨ k , x ⟩) (telToCon∘conToTel x)

            r : expandSort i T (expand i (conToTel x) p t (sym e))
            r = subst (expandSort i T) (isLinvUnify (proj₁ (f k)) (expand i (conToTel x) p t (sym e))) 
                    (eval (proj₂ (f k)) _)