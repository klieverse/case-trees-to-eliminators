{-# OPTIONS --allow-unsolved-metas #-}
module Non_Indexed.translation where 

open import Non_Indexed.datatypes
open import Non_Indexed.telescope 
open import Non_Indexed.casetrees

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Data.Unit.Base
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
eval {ℓ} {Δ = Δ} {T} (node {D = D} i f) t = case-μ D (λ x → proj₂ (t Σ[ i ]) ≡ x → T t) cs (proj₂ (t Σ[ i ])) refl where 

    cs : (x : ⟦ D ⟧ (μ D)) → proj₂ (t Σ[ i ]) ≡ ⟨ x ⟩ → T t
    cs (k , x) e = shrinkExpand i (conToTel x) p T t (cong (tt ,_) e) r where 

        p : ⟨ k , telToCon (conToTel x) ⟩ ≡ ⟨ k , x ⟩
        p = cong (λ x → ⟨ k , x ⟩) (telToCon∘conToTel x)

        r : expandSort i T (expand i (conToTel x) p t (cong (tt ,_) e))
        r = eval (f k) _


