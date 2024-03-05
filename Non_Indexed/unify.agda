{-# OPTIONS --allow-unsolved-metas #-}
module Non_Indexed.unify where

open import Non_Indexed.datatypes
open import Non_Indexed.telescope
open import Non_Indexed.unification

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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Vec using (Vec; []; _∷_)

data Unification : {i : ℕ} (Δ : Telescope i) → Set₁ where 
    UEnd : {i : ℕ} (Δ : Telescope i) → Unification Δ
    Usolution :  {i : ℕ} {Δ : Telescope i} {X : Set} {j : ℕ}
        → (p : Δ [ j ]∶[ X ][ X ] (λ t x → t ≡ x))
        → Unification (doSolutionTel p)
        → Unification Δ
    Usolution' :  {i : ℕ} {Δ : Telescope i} {X : Set} {j : ℕ}
        → (p : Δ [ j ]∶[ X ][ X ] (λ t x → x ≡ t))
        → Unification (doSolutionTel' p)
        → Unification Δ
    UDeletion : {i : ℕ} {Δ : Telescope i} {X : Set} 
        → {t : X} {j : ℕ} (p : Δ [ j ]∶Σ[ ⊤ ] (λ _ → t ≡ t))
        → Unification (doDeletionTel p)
        → Unification Δ
    UInjectivity : {i j k : ℕ} {Δ : Telescope i} {D : DataDesc j}{D' : Set}
        → {s t : D' → μ D} (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
        → (e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d))
        → {n : ℕ}(eℕ : (d : D') → conₙ (s d) ≡ n)
        → Unification (doInjectivityTel e' eℕ p)
        → Unification Δ
    UConflict : {i j : ℕ} {Δ : Telescope i} {D : DataDesc j}{D' : Set}
        → {s t : D' → μ D} {x : ℕ} (p : Δ [ x ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
        → (e' : (d : D') → ¬ (conᵢ (s d) ≡ conᵢ (t d)))
        → Unification (doConflictTel p e')
        → Unification Δ

    UReorder : {i j : ℕ} {Δ : Telescope i} (split : Fin i) (goal : Fin j)
        → (p : (x : ⟦ proj₁ (splitTel Δ split) ⟧telD) 
            → (Σ[ X ∈ Set ] ((proj₂ (splitTel Δ split)) x) [ j ]∶ X))
        → Unification (reorderTel split Δ goal p) 
        → Unification Δ

unifyTel : {i : ℕ} {Δ : Telescope i} (u : Unification Δ) 
    → Σ ℕ Telescope
unifyTel (UEnd Δ) = _ , Δ
unifyTel (Usolution p u) = unifyTel u
unifyTel (Usolution' p u) = unifyTel u
unifyTel (UDeletion p u) = unifyTel u
unifyTel (UInjectivity p e' eℕ u) = unifyTel u
unifyTel (UConflict p e' u) = unifyTel u
unifyTel (UReorder split goal p u) = unifyTel u

unify : {i : ℕ} {Δ : Telescope i} (u : Unification Δ) (xs : ⟦ Δ ⟧telD)
    → ⟦ proj₂ (unifyTel u) ⟧telD
unify (UEnd _) xs = xs
unify (Usolution p u) xs = unify u (doSolution p xs)
unify (Usolution' p u) xs = unify u (doSolution' p xs)
unify (UDeletion p u) xs = unify u (doDeletion p xs)
unify (UInjectivity p e' eℕ u) xs = unify u (doInjectivity e' eℕ p xs)
unify (UConflict p e' u) xs = unify u (doConflict p e' xs)
unify (UReorder split goal p u) xs = unify u (reorder split goal p xs)

linvUnify : {i : ℕ} {Δ : Telescope i} (u : Unification Δ) (xs : ⟦ proj₂ (unifyTel u) ⟧telD)
    → ⟦ Δ ⟧telD
linvUnify (UEnd _) xs = xs
linvUnify (Usolution p u) xs = linvDoSolution p (linvUnify u xs)
linvUnify (Usolution' p u) xs = linvDoSolution' p (linvUnify u xs)
linvUnify (UDeletion p u) xs = linvDoDeletion p (linvUnify u xs)
linvUnify (UInjectivity p e' eℕ u) xs = linvDoInjectivity e' eℕ p (linvUnify u xs)
linvUnify (UConflict p e' u) xs = linvDoConflict p e' (linvUnify u xs)
linvUnify (UReorder split goal p u) xs = linvReorder split goal p (linvUnify u xs)

isLinvUnify : {i : ℕ} {Δ : Telescope i} (u : Unification Δ) (xs : ⟦ Δ ⟧telD)
    → linvUnify u (unify u xs) ≡ xs
isLinvUnify (UEnd _) xs = refl
isLinvUnify (Usolution p u) xs = subst (λ xs' → linvDoSolution p xs' ≡ xs) (sym (isLinvUnify u (doSolution p xs))) (isLinvDoSolution p xs)
isLinvUnify (Usolution' p u) xs = subst (λ xs' → linvDoSolution' p xs' ≡ xs) (sym (isLinvUnify u (doSolution' p xs))) (isLinvDoSolution' p xs)
isLinvUnify (UDeletion p u) xs = subst (λ xs' → linvDoDeletion p xs' ≡ xs) (sym (isLinvUnify u (doDeletion p xs))) (isLinvDoDeletion p xs)
isLinvUnify (UInjectivity p e' eℕ u) xs = subst (λ xs' → linvDoInjectivity e' eℕ p xs' ≡ xs) (sym (isLinvUnify u (doInjectivity e' eℕ p xs))) (isLinvDoInjectivity e' eℕ p xs)
isLinvUnify (UConflict p e' u) xs = subst (λ xs' → linvDoConflict p e' xs' ≡ xs) (sym (isLinvUnify u (doConflict p e' xs))) (isLinvDoConflict p e' xs)
isLinvUnify (UReorder split goal p u) xs = subst (λ xs' → linvReorder split goal p xs' ≡ xs) (sym (isLinvUnify u (reorder split goal p xs))) (isLinvReorder split goal p xs)

















