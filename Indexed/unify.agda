{-# OPTIONS --allow-unsolved-metas #-}
module Indexed.unify where 

import Non_Indexed.datatypes as NI
open import Indexed.datatypes
open import Non_Indexed.telescope 
open import Non_Indexed.unification 
  using (doSolutionTel; doSolutionTel'; doSolution; doSolution'; linvDoSolution'; linvDoSolution; isLinvDoSolution; 
    isLinvDoSolution'; _[_]∶[_][_]_; doDeletionTel; doDeletion; linvDoDeletion; isLinvDoDeletion)
open import Indexed.unification

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
    UInjectivity :  {i j m x : ℕ} {Δ : Telescope i} {IΔ : Telescope m} {D : DataDesc j IΔ} {D' : Set}
        → {s t : D' → (d : ⟦ IΔ ⟧telD) → (μ D d)} (p : Δ [ x ]∶Σ[ Σ D' (λ _ → ⟦ IΔ ⟧telD) ] (λ d' → (s (proj₁ d') (proj₂ d')) ≡ (t (proj₁ d') (proj₂ d'))))
        → (e' : (d' : D') → (d : ⟦ IΔ ⟧telD) → (conᵢ (s d' d)) ≡ conᵢ (t d' d))
        → {n : ℕ}(eℕ : (d' : D') → (d : ⟦ IΔ ⟧telD) → (conₙ (s d' d) ≡ n))
        → Unification (doInjectivityTel eℕ p e')
        → Unification Δ
    UConflict : {i j m x : ℕ} {Δ : Telescope i} {IΔ : Telescope m} {D : DataDesc j IΔ} {D' : Set}
        → {s t : D' → (d : ⟦ IΔ ⟧telD) → (μ D d)} (p : Δ [ x ]∶Σ[ Σ D' (λ _ → ⟦ IΔ ⟧telD) ] (λ d' → (s (proj₁ d') (proj₂ d')) ≡ (t (proj₁ d') (proj₂ d'))))
        → (e' : (d' : D') → (d : ⟦ IΔ ⟧telD) → ¬ (conᵢ (s d' d)) ≡ conᵢ (t d' d))
        → Unification (doConflictTel p e')
        → Unification Δ
    UReorder : {i j : ℕ} {Δ : Telescope i} (split : Fin i) (goal : Fin j)
        → (p : (x : ⟦ proj₁ (splitTel Δ split) ⟧telD) → (Σ[ X ∈ Set ] ((proj₂ (splitTel Δ split)) x) [ j ]∶ X))
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
unify (UInjectivity p e' eℕ u) xs = unify u {!   !} -- (doInjectivity e' eℕ p xs)
unify (UConflict p e' u) xs = unify u (doConflict p e' xs)
unify (UReorder split goal p u) xs = unify u (reorder split goal p xs)

linvUnify : {i : ℕ} {Δ : Telescope i} (u : Unification Δ) (xs : ⟦ proj₂ (unifyTel u) ⟧telD)
    → ⟦ Δ ⟧telD
linvUnify (UEnd _) xs = xs
linvUnify (Usolution p u) xs = linvDoSolution p (linvUnify u xs)
linvUnify (Usolution' p u) xs = linvDoSolution' p (linvUnify u xs)
linvUnify (UDeletion p u) xs = linvDoDeletion p (linvUnify u xs)
linvUnify (UInjectivity p e' eℕ u) xs = {!   !} -- linvDoInjectivity e' eℕ p (linvUnify u xs)
linvUnify (UConflict p e' u) xs = {!   !} -- linvDoConflict p e' (linvUnify u xs)
linvUnify (UReorder split goal p u) xs = linvReorder split goal p (linvUnify u xs)

isLinvUnify : {i : ℕ} {Δ : Telescope i} (u : Unification Δ) (xs : ⟦ Δ ⟧telD)
    → linvUnify u (unify u xs) ≡ xs
isLinvUnify (UEnd _) xs = refl
isLinvUnify (Usolution p u) xs = subst (λ xs' → linvDoSolution p xs' ≡ xs) (sym (isLinvUnify u (doSolution p xs))) (isLinvDoSolution p xs)
isLinvUnify (Usolution' p u) xs = subst (λ xs' → linvDoSolution' p xs' ≡ xs) (sym (isLinvUnify u (doSolution' p xs))) (isLinvDoSolution' p xs)
isLinvUnify (UDeletion p u) xs = subst (λ xs' → linvDoDeletion p xs' ≡ xs) (sym (isLinvUnify u (doDeletion p xs))) (isLinvDoDeletion p xs)
isLinvUnify (UInjectivity p e' eℕ u) xs = {!   !} -- subst (λ xs' → linvDoInjectivity e' eℕ p xs' ≡ xs) (sym (isLinvUnify u (doInjectivity e' eℕ p xs))) (isLinvDoInjectivity e' eℕ p xs)
isLinvUnify (UConflict p e' u) xs = {!   !} -- subst (λ xs' → linvDoConflict p e' xs' ≡ xs) (sym (isLinvUnify u (doConflict p e' xs))) (isLinvDoConflict p e' xs)
isLinvUnify (UReorder split goal p u) xs = subst (λ xs' → linvReorder split goal p xs' ≡ xs) (sym (isLinvUnify u (reorder split goal p xs))) (isLinvReorder split goal p xs)
