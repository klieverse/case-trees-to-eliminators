{-# OPTIONS --allow-unsolved-metas #-}
module One_Indexed.unify where

open import Non_Indexed.datatypes as NI
open import One_Indexed.datatypes as OI
open import Non_Indexed.telescope
open import lib
open import One_Indexed.unification

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

private variable
  n m k : ℕ

data Unification : (Δ : Telescope n) → Set₁ where 
    -- end of unification
    UEnd : (Δ : Telescope n) → Unification Δ

    -- (x : X) (x ≡ t) ≃ ()
    Usolution :  {Δ : Telescope n} {X : Set} {A : X → Set}
        → (p : Δ [ k ]∶Σ[ Σ[ x ∈ X ] (A x) ] (λ xa → A (proj₁ xa)) ∶ (λ t x → (proj₂ t) ≡ x)) 
        → Unification (doSolutionTel p)
        → Unification Δ

    -- (x : X) (t ≡ x) ≃ ()
    Usolution₁ :  {Δ : Telescope n} {X : Set} {X : Set} {A : X → Set}
        → (p : Δ [ k ]∶Σ[ Σ[ x ∈ X ] (A x) ] (λ xa → A (proj₁ xa)) ∶ (λ t x → x ≡ (proj₂ t)))
        → Unification (doSolutionTel₁ p)
        → Unification Δ
    
    -- (t ≡ t) ≃ ()
    UDeletion : {Δ : Telescope n} {D : Set} {X : D → Set} 
        → {t : (d : D) → X d} (p : Δ [ k ]∶Σ[ D ] (λ d → t d ≡ t d))
        → Unification (doDeletionTel p)
        → Unification Δ

    -- (c s ≡ c t) ≃ (c ≡ t)
    UInjectivity : {j : ℕ} {Δ : Telescope n} {D : NI.DataDesc m}{D' : Set}
        → {s t : D' → NI.μ D} (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
        → (e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d))
        → (eℕ : (d : D') → conₙ (s d) ≡ j)
        → Unification (doinjectivityTel e' eℕ p)
        → Unification Δ

    -- (c₁ s ≡ c₂ t) ≃ ⊥
    UConflict : {Δ : Telescope n} {D : NI.DataDesc m}{D' : Set}
        → {s t : D' → NI.μ D} (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
        → (e' : (d : D') → ¬ (conᵢ (s d) ≡ conᵢ (t d)))
        → Unification (doConflictTel p e')
        → Unification Δ

    -- move item at goal back if it is not dependent on items after split
    UReorder : {Δ : Telescope n} (split : Fin n) (goal : Fin k)
        → (p : (x : ⟦ proj₁ (splitTel split Δ) ⟧telD) 
            → (Σ[ X ∈ Set ] ((proj₂ (splitTel split Δ)) x) [ k ]∶Σ[ ⊤ ] (λ _ → X)))
        → Unification (reorderTel split Δ goal p) 
        → Unification Δ

unifyTel : {i : ℕ} {Δ : Telescope i} (u : Unification Δ) 
    → Σ ℕ Telescope
unifyTel (UEnd Δ) = _ , Δ
unifyTel (Usolution p u) = unifyTel u
unifyTel (Usolution₁ p u) = unifyTel u
unifyTel (UDeletion p u) = unifyTel u
unifyTel (UInjectivity p e' eℕ u) = unifyTel u
unifyTel (UConflict p e' u) = unifyTel u
unifyTel (UReorder split goal p u) = unifyTel u

unify : {i : ℕ} {Δ : Telescope i} (u : Unification Δ) (xs : ⟦ Δ ⟧telD)
    → ⟦ proj₂ (unifyTel u) ⟧telD
unify (UEnd _) xs = xs
unify (Usolution p u) xs = unify u (update₂ p nil (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) xs)
unify (Usolution₁ p u) xs = unify u (update₂ p nil (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) xs)
unify (UDeletion p u) xs = unify u (update₁ p nil (λ xa → deletion) (λ xa → deletion') (λ xa → deletion'∘deletion) xs)
unify (UInjectivity p e' eℕ u) xs = unify u (doInjectivity e' eℕ p xs)
unify (UConflict {s = s} {t = t} p e' u) xs = unify u (update₁ p (cons ⊥ (λ b → nil)) (λ d' → conflict (s d') (t d') (e' d')) 
    (λ d' → conflict' (s d') (t d') (e' d')) (λ d' → conflict'∘conflict (s d') (t d') (e' d')) xs)
unify (UReorder split goal p u) xs = unify u (reorder split goal p xs)

unify' : {i : ℕ} {Δ : Telescope i} (u : Unification Δ) (xs : ⟦ proj₂ (unifyTel u) ⟧telD)
    → ⟦ Δ ⟧telD
unify' (UEnd _) xs = xs
unify' (Usolution p u) xs = update₂' p nil (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) (unify' u xs)
unify' (Usolution₁ p u) xs = update₂' p nil (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) (unify' u xs)
unify' (UDeletion p u) xs = update₁' p nil (λ xa → deletion) (λ xa → deletion') (λ xa → deletion'∘deletion) (unify' u xs)
unify' (UInjectivity p e' eℕ u) xs = doInjectivity' e' eℕ p (unify' u xs)
unify' (UConflict {s = s} {t = t} p e' u) xs = update₁' p (cons ⊥ (λ b → nil)) (λ d' → conflict (s d') (t d') (e' d')) 
    (λ d' → conflict' (s d') (t d') (e' d')) (λ d' → conflict'∘conflict (s d') (t d') (e' d')) (unify' u xs)
unify' (UReorder split goal p u) xs = reorder' split goal p (unify' u xs)

unify'∘unify : {i : ℕ} {Δ : Telescope i} (u : Unification Δ) (xs : ⟦ Δ ⟧telD)
    → unify' u (unify u xs) ≡ xs
unify'∘unify (UEnd _) xs = refl
unify'∘unify (Usolution p u) xs = subst (λ xs' → update₂' p nil (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) xs' ≡ xs) 
    (sym (unify'∘unify u ((update₂ p nil (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) xs)))) 
    (update₂'∘update₂ p nil (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) xs)
unify'∘unify (Usolution₁ p u) xs = subst (λ xs' → update₂' p nil (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) xs' ≡ xs) 
    (sym (unify'∘unify u ((update₂ p nil (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) xs)))) 
    (update₂'∘update₂ p nil (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) xs)
unify'∘unify (UDeletion p u) xs = subst (λ xs' → update₁' p nil (λ xa → deletion) (λ xa → deletion') (λ xa → deletion'∘deletion) xs' ≡ xs) 
    (sym (unify'∘unify u ((update₁ p nil (λ xa → deletion) (λ xa → deletion') (λ xa → deletion'∘deletion) xs)))) 
    (update₁'∘update₁ p nil (λ xa → deletion) (λ xa → deletion') (λ xa → deletion'∘deletion) xs)
unify'∘unify (UInjectivity p e' eℕ u) xs = subst (λ xs' → doInjectivity' e' eℕ p xs' ≡ xs) (sym (unify'∘unify u (doInjectivity e' eℕ p xs))) (doInjectivity'∘doInjectivity e' eℕ p xs)
unify'∘unify (UConflict {s = s} {t = t} p e' u) xs = subst (λ xs' → update₁' p (cons ⊥ (λ b → nil)) (λ d' → conflict (s d') (t d') (e' d')) 
    (λ d' → conflict' (s d') (t d') (e' d')) (λ d' → conflict'∘conflict (s d') (t d') (e' d')) xs' ≡ xs) 
    (sym (unify'∘unify u ((update₁ p (cons ⊥ (λ b → nil)) (λ d' → conflict (s d') (t d') (e' d')) 
    (λ d' → conflict' (s d') (t d') (e' d')) (λ d' → conflict'∘conflict (s d') (t d') (e' d')) xs)))) 
    (update₁'∘update₁ p (cons ⊥ (λ b → nil)) (λ d' → conflict (s d') (t d') (e' d')) 
    (λ d' → conflict' (s d') (t d') (e' d')) (λ d' → conflict'∘conflict (s d') (t d') (e' d')) xs) 
unify'∘unify (UReorder split goal p u) xs = subst (λ xs' → reorder' split goal p xs' ≡ xs) (sym (unify'∘unify u (reorder split goal p xs))) (reorder'∘reorder split goal p xs)


-- (n : ℕ) (zero ≡ suc n) ≃ (n : ℕ) (b : ⊥)
UnifyZero : Unification (n ∈ NI.μ NI.NatD , e ∈ (_≡_ {A = NI.μ NI.NatD} NI.zero' (NI.suc' n)) , nil) 
UnifyZero = UConflict (there (λ n → here n)) (λ d ()) 
                (UEnd (n ∈ NI.μ NI.NatD , _ ∈ ⊥ , nil))


-- (n m : ℕ) (x : X) (v : Vec X m) (suc n ≡ suc m) 
--      ≃ (n m : ℕ) (x : X) (v : Vec X m) (n ≡ m) 
--      ≃ (n : ℕ) (x : X) (v : Vec X n)
CTSucTel : (X : Set) → Telescope 5
CTSucTel X = n ∈ NI.μ NI.NatD , m ∈ NI.μ NI.NatD , x ∈ X , v ∈ OI.μ (OI.VecD X) (m , tt) 
        , e ∈ _≡_ {A = NI.μ NI.NatD} (NI.suc' m) (NI.suc' n) , nil

UnifySuc : (X : Set) → Unification (CTSucTel X)
UnifySuc X = UReorder (f2) (f0) (λ x → _ , (there (λ _ → there (λ _ → here tt)))) 
            (UInjectivity (there (λ n → there (λ m → here (m , n)))) (λ _ → refl) (λ _ → refl) 
                (Usolution₁ {X = ⊤} (there (λ n → here (tt , n))) 
                    (UEnd (n ∈ NI.μ NI.NatD , x ∈ X , v ∈ OI.μ (VecD X) (n , tt) , nil))))











 