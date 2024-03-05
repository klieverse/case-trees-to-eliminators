{-# OPTIONS --allow-unsolved-metas #-}
module Indexed.unification where

import Non_Indexed.datatypes as NI
open import Indexed.datatypes
open import Non_Indexed.telescope 

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

-- NoConfusion
private variable
  i j k : ℕ
  IΔ    : Telescope j

NoConfusionCTel : {IΔ : Telescope j} (d₁ d₂ : ⟦ IΔ ⟧telD) → Telescope j
NoConfusionCTel {IΔ = nil} d₁ d₂ = nil
NoConfusionCTel {IΔ = cons S E} (d₁ , ds₁) (d₂ , ds₂) = e ∈ d₁ ≡ d₂ , NoConfusionCTel (subst (λ d → ⟦ E d ⟧telD) e ds₁) ds₂

NoConfusionC : {IΔ : Telescope j}{D : DataDesc i IΔ}{C : ConDesc IΔ k} {d₁ d₂ : ⟦ IΔ ⟧telD} 
  → ⟦ C ⟧c (μ D) d₁ → ⟦ C ⟧c (μ D) d₂ → Telescope (k + j)
NoConfusionC {C = one' x} {d₁} {d₂} x₁ x₂ = NoConfusionCTel d₁ d₂
NoConfusionC {D = D} {C = Σ' S C} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , NoConfusionC (subst (λ x → ⟦ C x ⟧c (μ D) d₁) e xs₁) xs₂
NoConfusionC {C = ×' x C} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , NoConfusionC xs₁ xs₂

NoConfusion' : {D : DataDesc i IΔ} {d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (x₁ : ⟦ D ⟧ (μ D) d₁) → (x₂ : ⟦ D ⟧ (μ D) d₂) 
    → Dec (proj₁ x₁ ≡ proj₁ x₂) → Σ ℕ Telescope
NoConfusion' {D = D} {d₁} {d₂} x₁ x₂ (yes e) = _ , NoConfusionC (proj₂ x₁) (subst (λ x → ⟦ proj₂ (D x) ⟧c (μ D) d₂) (sym e) (proj₂ x₂))
NoConfusion' x₁ x₂ (no _) = 1 , (_ ∈ ⊥ , nil)

NoConfusion : {D : DataDesc i IΔ} {d₁ d₂ : ⟦ IΔ ⟧telD}  
    → (x₁ : μ D d₁) → (x₂ : μ D d₂) → Dec (conᵢ x₁ ≡ conᵢ x₂) → Σ ℕ Telescope
NoConfusion {D = D} {d₁} {d₂} x₁ x₂ e = case-μ D (λ d₁' x₁' → (x₂' : μ D d₂) → Dec (conᵢ x₁' ≡ conᵢ x₂') → Σ ℕ Telescope) 
        (λ d₁' x₁' x₂' e' → case-μ D (λ d₂' x₂' → Dec (proj₁ x₁' ≡ conᵢ x₂') → Σ ℕ Telescope) 
            (λ d₂' x₂' e'' → NoConfusion' x₁' x₂' e'') 
                d₂ x₂' e') d₁ x₁ x₂ e

-- no confusion 
noConfCTel : {IΔ : Telescope j} (d : ⟦ IΔ ⟧telD) → ⟦ NoConfusionCTel d d ⟧telD
noConfCTel {IΔ = nil} d = tt
noConfCTel {IΔ = cons S E} (d , ds) = refl , (noConfCTel ds) 

noConfC : {D : DataDesc i IΔ}{C : ConDesc IΔ k} {d : ⟦ IΔ ⟧telD} 
         → (c : ⟦ C ⟧c (μ D) d) → ⟦ NoConfusionC c c ⟧telD
noConfC {C = one' v} {d} c = noConfCTel d
noConfC {C = Σ' S D} {d} (c , cs) = refl , noConfC cs
noConfC {D = D} {C = ×' d C} (c , cs) = refl , noConfC cs

noConf' : {D : DataDesc i IΔ}{d : ⟦ IΔ ⟧telD} (x : ⟦ D ⟧ (μ D) d) 
    → ⟦ proj₂ (NoConfusion ⟨ x ⟩ ⟨ x ⟩ (yes refl)) ⟧telD
noConf' (n , c) = noConfC c

noConf : {D : DataDesc i IΔ} {d₁ d₂ : ⟦ IΔ ⟧telD} (x₁ : μ D d₁) (x₂ : μ D d₂) 
    → (e : (d₁ , x₁) ≡ (d₂ , x₂)) → (f : Dec (conᵢ x₁ ≡ conᵢ x₂)) → ⟦ proj₂ (NoConfusion x₁ x₂ f) ⟧telD
noConf {D = D} {d₁} {d₂} x₁ x₂ e = subst (λ x₂ → (f : Dec (conᵢ x₁ ≡ conᵢ (proj₂ x₂))) → ⟦ proj₂ (NoConfusion x₁ (proj₂ x₂) f) ⟧telD) e λ where
    (yes refl) → case-μ D (λ d' x' → ⟦ proj₂ (NoConfusion x' x' (yes refl)) ⟧telD) (λ _ → noConf') d₁ x₁ 
    (no x) → case-μ D (λ d' x' → (x : ¬ conᵢ x' ≡ conᵢ x') → ⟦ proj₂ (NoConfusion x' x' (no x)) ⟧telD) (λ d x' e → (e refl) , tt) d₁ x₁ x

-- left inverse no confusion 
linvNoConfC : {D : DataDesc i IΔ}{C : ConDesc IΔ k}{d₁ d₂ : ⟦ IΔ ⟧telD}
    → (x₁ : ⟦ C ⟧c (μ D) d₁) → (x₂ : ⟦ C ⟧c (μ D) d₂) → ⟦ NoConfusionC x₁ x₂ ⟧telD
    → (d₁ , x₁) ≡ (d₂ , x₂)
linvNoConfC {IΔ = IΔ} {C = one' v} {d₁} {d₂} x₁ x₂ e 
    = J' (λ v e → (x₂ : v ≡ d₂) → (d₁ , e) ≡ (d₂ , x₂)) (J (λ d₂ e → (d₁ , refl) ≡ (d₂ , e)) refl) x₁ x₂ 
linvNoConfC {D = D} {C = Σ' S D'} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    =  J' (λ x₁ e → (xs₁ : ⟦ D' x₁ ⟧c (μ D) d₁) → (d₁ , subst (λ x → ⟦ D' x ⟧c (μ D) d₁) e xs₁) ≡ (d₂ , xs₂) → (d₁ , x₁ , xs₁) ≡ (d₂ , x₂ , xs₂)) 
            (λ xs₁ → (cong (λ e → proj₁ e , x₂ , proj₂ e))) e xs₁ (linvNoConfC (subst (λ x → ⟦ D' x ⟧c (μ D) d₁) e xs₁) xs₂ es) 
linvNoConfC {D = D} {C = ×' d C} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    = J (λ x₂ e → (d₁ , xs₁) ≡ (d₂ , xs₂) → (d₁ , x₁ , xs₁) ≡ (d₂ , x₂ , xs₂)) 
        (cong (λ e → proj₁ e , x₁ , proj₂ e)) e (linvNoConfC xs₁ xs₂ es)

linvNoConf' : {D : DataDesc i IΔ} {d₁ d₂ : ⟦ IΔ ⟧telD} (x₁ : ⟦ D ⟧ (μ D) d₁) (x₂ : ⟦ D ⟧ (μ D) d₂)
     → (f : Dec (proj₁ x₁ ≡ proj₁ x₂)) → ⟦ proj₂ (NoConfusion ⟨ x₁ ⟩ ⟨ x₂ ⟩ f) ⟧telD → (d₁ , ⟨ x₁ ⟩) ≡ (d₂ , ⟨ x₂ ⟩)
linvNoConf' (n₁ , x₁) (n₂ , x₂) (yes refl) e = cong (λ x → (proj₁ x , ⟨ n₁ , proj₂ x ⟩)) (linvNoConfC x₁ x₂ e) 
linvNoConf' x₁ x₂ (no d) e = ⊥-elim (proj₁ e)

linvNoConf : {D : DataDesc i IΔ} {d₁ d₂ : ⟦ IΔ ⟧telD} → (x₁ : μ D d₁) (x₂ : μ D d₂) 
    → (f : Dec (conᵢ x₁ ≡ conᵢ x₂)) → ⟦ proj₂ (NoConfusion x₁ x₂ f) ⟧telD → (d₁ , x₁) ≡ (d₂ , x₂)
linvNoConf {IΔ = IΔ} {D = D} {d₁} {d₂} x₁ = case-μ D (λ d₁ x₁ → (d₂ : ⟦ IΔ ⟧telD) → (x₂ : μ D d₂) → (f : Dec (conᵢ x₁ ≡ conᵢ x₂)) → ⟦ proj₂ (NoConfusion x₁ x₂ f) ⟧telD → (d₁ , x₁) ≡ (d₂ , x₂)) 
            (λ d₁ x₁ → case-μ D (λ d₂ x₂ → (f : Dec (conᵢ ⟨ x₁ ⟩ ≡ conᵢ x₂)) → ⟦ proj₂ (NoConfusion ⟨ x₁ ⟩ x₂ f) ⟧telD → (d₁ , ⟨ x₁ ⟩) ≡ (d₂ , x₂)) 
                λ d₂ x₂ f e → linvNoConf' x₁ x₂ f e) d₁ x₁ d₂
                
-- proof of left inverse no confusion
isLinvNoConfC : {D : DataDesc i IΔ}{C : ConDesc IΔ k}{d : ⟦ IΔ ⟧telD} (x : ⟦ C ⟧c (μ D) d)
    → linvNoConfC x x (noConfC x) ≡ refl
isLinvNoConfC {IΔ = IΔ} {C = one' v} {d} x = J ((λ d x → J' (λ v₁ e → (x₂ : v₁ ≡ d) → (d , e) ≡ (d , x₂))
            (J (λ d₂ e → (d , refl {x = d}) ≡ (d₂ , e)) refl) x x
            ≡ refl )) refl x
isLinvNoConfC {D = D} {C = Σ' S E} (s , x) = subst (λ e → cong (λ e₁ → proj₁ e₁ , s , proj₂ e₁) e ≡ refl) (sym (isLinvNoConfC x)) refl
isLinvNoConfC {D = D}{C = ×' d C} (u , x) = subst (λ e → cong (λ e₁ → proj₁ e₁ , u , proj₂ e₁) e ≡ refl) (sym (isLinvNoConfC x)) refl 

isLinvNoConf' :  {D : DataDesc i IΔ} {d : ⟦ IΔ ⟧telD} {n : Fin i} (x : ⟦ proj₂ (D n) ⟧c (μ D) d) 
    → linvNoConf ⟨ n , x ⟩ ⟨ n , x ⟩ (yes refl) (noConf ⟨ n , x ⟩ ⟨ n , x ⟩ refl (yes refl)) ≡ refl
isLinvNoConf' {D = D} {n = n} x = subst (λ e → cong (λ x₁ → proj₁ x₁ , ⟨ n , proj₂ x₁ ⟩) e ≡ refl) (sym (isLinvNoConfC x)) refl 

isLinvNoConf :  {D : DataDesc i IΔ} {d₁ d₂ : ⟦ IΔ ⟧telD} → (x₁ : μ D d₁) (x₂ : μ D d₂) 
    → (e : (d₁ , x₁) ≡ (d₂ , x₂)) → (f : Dec (conᵢ x₁ ≡ conᵢ x₂)) → linvNoConf x₁ x₂ f (noConf x₁ x₂ e f) ≡ e
isLinvNoConf {D = D} {d₁} x₁ x₂ refl (yes refl) = case-μ D (λ d x → linvNoConf x x (yes refl) (noConf x x refl (yes refl)) ≡ refl) 
    (λ d x → isLinvNoConf' (proj₂ x)) d₁ x₁ 
isLinvNoConf {D = D} x₁ x₂ e (no f) = ⊥-elim (f (cong (λ e → conᵢ (proj₂ e)) e)) 



proj₂d : {D : Set} {DS : D → Set} {d : D} (ds₁ ds₂ : (d : D) → DS d)
        → (e :  _,_ {B = λ d → DS d} d (ds₁ d) ≡ (d , ds₂ d)) 
        → ds₁ d ≡ ds₂ d
proj₂d {D} {DS} {d} ds₁ ds₂ e = linvJ (λ x e → subst DS e (ds₁ d) ≡ ds₂ x) (cong proj₁ e) 
    (J' (λ ds₁ e → subst DS (cong proj₁ e) (proj₂ ds₁) ≡ ds₂ d) refl e)

≡proj₂d' : {D : Set} {DS : D → Set} {d : D} (ds₁ ds₂ : (d : D) → DS d)
        → (x : ds₁ d ≡ ds₂ d)
        → x ≡ proj₂d ds₁ ds₂ (cong (d ,_) x)
≡proj₂d' {D} {DS} {d} ds₁ ds₂ x = goal where 

    goal : x ≡ subst (λ xe → subst DS (proj₂ xe) (ds₁ d) ≡ ds₂ (proj₁ xe))
            (J (λ y e → (y , e) ≡ (d , refl)) refl (cong proj₁ (cong (d ,_) x)))
                (J' (λ ds₃ e → subst DS (cong proj₁ e) (proj₂ ds₃) ≡ ds₂ d)
                    refl (cong (d ,_) x))
    goal = {!   !}  


≡proj₂d : {D : Set} {DS : D → Set} {d : D} (ds₁ ds₂ : (d : D) → DS d)
        → (x : ds₁ d ≡ ds₂ d)
        → {f : (e :  _,_ {B = λ d → DS d} d (ds₁ d) ≡ (d , ds₂ d)) 
                → _,_ {B = λ d → DS d} d (ds₁ d) ≡ (d , ds₂ d)}
        → (p : (e :  _,_ {B = λ d → DS d} d (ds₁ d) ≡ (d , ds₂ d)) → f e ≡ e)
        → x ≡ proj₂d ds₁ ds₂ (f (cong (d ,_) x))
≡proj₂d {D} {DS} {d} ds₁ ds₂ x p = subst (λ e' → x ≡ proj₂d ds₁ ds₂ e') (sym (p (cong (d ,_) x))) (≡proj₂d' ds₁ ds₂ x) 




-- the injectivity rule
injectivity : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) 
    → (e' : conᵢ s ≡ conᵢ t)
    → (e : (d₁ , s) ≡ (d₂ , t)) → ⟦ proj₂ (NoConfusion s t (yes e')) ⟧telD
injectivity {D} s t e' e = noConf s t e (yes e')

linvInjectivity : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) 
    → (e' : conᵢ s ≡ conᵢ t)
    → ⟦ proj₂ (NoConfusion s t (yes e')) ⟧telD
    → (d₁ , s) ≡ (d₂ , t)
linvInjectivity {D} s t e' e = linvNoConf s t (yes e') e 

isLinvinjectivity : {D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) 
    → (e' : conᵢ s ≡ conᵢ t)
    → (e : (d₁ , s) ≡ (d₂ , t)) → linvInjectivity s t e' (injectivity s t e' e) ≡ e
isLinvinjectivity {D} s t e' e = isLinvNoConf s t e (yes e')


doInjectivityTel' : {j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD}
    → (s : μ D d₁) (t : μ D d₂) 
    → (e' : conᵢ s ≡ conᵢ t)
    → proj₁ (NoConfusion s t (yes e')) ≡ conₙ s + j
doInjectivityTel' {j = j} {IΔ} {D} {d₁} {d₂} s t e' 
    = case-μ D (λ d₁ s → (d₂ : ⟦ IΔ ⟧telD) → (t : μ D d₂) → (e' : conᵢ s ≡ conᵢ t) → proj₁ (NoConfusion s t (yes e')) ≡ conₙ s + j) 
        (λ d₁ s d₂ t e' → case-μ D (λ d₂ t → (e' : conᵢ ⟨ s ⟩ ≡ conᵢ t) → proj₁ (NoConfusion ⟨ s ⟩ t (yes e')) ≡ conₙ ⟨ s ⟩ + j) 
            (λ d x e' → refl) 
        d₂ t e') d₁ s d₂ t e' 

doInjectivityTel :  {i j m : ℕ} {Δ : Telescope i} {IΔ : Telescope m} {D : DataDesc j IΔ} {D' : Set}
        → {s t : D' → (d : ⟦ IΔ ⟧telD) → (μ D d)} {n x : ℕ} (eℕ : (d' : D') → (d : ⟦ IΔ ⟧telD) → (conₙ (s d' d) ≡ n))
            (p : Δ [ x ]∶Σ[ Σ D' (λ _ → ⟦ IΔ ⟧telD) ] (λ d' → (s (proj₁ d') (proj₂ d')) ≡ (t (proj₁ d') (proj₂ d'))))
        → (e' : (d' : D') → (d : ⟦ IΔ ⟧telD) → (conᵢ (s d' d)) ≡ conᵢ (t d' d))
        → Telescope (x + n + m + (i ∸ suc x))
doInjectivityTel {i = suc i} {m = m} {Δ = cons E Δ} {IΔ} {D} {s = s} {t = t} {n = n} eℕ (here (d' , d)) e' 
    = subst (λ j → Telescope (j + i)) (trans (doInjectivityTel' (s d' d) (t d' d) (e' d' d)) 
        (cong (λ n → n + m) (eℕ d' d))) (mergeTel (proj₂ (NoConfusion (s d' d) (t d' d) (yes (e' d' d)))) 
            Δ (λ x → proj₂d (s d') (t d') (linvInjectivity (s d' d) (t d' d) (e' d' d) x)))
doInjectivityTel {Δ = cons S E} eℕ (there p) e' = cons S (λ s → doInjectivityTel eℕ (p s) e') 


-- doInjectivity : {D' : Set}{n i j k : ℕ}{D : DataDesc i}{Δ : Telescope n}
--   → {s t : D' → μ D}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
--   → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d'))) (xs : ⟦ Δ ⟧telD)
--   → ⟦ doInjectivityTel e' eℕ p ⟧telD
-- doInjectivity {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) (e , xs) = J 
--     (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (NoConfusion (s d) (t d) (yes (e' d)))) E (linvInjectivity (s d) (t d) (e' d))) ⟧telD) 
--     (merge (injectivity (s d) (t d) (e' d) e) (subst (λ e → ⟦ E e ⟧telD) (sym (isLinvinjectivity (s d) (t d) (e' d) e)) xs)) 
--     (trans (doInjectivityTel' (s d) (t d) (e' d)) (eℕ d))
-- doInjectivity {Δ = cons S E} {s} {t} e' eℕ (there p) (x , xs) = x , doInjectivity e' eℕ (p x) xs 




-- the conflict rule
conflict : {D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) 
    → (e' : ¬ (conᵢ s ≡ conᵢ t))
    → (e : (d₁ , s) ≡ (d₂ , t))
    → ⊥
conflict {IΔ = IΔ} {D = D} {d₁} {d₂} s
    = case-μ D (λ d₁ s → (d₂ : ⟦ IΔ ⟧telD) (t : μ D d₂) → ¬ conᵢ s ≡ conᵢ t → (d₁ , s) ≡ (d₂ , t) → ⊥) 
        (λ d₁ s → case-μ D (λ d₂ t → ¬ conᵢ ⟨ s ⟩ ≡ conᵢ t → (d₁ , ⟨ s ⟩) ≡ (d₂ , t) → ⊥) 
            (λ d₂ t e' e → proj₁ (noConf ⟨ s ⟩ ⟨ t ⟩ e (no e')))) 
        d₁ s d₂ 

linvConflict : {D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) 
    → (e' : ¬ (conᵢ s ≡ conᵢ t))
    → ⊥
    → (d₁ , s) ≡ (d₂ , t)
linvConflict {IΔ = IΔ} {D = D} {d₁} {d₂} s
    = case-μ D (λ d₁ s → (d₂ : ⟦ IΔ ⟧telD) (t : μ D d₂) → ¬ conᵢ s ≡ conᵢ t → ⊥ → (d₁ , s) ≡ (d₂ , t)) 
        (λ d₁ s → case-μ D (λ d₂ t → ¬ conᵢ ⟨ s ⟩ ≡ conᵢ t → ⊥ → (d₁ , ⟨ s ⟩) ≡ (d₂ , t)) 
            (λ d₂ t e' b → linvNoConf ⟨ s ⟩ ⟨ t ⟩ (no e') (b , tt)))
        d₁ s d₂ 

isLinvConflict : {D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) 
    → (e' : ¬ (conᵢ s ≡ conᵢ t))
    → (e : (d₁ , s) ≡ (d₂ , t))
    → linvConflict s t e' (conflict s t e' e) ≡ e
isLinvConflict {IΔ = IΔ} {D = D} {d₁} {d₂} s
    = case-μ D (λ d₁ s → (d₂ : ⟦ IΔ ⟧telD) (t : μ D d₂) → (e' : ¬ conᵢ s ≡ conᵢ t) → (e : (d₁ , s) ≡ (d₂ , t)) → linvConflict s t e' (conflict s t e' e) ≡ e) 
            (λ d₁ s → case-μ D (λ d₂ t → (e' : ¬ conᵢ ⟨ s ⟩ ≡ conᵢ t) → (e : (d₁ , ⟨ s ⟩) ≡ (d₂ , t)) → linvConflict ⟨ s ⟩ t e' (conflict ⟨ s ⟩ t e' e) ≡ e) 
            (λ d₂ t e' e → isLinvNoConf ⟨ s ⟩ ⟨ t ⟩ e (no e'))) d₁ s d₂ 

doConflictTel :  {i j : ℕ} {Δ : Telescope i} {D : DataDesc j IΔ} {D' : Set}
        → {s t : D' → (d : ⟦ IΔ ⟧telD) → (μ D d)} {x : ℕ} 
            (p : Δ [ x ]∶Σ[ Σ D' (λ _ → ⟦ IΔ ⟧telD) ] (λ d' → (s (proj₁ d') (proj₂ d')) ≡ (t (proj₁ d') (proj₂ d'))))
        → (e' : (d' : D') → (d : ⟦ IΔ ⟧telD) → (¬ (conᵢ (s d' d)) ≡ conᵢ (t d' d)))
        → Telescope i
doConflictTel {IΔ = IΔ} {Δ = cons E Δ} {D} {s = s} {t = t} (here (d' , d)) e' = b ∈ ⊥ , Δ (proj₂d (s d') (t d') (linvConflict (s d' d) (t d' d) (e' d' d) b)) 

doConflictTel {Δ = cons S E} (there p) e' = cons S (λ s → doConflictTel (p s) e') 

doConflict :  {i j : ℕ} {Δ : Telescope i} {D : DataDesc j IΔ} {D' : Set}
        → {s t : D' → (d : ⟦ IΔ ⟧telD) → (μ D d)} {x : ℕ} 
            (p : Δ [ x ]∶Σ[ Σ D' (λ _ → ⟦ IΔ ⟧telD) ] (λ d' → (s (proj₁ d') (proj₂ d')) ≡ (t (proj₁ d') (proj₂ d'))))
        → (e' : (d' : D') → (d : ⟦ IΔ ⟧telD) → (¬ (conᵢ (s d' d)) ≡ conᵢ (t d' d))) (xs : ⟦ Δ ⟧telD)
        → ⟦ doConflictTel p e' ⟧telD
doConflict {Δ = cons E Δ} {s = s} {t = t} (here (d' , d)) e' (x , xs) = conflict (s d' d) (t d' d) (e' d' d) (cong (d ,_) x) 
    , subst (λ e → ⟦ Δ e ⟧telD) (≡proj₂d (s d') (t d') x (isLinvConflict (s d' d) (t d' d) (e' d' d))) xs 
doConflict {Δ = cons S E} (there p) e' (x , xs) = x , doConflict (p x) e' xs
