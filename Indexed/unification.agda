{-# OPTIONS --allow-unsolved-metas #-}
module Indexed.unification where

open import Indexed.datatypes
open import Non_Indexed.telescope 
open import lib

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
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

private variable
  A     : Set
  t     : A
  n m k : ℕ

-- the solution rule
solution : Σ[ x ∈ A ] (t ≡ x) → ⊤
solution _ = tt

solution' : ⊤ → Σ[ x ∈ A ] (t ≡ x)
solution' {t = t} _ = t , refl

solution'∘solution : (xe : Σ[ x ∈ A ] (t ≡ x)) → solution' (solution xe) ≡ xe
solution'∘solution {t = t} xe = J (λ x e → (t , refl) ≡ (x , e)) refl (proj₂ xe)

-- update telescope with solution rule that replaces occurences of x by t
doSolutionTel : {Δ : Telescope n} {X : Set} {A : X → Set}
    (p : Δ [ k ]∶Σ[ Σ[ x ∈ X ] (A x) ] (λ xa → A (proj₁ xa)) ∶ (λ t x → (proj₂ t) ≡ x))
    → Telescope (n + zero ∸ 2)
doSolutionTel p = updateTel₂ p nil (λ xa → solution) (λ xa → solution') (λ xa → solution'∘solution) 


-- symmetric solution rule
solution₁ : Σ[ x ∈ A ] (x ≡ t) → ⊤
solution₁ _ = tt

solution₁' : ⊤ → Σ[ x ∈ A ] (x ≡ t)
solution₁' {t = t} _ = t , refl

solution₁'∘solution₁ : (xe : Σ[ x ∈ A ] (x ≡ t)) → solution₁' (solution₁ xe) ≡ xe
solution₁'∘solution₁ {t = t} xe = J₁ (λ x e → (t , refl) ≡ (x , e)) refl (proj₂ xe)

-- update telescope with solution rule that replaces occurences of x by t
doSolutionTel₁ : {Δ : Telescope n} {X : Set} {A : X → Set}
    (p : Δ [ k ]∶Σ[ Σ[ x ∈ X ] (A x) ] (λ xa → A (proj₁ xa)) ∶ (λ t x → x ≡ (proj₂ t))) 
    → Telescope (n + zero ∸ 2)
doSolutionTel₁ p = updateTel₂ p nil (λ xa → solution₁) (λ xa → solution₁') (λ xa → solution₁'∘solution₁) 


K : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : x ≡ x → Set ℓ') → (p : P refl) → (e : x ≡ x) → P e
K P p refl = p

-- the deletion rule
deletion : (e : t ≡ t) → ⊤ 
deletion e = K (λ e → ⊤) tt e

deletion' : ⊤ → t ≡ t 
deletion' _ = refl

deletion'∘deletion : (e : t ≡ t) → deletion' (deletion e) ≡ e 
deletion'∘deletion e = K (λ e → deletion' (deletion e) ≡ e) refl e

-- update the telescope by removing t ≡ t and replacing occurences by refl
doDeletionTel : {Δ : Telescope n} {D : Set} {X : D → Set} 
    → {t : (d : D) → X d}  (p : Δ [ k ]∶Σ[ D ] (λ d → t d ≡ t d))
    → Telescope (n + zero ∸ 1)
doDeletionTel p = updateTel₁ p nil (λ _ → deletion) (λ _ → deletion') (λ _ → deletion'∘deletion)



-- the conflict rule
conflict : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) → (f : ¬ (conᵢ s ≡ conᵢ t))
    → Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e s ≡ t)
    → Σ[ b ∈ ⊥ ] ⊤
conflict {D = D} s t f (ed , es) = ⊥-elim (f (cong (λ x → conᵢ (proj₂ x)) (Σ-create ed es))) , tt

conflict' :{i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) → (f : ¬ (conᵢ s ≡ conᵢ t))
    → Σ[ b ∈ ⊥ ] ⊤
    → Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e s ≡ t)
conflict' {D = D} {d₁} {d₂} s t f (b , tt) = ⊥-elim b

conflict'∘conflict : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) → (f : ¬ (conᵢ s ≡ conᵢ t))
    → (e : Σ[ e ∈ d₁ ≡ d₂ ] (subst (μ D) e s ≡ t))
    → conflict' s t f (conflict s t f e) ≡ e
conflict'∘conflict {D = D} s t f (ed , es) = ⊥-elim (f (cong (λ x → conᵢ (proj₂ x)) (Σ-create ed es)))

-- update the telescope by replacing (d₁ ≡ d₂)(x₁ ≡ x₂) by ⊥
doConflictTel : {Δn IΔn Dn i : ℕ} {Δ : Telescope Δn} {IΔ : Telescope IΔn} {D : DataDesc Dn IΔ}
        {X : Set} {d₁ : X → ⟦ IΔ ⟧telD} {d₂ : X → ⟦ IΔ ⟧telD} 
        {x₁ : (x : X) → μ D (d₁ x)} {x₂ : (x : X) → μ D (d₂ x)}
        → (p : Δ [ i ]∶Σ[ X ] (λ x → d₁ x ≡ d₂ x ) ∶ (λ x e → subst (μ D) e (x₁ x) ≡ x₂ x))
        → (e' : (x : X) → ¬ (conᵢ (x₁ x) ≡ conᵢ (x₂ x)))
        → Telescope (Δn + 1 ∸ 2)
doConflictTel {d₁ = d₁} {d₂} {x₁} {x₂} p e' = updateTel₂ p (cons ⊥ (λ b → nil)) 
    (λ d' → conflict (x₁ d') (x₂ d') (e' d')) (λ d' → conflict' (x₁ d') (x₂ d') (e' d')) 
        (λ d' → conflict'∘conflict (x₁ d') (x₂ d') (e' d'))

-- the injectivity rule
private variable
  i j : ℕ
  IΔ    : Telescope j

injectivityTelC : {IΔ : Telescope j}{D : DataDesc i IΔ}{C : ConDesc IΔ k} {d₁ d₂ : ⟦ IΔ ⟧telD} 
  → ⟦ C ⟧c (μ D) d₁ → ⟦ C ⟧c (μ D) d₂ → Telescope k
injectivityTelC {C = one' x} {d₁} {d₂} x₁ x₂ = nil
injectivityTelC {D = D} {C = Σ' S C} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , injectivityTelC (subst (λ x → ⟦ C x ⟧c (μ D) d₁) e xs₁) xs₂
injectivityTelC {C = ×' x C} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , injectivityTelC xs₁ xs₂

injectivityTel : {IΔ : Telescope j}{D : DataDesc i IΔ} {d₁ d₂ : ⟦ IΔ ⟧telD}
        → (x₁ : μ D d₁)  (x₂ : μ D d₂) → (conᵢ x₁ ≡ conᵢ x₂) → Σ ℕ Telescope
injectivityTel {D = D} {d₁} {d₂} x₁ x₂ ec = case-μ D 
        (λ d₁ x₁ → (x₂ : μ D d₂) → (conᵢ x₁ ≡ conᵢ x₂) → Σ ℕ Telescope) 
        (λ d₁ x₁ x₂ ec → case-μ D (λ d₂ x₂ → (proj₁ x₁ ≡ conᵢ x₂) → Σ ℕ Telescope) 
            (λ d₂ x₂ ec → proj₁ (D (proj₁ x₁)) , injectivityTelC (proj₂ x₁) (subst (λ x → ⟦ proj₂ (D x) ⟧c (μ D) d₂) (sym ec) (proj₂ x₂))) d₂ x₂ ec) 
        d₁  x₁ x₂ ec


injectivityC : {D : DataDesc i IΔ}{C : ConDesc IΔ k} {d : ⟦ IΔ ⟧telD} 
         → (x : ⟦ C ⟧c (μ D) d)
         → ⟦ injectivityTelC x x ⟧telD
injectivityC {C = one' v} {d₁} x = tt
injectivityC {D = D} {C = Σ' S D'} {d} (x , xs) = refl , injectivityC xs 
injectivityC {D = D} {C = ×' d' C} {d} (x , xs) = refl , injectivityC xs

injectivity : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂)
    → (e : (d₁ , s) ≡ (d₂ , t)) → ⟦ proj₂ (injectivityTel s t (cong (λ dx → conᵢ (proj₂ dx)) e)) ⟧telD
injectivity {D = D} {d₁} {d₂} s t e = J (λ x e → ⟦ proj₂ (injectivityTel s (proj₂ x) (cong (λ dx → conᵢ (proj₂ dx)) e)) ⟧telD) 
        (case-μ D (λ d₁ s → ⟦ proj₂ (injectivityTel s s refl) ⟧telD) (λ d₁ s → injectivityC (proj₂ s)) d₁ s) e 

injectivityK : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) (f : conᵢ s ≡ conᵢ t)
    → (e : (d₁ , s) ≡ (d₂ , t)) → ⟦ proj₂ (injectivityTel s t f) ⟧telD
injectivityK {D = D} {d₁} {d₂} s t f e = J (λ x e → (f : conᵢ s ≡ conᵢ (proj₂ x)) → ⟦ proj₂ (injectivityTel s (proj₂ x) f) ⟧telD) 
        (λ f → K (λ f → ⟦ proj₂ (injectivityTel s s f) ⟧telD) 
            (case-μ D (λ d₁ s → ⟦ proj₂ (injectivityTel s s refl) ⟧telD) (λ d₁ s → injectivityC (proj₂ s)) 
        d₁ s) f) e f

injectivityC' : {D : DataDesc i IΔ}{C : ConDesc IΔ k}{d₁ d₂ : ⟦ IΔ ⟧telD}
    → (x₁ : ⟦ C ⟧c (μ D) d₁) → (x₂ : ⟦ C ⟧c (μ D) d₂) → ⟦ injectivityTelC x₁ x₂ ⟧telD
    → (d₁ , x₁) ≡ (d₂ , x₂)
injectivityC' {IΔ = IΔ} {C = one' v} {d₁} {d₂} x₁ x₂ tt 
    = J₁ (λ v e → (x₂ : v ≡ d₂) → (d₁ , e) ≡ (d₂ , x₂)) (J (λ d₂ e → (d₁ , refl) ≡ (d₂ , e)) refl) x₁ x₂ 
injectivityC' {D = D} {C = Σ' S D'} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    =  ΣΣ-create (linvΣ₁' e (injectivityC' (subst (λ x → ⟦ D' x ⟧c (μ D) d₁) e xs₁) xs₂ es)) 
        e (linvΣ₂' e (injectivityC' (subst (λ x → ⟦ D' x ⟧c (μ D) d₁) e xs₁) xs₂ es)) 
injectivityC' {D = D} {C = ×' d C} {d₁} {d₂} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    = ΣΠ-create (linvΣ₁ (injectivityC' xs₁ xs₂ es)) e (linvΣ₂ (injectivityC' xs₁ xs₂ es)) 


injectivity' : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) → (ec : conᵢ s ≡ conᵢ t)
    → ⟦ proj₂ (injectivityTel s t ec) ⟧telD
    → (d₁ , s) ≡ (d₂ , t)
injectivity' {D = D} {d₁} {d₂} s t ec xs = case-μ D (λ d₁ s → (t : μ D d₂) → (ec : conᵢ s ≡ conᵢ t) 
    → ⟦ proj₂ (injectivityTel s t ec) ⟧telD → (d₁ , s) ≡ (d₂ , t)) 
    (λ d₁ s t ec xs → case-μ D (λ d₂ t → (ec : proj₁ s ≡ conᵢ t) → ⟦ proj₂ (injectivityTel ⟨ s ⟩ t ec) ⟧telD 
        → (d₁ , ⟨ s ⟩) ≡ (d₂ , t)) 
            (λ d₂ t ec xs → J (λ n₂ ec → (t : ⟦ proj₂ (D n₂) ⟧c (μ D) d₂) → ⟦ proj₂ (injectivityTel ⟨ s ⟩ ⟨ n₂ , t ⟩ ec) ⟧telD  → (d₁ , ⟨ proj₁ s , proj₂ s ⟩) 
                ≡ (d₂ , ⟨ n₂ , t ⟩)) (λ t xs → cong (λ where (d , x) → (d , ⟨ proj₁ s , x ⟩)) 
                (injectivityC' (proj₂ s) t xs)) ec (proj₂ t) xs) 
    d₂ t ec xs) d₁ s t ec xs

injectivity'K : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂) → (ec : conᵢ s ≡ conᵢ t)
    → ⟦ proj₂ (injectivityTel s t ec) ⟧telD
    → (d₁ , s) ≡ (d₂ , t)
injectivity'K {D = D} {d₁} {d₂} s t ec xs = case-μ D (λ d₁ s → (t : μ D d₂) → (ec : conᵢ s ≡ conᵢ t) 
    → ⟦ proj₂ (injectivityTel s t ec) ⟧telD → (d₁ , s) ≡ (d₂ , t)) 
    (λ d₁ s t ec xs → case-μ D (λ d₂ t → (ec : proj₁ s ≡ conᵢ t) → ⟦ proj₂ (injectivityTel ⟨ s ⟩ t ec) ⟧telD 
        → (d₁ , ⟨ s ⟩) ≡ (d₂ , t)) 
            (λ d₂ t ec xs → J (λ n₂ ec → (t : ⟦ proj₂ (D n₂) ⟧c (μ D) d₂) → ⟦ proj₂ (injectivityTel ⟨ s ⟩ ⟨ n₂ , t ⟩ ec) ⟧telD  → (d₁ , ⟨ proj₁ s , proj₂ s ⟩) 
                ≡ (d₂ , ⟨ n₂ , t ⟩)) (λ t xs → cong (λ where (d , x) → (d , ⟨ proj₁ s , x ⟩)) 
                (injectivityC' (proj₂ s) t xs)) ec (proj₂ t) xs) 
    d₂ t ec xs) d₁ s t ec xs



injectivityC'∘injectivityC : {D : DataDesc i IΔ}{C : ConDesc IΔ k}{d : ⟦ IΔ ⟧telD}
    → (x : ⟦ C ⟧c (μ D) d) 
    → injectivityC' x x (injectivityC x) ≡ refl
injectivityC'∘injectivityC {C = one' v} {d} x = J (λ d x → J₁ (λ v₁ e → (x₂ : v₁ ≡ d) → (d , e) ≡ (d , x₂)) (J (λ d₂ e → (d , refl {x = d}) ≡ (d₂ , e)) refl) x x ≡ refl) refl x --  refl
injectivityC'∘injectivityC {D = D} {C = Σ' S E} {d} (s , x) = subst (λ e → ΣΣ-create (linvΣ₁' {C = λ d s → ⟦ E s ⟧c (μ D) d} refl e) refl
      (linvΣ₂' refl e) ≡ refl) (sym (injectivityC'∘injectivityC x)) refl
injectivityC'∘injectivityC {D = D}{C = ×' d' C'} {d} (u , x) =  subst (λ e → ΣΠ-create (linvΣ₁ e) refl
      (linvΣ₂ e) ≡ refl) (sym (injectivityC'∘injectivityC x)) refl


injectivity'∘injectivity : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂)
    → (e : (d₁ , s) ≡ (d₂ , t)) → injectivity' s t (cong (λ dx → conᵢ (proj₂ dx)) e) (injectivity s t e) ≡ e
injectivity'∘injectivity {D = D} {d₁} {d₂} s t e = J (λ x e → injectivity' s (proj₂ x) (cong (λ dx → conᵢ (proj₂ dx)) e) (injectivity s (proj₂ x) e) ≡ e) 
    (case-μ D (λ d₁ s → injectivity' s s refl (injectivity s s refl) ≡ refl) 
       (λ d₁ s → cong (cong (λ { (d , x) → d , ⟨ proj₁ s , x ⟩ })) (injectivityC'∘injectivityC (proj₂ s))) 
    d₁ s) e

injectivity'∘injectivityK : {i j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD} 
    → (s : μ D d₁) (t : μ D d₂ )(f : conᵢ s ≡ conᵢ t)
    → (e : (d₁ , s) ≡ (d₂ , t)) → injectivity'K s t f (injectivityK s t f e) ≡ e
injectivity'∘injectivityK {D = D} {d₁} {d₂} s t f e = J (λ x e → (f : conᵢ s ≡ conᵢ (proj₂ x)) → injectivity'K s (proj₂ x) f (injectivityK s (proj₂ x) f e) ≡ e) 
    (λ f → K (λ f → injectivity'K s s f (injectivityK s s f refl) ≡ refl)
        (case-μ D (λ d₁ s → injectivity'K s s refl (injectivityK s s refl refl) ≡ refl) 
            (λ d s → cong (cong (λ { (d , x) → d , ⟨ proj₁ s , x ⟩ })) (injectivityC'∘injectivityC (proj₂ s)))
            d₁ s) 
    f) e f 

doInjectivityTelLength : {j : ℕ}{IΔ : Telescope j}{D : DataDesc i IΔ}{d₁ d₂ : ⟦ IΔ ⟧telD}
    → (s : μ D d₁) (t : μ D d₂) →  (e' : conᵢ s ≡ conᵢ t)
    → proj₁ (injectivityTel s t e') ≡ conₙ s
doInjectivityTelLength {D = D} ⟨ s ⟩ ⟨ t ⟩ e' = refl

doinjectivityTel : {Δn IΔn Dn i : ℕ} {Δ : Telescope Δn} {IΔ : Telescope IΔn} {D : DataDesc Dn IΔ}
    {X : Set} {d₁ : X → ⟦ IΔ ⟧telD} {d₂ : X → ⟦ IΔ ⟧telD} 
    {x₁ : (x : X) → μ D (d₁ x)} {x₂ : (x : X) → μ D (d₂ x)}
    {n : ℕ}(eℕ : (x : X) → conₙ (x₁ x) ≡ n)
    (p : Δ [ i ]∶Σ[ X ] (λ x → d₁ x ≡ d₂ x ) ∶ (λ x e → subst (μ D) e (x₁ x) ≡ x₂ x))
    (e' : (x : X) → (conᵢ (x₁ x) ≡ conᵢ (x₂ x)))
    → Telescope (i + n + (Δn ∸ suc (suc i)))
doinjectivityTel {Δn = suc (suc Δn)} {Δ = cons S E } {d₁ = d₁} {d₂} {x₁} {x₂} eℕ (here x {Δ}) e' 
    = subst (λ n → Telescope (n + Δn)) (trans (doInjectivityTelLength (x₁ x) (x₂ x) (e' x)) (eℕ x))
        (mergeTel (proj₂ (injectivityTel (x₁ x) (x₂ x) (e' x))) 
            (λ dx → Δ (linvΣ₁ dx) (linvΣ₂ dx)) 
            (λ xs → (injectivity'K (x₁ x) (x₂ x) (e' x) xs))) 
doinjectivityTel {Δ = cons S E} eℕ (there p) e' = cons S (λ s → doinjectivityTel eℕ (p s) e') 

doInjectivity : {Δn IΔn Dn i : ℕ} {Δ : Telescope Δn} {IΔ : Telescope IΔn} {D : DataDesc Dn IΔ}
    {X : Set} {d₁ : X → ⟦ IΔ ⟧telD} {d₂ : X → ⟦ IΔ ⟧telD} 
    {x₁ : (x : X) → μ D (d₁ x)} {x₂ : (x : X) → μ D (d₂ x)}
    {n : ℕ}(eℕ : (x : X) → conₙ (x₁ x) ≡ n)
    (p : Δ [ i ]∶Σ[ X ] (λ x → d₁ x ≡ d₂ x ) ∶ (λ x e → subst (μ D) e (x₁ x) ≡ x₂ x))
    (e' : (x : X) → (conᵢ (x₁ x) ≡ conᵢ (x₂ x)))
    → (xs : ⟦ Δ ⟧telD)
    → ⟦ doinjectivityTel eℕ p e' ⟧telD
doInjectivity {Δn = suc (suc Δn)} {Δ = cons S E} {D = D} {d₁ = d₁} {d₂} {x₁} {x₂} 
    eℕ (here x {Δ}) e' (ed , ex , xs)
    =  J (λ _ e → ⟦ subst (λ n → Telescope (n + Δn)) e 
            (mergeTel (proj₂ (injectivityTel (x₁ x) (x₂ x) (e' x))) 
            (λ dx → Δ (linvΣ₁ dx) (linvΣ₂ dx)) (injectivity'K (x₁ x) (x₂ x) (e' x))) ⟧telD )
    (merge (injectivityK (x₁ x) (x₂ x) (e' x) (Σ-create ed ex)) 
        (subst (λ e → ⟦ Δ (linvΣ₁ e) (linvΣ₂ e) ⟧telD) (sym (injectivity'∘injectivityK (x₁ x) (x₂ x) (e' x) (Σ-create ed ex))) 
            (applyΣ ed ex (λ ea eb → ⟦ Δ ea eb ⟧telD) xs)))
    (trans (doInjectivityTelLength (x₁ x) (x₂ x) (e' x)) (eℕ x))
doInjectivity {Δ = cons S E} {s} {t} eℕ (there p) e' (x , xs) = x , doInjectivity eℕ (p x) e' xs


doInjectivity' : {Δn IΔn Dn i : ℕ} {Δ : Telescope Δn} {IΔ : Telescope IΔn} {D : DataDesc Dn IΔ}
    {X : Set} {d₁ : X → ⟦ IΔ ⟧telD} {d₂ : X → ⟦ IΔ ⟧telD} 
    {x₁ : (x : X) → μ D (d₁ x)} {x₂ : (x : X) → μ D (d₂ x)}
    {n : ℕ}(eℕ : (x : X) → conₙ (x₁ x) ≡ n)
    (p : Δ [ i ]∶Σ[ X ] (λ x → d₁ x ≡ d₂ x ) ∶ (λ x e → subst (μ D) e (x₁ x) ≡ x₂ x))
    (e' : (x : X) → (conᵢ (x₁ x) ≡ conᵢ (x₂ x)))
    → ⟦ doinjectivityTel eℕ p e' ⟧telD
    → ⟦ Δ ⟧telD
doInjectivity' {Δn = suc (suc Δn)} {Δ = cons S E} {D = D} {d₁ = d₁} {d₂} {x₁} {x₂} 
    eℕ (here x {Δ}) e' xs
    = linvΣ₁ (injectivity'K (x₁ x) (x₂ x) (e' x) (mproj₁ xs')) , linvΣ₂ (injectivity'K (x₁ x) (x₂ x) (e' x) (mproj₁ xs')) 
        , mproj₂ {X = proj₂ (injectivityTel (x₁ x) (x₂ x) (e' x))} {Y = λ dx → Δ (linvΣ₁ dx) (linvΣ₂ dx)} xs'  where 
    
    xs' : ⟦ mergeTel (proj₂ (injectivityTel (x₁ x) (x₂ x) (e' x))) (λ dx → Δ (linvΣ₁ dx) (linvΣ₂ dx)) (injectivity'K (x₁ x) (x₂ x) (e' x)) ⟧telD
    xs' = J' (λ _ e → ⟦ subst (λ j₁ → Telescope (j₁ + Δn)) e 
            (mergeTel 
                (proj₂ (injectivityTel (x₁ x) (x₂ x) (e' x))) 
                (λ dx → Δ (linvΣ₁ dx) (linvΣ₂ dx)) 
                (injectivity'K (x₁ x) (x₂ x) (e' x))) ⟧telD) 
            (trans (doInjectivityTelLength (x₁ x) (x₂ x) (e' x)) (eℕ x)) xs

doInjectivity' {Δ = cons S E} {s} {t} eℕ (there p) e' (x , xs) = x , doInjectivity' eℕ (p x) e' xs



doInjectivity'∘doInjectivity :  {Δn IΔn Dn i : ℕ} {Δ : Telescope Δn} {IΔ : Telescope IΔn} {D : DataDesc Dn IΔ}
        {X : Set} {d₁ : X → ⟦ IΔ ⟧telD} {d₂ : X → ⟦ IΔ ⟧telD} 
        {x₁ : (x : X) → μ D (d₁ x)} {x₂ : (x : X) → μ D (d₂ x)}
        {n : ℕ}(eℕ : (x : X) → conₙ (x₁ x) ≡ n)
        → (p : Δ [ i ]∶Σ[ X ] (λ x → d₁ x ≡ d₂ x ) ∶ (λ x e → subst (μ D) e (x₁ x) ≡ x₂ x))
        → (e' : (x : X) → (conᵢ (x₁ x) ≡ conᵢ (x₂ x))) (xs : ⟦ Δ ⟧telD)
        → doInjectivity' eℕ p e' (doInjectivity eℕ p e' xs) ≡ xs
doInjectivity'∘doInjectivity {Δn = suc (suc Δn)} {Δ = cons E T} {D = D} {d₁ = d₁} {d₂} {x₁ = x₁} {x₂} eℕ (here x {Δ}) e' (ed , ex , xs) 
    = goal where

    xs' : ⟦ mergeTel (proj₂ (injectivityTel (x₁ x) (x₂ x) (e' x))) (λ dx → Δ (linvΣ₁ dx) (linvΣ₂ dx)) (injectivity'K (x₁ x) (x₂ x) (e' x)) ⟧telD
    xs' = J' (λ _ e → ⟦ subst (λ j₁ → Telescope (j₁ + Δn)) e 
            (mergeTel 
                (proj₂ (injectivityTel (x₁ x) (x₂ x) (e' x))) 
                (λ dx → Δ (linvΣ₁ dx) (linvΣ₂ dx)) 
                (injectivity'K (x₁ x) (x₂ x) (e' x))) ⟧telD) 
            (trans (doInjectivityTelLength (x₁ x) (x₂ x) (e' x)) (eℕ x)) 
            (J (λ _ e → ⟦ subst (λ j₁ → Telescope (j₁ + Δn)) e 
                (mergeTel 
                    (proj₂ (injectivityTel (x₁ x) (x₂ x) (e' x))) 
                    (λ dx → Δ (linvΣ₁ dx) (linvΣ₂ dx)) 
                    (injectivity'K (x₁ x) (x₂ x) (e' x))) ⟧telD) 
                (merge (injectivityK (x₁ x) (x₂ x) (e' x) (Σ-create ed ex)) 
                    (subst (λ e → ⟦ Δ (linvΣ₁ e) (linvΣ₂ e) ⟧telD) (sym (injectivity'∘injectivityK (x₁ x) (x₂ x) (e' x) (Σ-create ed ex))) 
                        (applyΣ ed ex (λ ea eb → ⟦ Δ ea eb ⟧telD) xs))) 
                (trans (doInjectivityTelLength (x₁ x) (x₂ x) (e' x)) (eℕ x)))

    goal :  (linvΣ₁ (injectivity'K (x₁ x) (x₂ x) (e' x) (mproj₁ xs')) , linvΣ₂ (injectivity'K (x₁ x) (x₂ x) (e' x) (mproj₁ xs')) 
        , mproj₂ {X = proj₂ (injectivityTel (x₁ x) (x₂ x) (e' x))} {Y = λ dx → Δ (linvΣ₁ dx) (linvΣ₂ dx)} xs')
        ≡ (ed , ex , xs)
    goal = subst (λ xs' → (linvΣ₁ (injectivity'K (x₁ x) (x₂ x) (e' x) (mproj₁ xs')) , linvΣ₂ (injectivity'K (x₁ x) (x₂ x) (e' x) (mproj₁ xs')) 
                , mproj₂ {X = proj₂ (injectivityTel (x₁ x) (x₂ x) (e' x))} {Y = λ dx → Δ (linvΣ₁ dx) (linvΣ₂ dx)} xs')
                ≡ (ed , ex , xs))
            (sym (J'∘J (λ _ e → ⟦ subst (λ j₁ → Telescope (j₁ + Δn)) e 
                (mergeTel 
                    (proj₂ (injectivityTel (x₁ x) (x₂ x) (e' x))) 
                    (λ dx → Δ (linvΣ₁ dx) (linvΣ₂ dx)) 
                    (injectivity'K (x₁ x) (x₂ x) (e' x))) ⟧telD) 
                (merge (injectivityK (x₁ x) (x₂ x) (e' x) (Σ-create ed ex)) 
                    (subst (λ e → ⟦ Δ (linvΣ₁ e) (linvΣ₂ e) ⟧telD) (sym (injectivity'∘injectivityK (x₁ x) (x₂ x) (e' x) (Σ-create ed ex))) 
                        (applyΣ ed ex (λ ea eb → ⟦ Δ ea eb ⟧telD) xs))) 
                (trans (doInjectivityTelLength (x₁ x) (x₂ x) (e' x)) (eℕ x)))) 
                (subst (λ axs → (linvΣ₁ (injectivity'K (x₁ x) (x₂ x) (e' x) (proj₁ axs)) ,
                                linvΣ₂ (injectivity'K (x₁ x) (x₂ x) (e' x) (proj₁ axs)) ,
                                proj₂ axs) ≡ (ed , ex , xs)) 
                (mproj∘merge (injectivityK (x₁ x) (x₂ x) (e' x) (Σ-create ed ex)) 
                    (subst (λ e → ⟦ Δ (linvΣ₁ e) (linvΣ₂ e) ⟧telD) (sym
                        (injectivity'∘injectivityK (x₁ x) (x₂ x) (e' x) (Σ-create ed ex)))
                    (applyΣ ed ex (λ ea eb → ⟦ Δ ea eb ⟧telD) xs)))
                (J (λ x' e' → ( linvΣ₁ x' , linvΣ₂ x' , subst (λ e → ⟦ Δ (linvΣ₁ e) (linvΣ₂ e) ⟧telD)
                        e' (applyΣ ed ex (λ ea eb → ⟦ Δ ea eb ⟧telD) xs)) ≡ (ed , ex , xs)) 
                    (proofΣ ed ex xs) 
                    (sym (injectivity'∘injectivityK (x₁ x) (x₂ x) (e' x) (Σ-create ed ex))) 
                       )) 
                      
doInjectivity'∘doInjectivity {Δ = cons S E} eℕ (there p) e' (x , xs) = subst (λ xs' → (x , xs') ≡ (x , xs)) (sym (doInjectivity'∘doInjectivity eℕ (p x) e' xs)) refl   



-- injectivity rule for datatypes with no indices
injectivityTelC₁ : {D : DataDesc i nil}{C : ConDesc nil j} (x₁ x₂ : ⟦ C ⟧c (μ D) tt) → Telescope j
injectivityTelC₁ {C = one' tt} _ _ = nil
injectivityTelC₁ {D = D} {C = Σ' S C} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , injectivityTelC₁ (subst (λ x → ⟦ C x ⟧c (μ D) tt) e xs₁) xs₂
injectivityTelC₁ {C = ×' tt C} (x₁ , xs₁) (x₂ , xs₂) = e ∈ x₁ ≡ x₂ , injectivityTelC₁ xs₁ xs₂

injectivityTel₁ : {D : DataDesc i nil} (x₁ x₂ : μ D tt) → conᵢ x₁ ≡ conᵢ x₂ → Σ ℕ Telescope
injectivityTel₁ {D = D} x₁ x₂ e = case-μ D (λ _ x₁ → (x₂ : μ D tt) → conᵢ x₁ ≡ conᵢ x₂ → Σ ℕ Telescope) 
        (λ _ x₁ → case-μ D (λ _ x₂ → proj₁ x₁ ≡ conᵢ x₂ → Σ ℕ Telescope) 
            (λ _ x₂ e → proj₁ (D (proj₁ x₁)) , injectivityTelC₁ (proj₂ x₁) (subst (λ x → ⟦ proj₂ (D x) ⟧c (μ D) tt) (sym e) (proj₂ x₂))) tt) 
            tt x₁ x₂ e

injectivityC₁ : {D : DataDesc i nil}{C : ConDesc nil j} → (c : ⟦ C ⟧c (μ D) tt) → ⟦ injectivityTelC₁ c c ⟧telD
injectivityC₁ {C = one' tt} c = tt
injectivityC₁ {C = Σ' S D} (c , cs) = refl , injectivityC₁ cs
injectivityC₁ {C = ×' tt C} (c , cs) = refl , injectivityC₁ cs

injectivity₁ : {D : DataDesc i nil} (x₁ x₂ : μ D tt) (f : conᵢ x₁ ≡ conᵢ x₂) (e : x₁ ≡ x₂) 
    → ⟦ proj₂ (injectivityTel₁ x₁ x₂ f) ⟧telD
injectivity₁ {D = D} x₁ x₂ f e = J (λ x₂ e → (f : conᵢ x₁ ≡ conᵢ x₂) → ⟦ proj₂ (injectivityTel₁ x₁ x₂ f) ⟧telD) 
    (λ f → K (λ f → ⟦ proj₂ (injectivityTel₁ x₁ x₁ f) ⟧telD) 
        (case-μ D (λ _ x₁ → ⟦ proj₂ (injectivityTel₁ x₁ x₁ refl) ⟧telD) (λ _ x₁ → injectivityC₁ (proj₂ x₁)) tt
    x₁) f) e f

-- -- left inverse injectivity
injectivityC₁' : {D : DataDesc i nil}{C : ConDesc nil j}
    → (x₁ x₂ : ⟦ C ⟧c (μ D) tt) → ⟦ injectivityTelC₁ x₁ x₂ ⟧telD → x₁ ≡ x₂
injectivityC₁' {C = one' tt} refl refl e = refl 
injectivityC₁' {D = D} {C = Σ' S D'} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    = J (λ x₂ e → (xs₂ : ⟦ D' x₂ ⟧c (μ D) tt) → subst (λ x → ⟦ D' x ⟧c (μ D) tt) e xs₁ ≡ xs₂ → (x₁ , xs₁) ≡ (x₂ , xs₂)) 
        (λ xs₂ e₂ → subst (λ x → (x₁ , xs₁) ≡ (x₁ , x)) e₂ refl)
        e xs₂ (injectivityC₁' (subst (λ s → ⟦ D' s ⟧c (μ D) tt) e xs₁) xs₂ es)
injectivityC₁' {D = D} {C = ×' tt C} (x₁ , xs₁) (x₂ , xs₂) (e , es) 
    = subst (λ xs₂ → (x₁ , xs₁) ≡ (x₂ , xs₂)) (injectivityC₁' xs₁ xs₂ es) 
        (subst (λ x₂ → (x₁ , xs₁) ≡ (x₂ , xs₁)) e refl)

injectivity₁' : {D : DataDesc i nil} (x₁ x₂ : μ D tt)
    → (f : conᵢ x₁ ≡ conᵢ x₂) → ⟦ proj₂ (injectivityTel₁ x₁ x₂ f) ⟧telD → x₁ ≡ x₂
injectivity₁' {D = D} 
    = case-μ D (λ _ x₁ → (x₂ : μ D tt) → (f : conᵢ x₁ ≡ conᵢ x₂) → ⟦ proj₂ (injectivityTel₁ x₁ x₂ f) ⟧telD → x₁ ≡ x₂) 
        (λ _ x₁ → case-μ D (λ _ x₂ → (f : proj₁ x₁ ≡ conᵢ x₂) → ⟦ proj₂ (injectivityTel₁ ⟨ x₁ ⟩ x₂ f) ⟧telD → ⟨ x₁ ⟩ ≡ x₂) 
            (λ _ x₂ f → J (λ n₂ e → (x₂ : ⟦ proj₂ (D n₂) ⟧c (μ D) tt) → ⟦ proj₂ (injectivityTel₁ ⟨ x₁ ⟩ ⟨ n₂ , x₂ ⟩ e) ⟧telD → ⟨ x₁ ⟩ ≡ ⟨ n₂ , x₂ ⟩) 
                (λ x₂ xs → cong (λ x → ⟨ proj₁ x₁ , x ⟩) (injectivityC₁' (proj₂ x₁) x₂ xs)) f (proj₂ x₂)) tt) tt

-- proof of left inverse injectivity
injectivityC₁'∘injectivityC₁ : {D : DataDesc i nil}{C : ConDesc nil j} (x : ⟦ C ⟧c (μ D) tt)
    → injectivityC₁' x x (injectivityC₁ x) ≡ refl
injectivityC₁'∘injectivityC₁ {C = one' tt} refl = refl
injectivityC₁'∘injectivityC₁ {D = D} {C = Σ' S E} (s , x) = subst (λ e → subst (λ x₁ → (s , x) ≡ (s , x₁)) e refl ≡ refl) (sym (injectivityC₁'∘injectivityC₁ x)) refl
injectivityC₁'∘injectivityC₁ {D = D}{C = ×' tt C'} (u , x) = subst (λ e → subst (λ xs → (u , x) ≡ (u , xs)) e refl
      ≡ refl) (sym (injectivityC₁'∘injectivityC₁ x)) refl 

injectivity₁'∘injectivity₁ : {D : DataDesc i nil} → (x₁ x₂ : μ D tt) → (f : conᵢ x₁ ≡ conᵢ x₂)
    → (e : x₁ ≡ x₂) → injectivity₁' x₁ x₂ f (injectivity₁ x₁ x₂ f e) ≡ e
injectivity₁'∘injectivity₁ {D = D} x₁ x₂ f e = J (λ x₂ e → (f : conᵢ x₁ ≡ conᵢ x₂) → injectivity₁' x₁ x₂ f (injectivity₁ x₁ x₂ f e) ≡ e) 
    (λ f → K (λ f → injectivity₁' x₁ x₁ f (injectivity₁ x₁ x₁ f refl) ≡ refl) 
        (case-μ D (λ _ x₁ → injectivity₁' x₁ x₁ refl (injectivity₁ x₁ x₁ refl refl) ≡ refl) 
            (λ _ x₁ → cong (cong (λ x → ⟨ proj₁ x₁ , x ⟩)) (injectivityC₁'∘injectivityC₁ (proj₂ x₁))) tt x₁) f) e f

doInjectivityTelLength₁ : {D : DataDesc i nil} → (s t : μ D tt) 
    → (f : conᵢ s ≡ conᵢ t)
    → proj₁ (injectivityTel₁ s t f) ≡ conₙ s 
doInjectivityTelLength₁ {D = D} = case-μ D (λ _ s → (t : μ D tt) → (f : (conᵢ s ≡ conᵢ t)) → proj₁ (injectivityTel₁ s t f) ≡ conₙ s) 
            (λ _ s → case-μ D (λ _ t → (f : (conᵢ ⟨ s ⟩ ≡ conᵢ t)) → proj₁ (injectivityTel₁ ⟨ s ⟩ t f) ≡ conₙ ⟨ s ⟩) 
            (λ _ t f → refl) tt) tt  

doinjectivityTel₁ : {D' : Set}{n i j k : ℕ}{D : DataDesc i nil} {Δ : Telescope n}
  → {s t : D' → μ D tt}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d')))
  → Telescope (k + j + (n ∸ suc k))
doinjectivityTel₁ {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) = subst (λ j → Telescope (j + i)) (trans (doInjectivityTelLength₁ (s d) (t d) (e' d)) (eℕ d)) 
    (mergeTel (proj₂ (injectivityTel₁ (s d) (t d) (e' d))) E (injectivity₁' (s d) (t d) (e' d))) 
doinjectivityTel₁ {Δ = cons S E} {s} {t} e' eℕ (there x) = cons S (λ s → doinjectivityTel₁ e' eℕ (x s))

doInjectivity₁ : {D' : Set}{n i j k : ℕ}{D : DataDesc i nil}{Δ : Telescope n}
  → {s t : D' → μ D tt}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d'))) (xs : ⟦ Δ ⟧telD)
  → ⟦ doinjectivityTel₁ e' eℕ p ⟧telD
doInjectivity₁ {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) (e , xs) = J 
    (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (injectivityTel₁ (s d) (t d) (e' d))) E (injectivity₁' (s d) (t d) (e' d))) ⟧telD) 
    (merge (injectivity₁ (s d) (t d) (e' d) e) (subst (λ e → ⟦ E e ⟧telD) (sym (injectivity₁'∘injectivity₁ (s d) (t d) (e' d) e)) xs)) 
    (trans (doInjectivityTelLength₁ (s d) (t d) (e' d)) (eℕ d))
doInjectivity₁ {Δ = cons S E} {s} {t} e' eℕ (there p) (x , xs) = x , doInjectivity₁ e' eℕ (p x) xs 

doInjectivity₁' : {D' : Set}{n i j k : ℕ}{D : DataDesc i nil}{Δ : Telescope n}
  → {s t : D' → μ D tt}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d'))) (xs : ⟦ doinjectivityTel₁ e' eℕ p ⟧telD)
  → ⟦ Δ ⟧telD
doInjectivity₁' {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) xs = (injectivity₁' (s d) (t d) (e' d) (mproj₁ xs')) 
    , mproj₂ {X = proj₂ (injectivityTel₁ (s d) (t d) (e' d))} {Y = E} xs'  where 
    
    xs' : ⟦ mergeTel (proj₂ (injectivityTel₁ (s d) (t d) (e' d))) E (injectivity₁' (s d) (t d) (e' d)) ⟧telD
    xs' = J' (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (injectivityTel₁ (s d) (t d) (e' d))) E (injectivity₁' (s d) (t d) (e' d))) ⟧telD) 
            (trans (doInjectivityTelLength₁ (s d) (t d) (e' d)) (eℕ d)) xs
    
doInjectivity₁' {Δ = cons S E} {s} {t} e' eℕ (there p) (x , xs) = x , doInjectivity₁' e' eℕ (p x) xs 

doInjectivity₁'∘doInjectivity₁ : {D' : Set}{n i j k : ℕ}{D : DataDesc i nil}{Δ : Telescope n}
  → {s t : D' → μ D tt}(e' : (d : D') → conᵢ (s d) ≡ conᵢ (t d)) (eℕ : (d : D') → conₙ (s d) ≡ j)
  → (p : Δ [ k ]∶Σ[ D' ] (λ d' → (s d') ≡ (t d'))) (xs : ⟦ Δ ⟧telD)
  → doInjectivity₁' e' eℕ p (doInjectivity₁ e' eℕ p xs) ≡ xs
doInjectivity₁'∘doInjectivity₁ {n = suc i} {Δ = cons S E} {s} {t} e' eℕ (here d) (e , xs) = goal where

    xs' : ⟦ mergeTel (proj₂ (injectivityTel₁ (s d) (t d) (e' d))) E (injectivity₁' (s d) (t d) (e' d)) ⟧telD 
    xs' = J' (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (injectivityTel₁ (s d) (t d) (e' d))) E (injectivity₁' (s d) (t d) (e' d))) ⟧telD) 
            (trans (doInjectivityTelLength₁ (s d) (t d) (e' d)) (eℕ d)) 
                (J (λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (injectivityTel₁ (s d) (t d) (e' d))) E (injectivity₁' (s d) (t d) (e' d))) ⟧telD) 
                (merge (injectivity₁ (s d) (t d) (e' d) e) (subst (λ e → ⟦ E e ⟧telD) (sym (injectivity₁'∘injectivity₁ (s d) (t d) (e' d) e)) xs)) 
                (trans (doInjectivityTelLength₁ (s d) (t d) (e' d)) (eℕ d)))

    goal : (injectivity₁' (s d) (t d) (e' d) (mproj₁ xs'),
       mproj₂ {X = proj₂ (injectivityTel₁ (s d) (t d) (e' d))} {Y = E} xs')
      ≡ (e , xs)
    goal = subst (λ xs' → (injectivity₁' (s d) (t d) (e' d) (mproj₁ xs') ,  mproj₂ {X = proj₂ (injectivityTel₁ (s d) (t d) (e' d))} {Y = E} xs') ≡ (e , xs)) 
            (sym (J'∘J ((λ x e → ⟦ subst (λ j₁ → Telescope (j₁ + i)) e (mergeTel (proj₂ (injectivityTel₁ (s d) (t d) (e' d))) E (injectivity₁' (s d) (t d) (e' d))) ⟧telD)) 
            (merge (injectivity₁ (s d) (t d) (e' d) e) (subst (λ e → ⟦ E e ⟧telD) (sym (injectivity₁'∘injectivity₁ (s d) (t d) (e' d) e)) xs)) 
            (trans (doInjectivityTelLength₁ (s d) (t d) (e' d)) (eℕ d)))) 
            (subst (λ axs → ((injectivity₁' (s d) (t d) (e' d) (proj₁ axs)) , (proj₂ axs)) ≡ (e , xs))
            (mproj∘merge (injectivity₁ (s d) (t d) (e' d) e) (subst (λ e₁ → ⟦ E e₁ ⟧telD)
                    (sym (injectivity₁'∘injectivity₁ (s d) (t d) (e' d) e)) xs))
                (J (λ x' e' → (x' , subst (λ e → ⟦ E e ⟧telD) e' xs) ≡ (e , xs)) refl  (sym (injectivity₁'∘injectivity₁ (s d) (t d) (e' d) e))))

doInjectivity₁'∘doInjectivity₁ {Δ = cons S E} {s} {t} e' eℕ (there p) (x , xs) = subst (λ xs' → (x , xs') ≡ (x , xs)) (sym (doInjectivity₁'∘doInjectivity₁ e' eℕ (p x) xs)) refl


-- reverse solution rule for HO unification
doSolution←Tel : {i : ℕ} {Δ : Telescope i} {j : ℕ} {X : Set} {Y : Set} (A : X → Set)
    → (f : Y → X)
    → {s t : (y : Y) → A (f y)} 
    → (p : Δ [ j ]∶Σ[ Y ] (λ x → s x ≡ t x)) 
    → Telescope (2 + i)
doSolution←Tel {Δ = cons S E} A f {s} {t} (here d {Δ}) = e ∈ f d ≡ f d , p ∈ e ≡ refl , x ∈ subst A e (s d) ≡ t d , Δ (subst (λ e → subst A e (s d) ≡ t d) p x)
doSolution←Tel {Δ = cons S E} A f (there p) = cons S (λ s → doSolution←Tel A f (p s)) 

doSolution← : {i : ℕ} {Δ : Telescope i} {j : ℕ}{X : Set}{Y : Set}  (A : X → Set)
    → (f : Y → X)
    → {s t : (y : Y) → A (f y)} 
    → (p : Δ [ j ]∶Σ[ Y ] (λ x → s x ≡ t x)) (xs : ⟦ Δ ⟧telD)
    → ⟦ doSolution←Tel A f p ⟧telD
doSolution← A f (here d {Δ}) (x , xs) = refl , refl , x , xs
doSolution← A f (there p) (x , xs) = x , doSolution← A f (p x) xs 

doSolution'← : {i : ℕ} {Δ : Telescope i} {j : ℕ}{X : Set}{Y : Set}  (A : X → Set)
    → (f : Y → X)
    → {s t : (y : Y) → A (f y)} 
    → (p : Δ [ j ]∶Σ[ Y ] (λ x → s x ≡ t x)) → ⟦ doSolution←Tel A f p ⟧telD
    → ⟦ Δ ⟧telD
doSolution'← A f {s} {t} (here d) (e , p , x , xs) =  subst (λ e → subst A e (s d) ≡ t d) p x , xs
doSolution'← A f (there p) (x , xs) = x , doSolution'← A f (p x) xs

doSolution'∘doSolution← : {i : ℕ} {Δ : Telescope i} {j : ℕ}{X : Set}{Y : Set}  (A : X → Set)
    → (f : Y → X)
    → {s t : (y : Y) → A (f y)} 
    → (p : Δ [ j ]∶Σ[ Y ] (λ x → s x ≡ t x)) → (xs : ⟦ Δ ⟧telD)
    → doSolution'← A f p (doSolution← A f p xs) ≡ xs
doSolution'∘doSolution← A f (here d {Δ}) (x , xs) = refl
doSolution'∘doSolution← A f (there p) (x , xs) = subst (λ xs' → (x , xs') ≡ (x , xs)) (sym (doSolution'∘doSolution← A f (p x) xs)) refl

