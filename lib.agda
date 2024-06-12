{-# OPTIONS --without-K #-}
{-# OPTIONS --safe #-}

module lib where 

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

pattern f0 = fzero
pattern f1 = fsuc fzero
pattern f2 = fsuc (fsuc fzero)
pattern f3 = fsuc (fsuc (fsuc fzero))
pattern f4 = fsuc (fsuc (fsuc (fsuc fzero)))
pattern f5 = fsuc (fsuc (fsuc (fsuc (fsuc fzero))))
pattern f6 = fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))

-- eliminator identity type
J : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : (y : A) → x ≡ y → Set ℓ') → (p : P x refl) → {y : A} (e : x ≡ y) → P y e
J P p refl = p

-- reverse of eliminator identity type
J' : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} 
  → (P : (y : A) → x ≡ y → Set ℓ') 
  → {y : A} (e : x ≡ y) 
  → (p : P y e) 
  → P x refl
J' {x = x} P {y = y} e p 
  = subst 
      (λ xe → P (proj₁ xe) (proj₂ xe)) 
      (J (λ y e → (y , e) ≡ (x , refl)) refl e) 
      p 

-- proof section-retraction pair identity type
J'∘J : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : (y : A) → x ≡ y → Set ℓ') → (p : P x refl) → {y : A} (e : x ≡ y) 
        → J' P e (J P p e) ≡ p 
J'∘J {x = x} P p e = J (λ y e → J' P e (J P p e) ≡ p) refl e


-- sym identity type
J₁ : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : (y : A) → y ≡ x → Set ℓ') → (p : P x refl) → {y : A} (e : y ≡ x) → P y e
J₁ {x = x} P p {y} e = J (λ e p → P y e) (J (λ y e → P y (sym e)) p (sym e)) (J (λ x e → sym (sym e) ≡ e) refl e) 

-- reverse of sym identity type
J₁' : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : (y : A) → y ≡ x → Set ℓ')
            → {y : A} (e : y ≡ x) → (p : P y e) → P x refl
J₁' {x = x} P {y = y} e p = subst (λ xe → P (proj₁ xe) (proj₂ xe)) (J₁ (λ y e → (y , e) ≡ (x , refl)) refl e) p 

-- proof of reverse sym identity type
J₁'∘J₁ : ∀ {ℓ ℓ'} {A : Set ℓ} {x : A} (P : (y : A) → y ≡ x → Set ℓ') 
            → (p : P x refl) → {y : A} (e : y ≡ x) 
        → J₁' P e (J₁ P p e) ≡ p 
J₁'∘J₁ {x = x} P p {y} e = J₁ (λ y e → J₁' P e (J₁ P p e) ≡ p) refl e    


-- create equivalence between two product types
×-create : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A} {b₁ b₂ : B} (ea : a₁ ≡ a₂) 
                (eds : b₁ ≡ b₂) → (a₁ , b₁) ≡ (a₂ , b₂)
×-create {B = B} {a₁} {a₂} {b₁} ea eb = subst (λ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)) eb 
        (subst (λ a₂ → (a₁ , b₁) ≡ (a₂ , b₁)) ea refl)

proj×₁ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A} {b₁ b₂ : B} (e : (a₁ , b₁) ≡ (a₂ , b₂)) → a₁ ≡ a₂ 
proj×₁ e = cong proj₁ e

proj×₂ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A} {b₁ b₂ : B} (e : (a₁ , b₁) ≡ (a₂ , b₂)) → b₁ ≡ b₂ 
proj×₂ e = cong proj₂ e

create∘proj× : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {a₁ a₂ : A} {b₁ b₂ : B} (e : (a₁ , b₁) ≡ (a₂ , b₂)) 
    → ×-create (proj×₁ e) (proj×₂ e) ≡ e 
create∘proj× e = J (λ x e → ×-create (proj×₁ e) (proj×₂ e) ≡ e) refl e 


-- create equivalence between two dependent sym types
Σ-create : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (ea : a₁ ≡ a₂) 
                (eds : subst B ea b₁ ≡ b₂) → (a₁ , b₁) ≡ (a₂ , b₂)
Σ-create {B = B} {a₁} {a₂} {b₁} {b₂} ea eb = subst (λ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)) eb 
  (J (λ a₂ ea → (a₁ , b₁) ≡ (a₂ , subst B ea b₁)) refl ea)

linvΣ₁ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (e : (a₁ , b₁) ≡ (a₂ , b₂))
        → a₁ ≡ a₂ 
linvΣ₁ e = cong proj₁ e 

linvΣ₂ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (e : (a₁ , b₁) ≡ (a₂ , b₂))
        → subst B (linvΣ₁ e) b₁ ≡ b₂ 
linvΣ₂ {B = B} {b₁ = b₁} e = J (λ x₂ e → subst B (linvΣ₁ e) b₁ ≡ proj₂ x₂) refl e 

isLinvΣ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} (e : (a₁ , b₁) ≡ (a₂ , b₂))
        → Σ-create (linvΣ₁ e) (linvΣ₂ e) ≡ e 
isLinvΣ e = J (λ x e → Σ-create (linvΣ₁ e) (linvΣ₂ e) ≡ e) refl e 

isLinvΣ₁ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} 
        (ea : a₁ ≡ a₂) (eb : subst B ea b₁ ≡ b₂)
        → linvΣ₁ (Σ-create ea eb) ≡ ea
isLinvΣ₁ ea eb = J (λ b₂ eb → linvΣ₁ (Σ-create ea eb) ≡ ea) (J (λ a₂ ea → linvΣ₁ (Σ-create ea refl) ≡ ea) refl ea) eb 

isLinvΣ₂ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} 
        (ea : a₁ ≡ a₂) (eb : subst B ea b₁ ≡ b₂)
        → subst (λ ea → subst B ea b₁ ≡ b₂) (isLinvΣ₁ ea eb) (linvΣ₂ (Σ-create ea eb)) ≡ eb
isLinvΣ₂ {A = A} {B = B} {a₁} {a₂} {b₁} {b₂} ea eb = J (λ b₂ eb → subst (λ ea → subst B ea b₁ ≡ b₂) (isLinvΣ₁ ea eb) (linvΣ₂ (Σ-create ea eb)) ≡ eb) 
                    (J (λ a₂ ea → subst (λ ea₁ → subst B ea₁ b₁ ≡ subst B ea b₁) (isLinvΣ₁ ea refl) (linvΣ₂ (Σ-create ea refl)) ≡ refl) refl ea) eb 


-- create equivalence between a dependent sum and product type
Σ×-create : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → Set ℓ'}
  → {a₁ a₂ : A} (ea : a₁ ≡ a₂)  
  → {b₁ b₂ : B} (eb : b₁ ≡ b₂)
  → {c₁ : C a₁} {c₂ : C a₂} (ec : subst C ea c₁ ≡ c₂)
  → (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂)
Σ×-create {A = A} {B} {C} {a₁} {a₂} ea {b₁} {b₂} eb {c₁} {c₂} ec 
  = subst (λ c₂ → (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂)) ec 
    (J (λ b₂ eb → (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , subst C ea c₁)) 
      (J (λ a₂ ea → (a₁ , b₁ , c₁) ≡ (a₂ , b₁ , subst C ea c₁)) refl ea) eb)

linvΣ×₁ : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → Set ℓ'}
  → {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁} {c₂ : C a₂}
  → (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂)
  → a₁ ≡ a₂
linvΣ×₁ {A = A} {B} {C} {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} e = J (λ x₂ e → a₁ ≡ proj₁ x₂) refl e

linvΣ×₂ : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → Set ℓ'}
  → {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁} {c₂ : C a₂}
  → (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂)
  → b₁ ≡ b₂
linvΣ×₂ {A = A} {B} {C} {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} e = J (λ x₂ e → b₁ ≡ proj₁ (proj₂ x₂)) refl e

linvΣ×₃ : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → Set ℓ'}
  → {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁} {c₂ : C a₂}
  → (e : (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂))
  → subst C (linvΣ×₁ e) c₁ ≡ c₂
linvΣ×₃ {A = A} {B} {C} {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} e = J (λ x₂ e → subst C (linvΣ×₁ e) c₁ ≡ proj₂ (proj₂ x₂)) refl e

isLinvΣ× : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → Set ℓ'}
  → {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁} {c₂ : C a₂}
  → (e : (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂))
  → Σ×-create (linvΣ×₁ e) (linvΣ×₂ e) (linvΣ×₃ e) ≡ e
isLinvΣ× {A = A} {B} {C} {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} e = J (λ x e → Σ×-create (linvΣ×₁ e) (linvΣ×₂ e) (linvΣ×₃ e) ≡ e) refl e



-- create equivalence between two dependent sum types
ΣΣ-create : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → B → Set ℓ'}
  → {a₁ a₂ : A} (ea : a₁ ≡ a₂)  
  → {b₁ b₂ : B} (eb : b₁ ≡ b₂)
  → {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} (ec : subst (λ ab → C (proj₁ ab) (proj₂ ab)) (×-create ea eb) c₁ ≡ c₂)
  → (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂)
ΣΣ-create {A = A} {B} {C} {a₁} {a₂} ea {b₁} {b₂} eb {c₁} {c₂} ec 
  = subst (λ c₂ → (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂)) ec 
    (J (λ b₂ eb → (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , subst (λ ab → C (proj₁ ab) (proj₂ ab)) (×-create ea eb) c₁)) 
      (J (λ a₂ ea → (a₁ , b₁ , c₁) ≡ (a₂ , b₁ , subst (λ ab → C (proj₁ ab) (proj₂ ab)) (×-create ea refl) c₁)) refl ea) eb)

linvΣΣ₁ : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → B → Set ℓ'}
  → {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂}
  → (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂)
  → a₁ ≡ a₂
linvΣΣ₁ {A = A} {B} {C} {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} e = J (λ x₂ e → a₁ ≡ proj₁ x₂) refl e

linvΣΣ₂ : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → B → Set ℓ'}
  → {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂}
  → (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂)
  → b₁ ≡ b₂
linvΣΣ₂ {A = A} {B} {C} {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} e = J (λ x₂ e → b₁ ≡ proj₁ (proj₂ x₂)) refl e

linvΣΣ₃ : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → B → Set ℓ'}
  → {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂}
  → (e : (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂))
  → subst (λ ab → C (proj₁ ab) (proj₂ ab)) (×-create (linvΣΣ₁ e) (linvΣΣ₂ e)) c₁ ≡ c₂
linvΣΣ₃ {A = A} {B} {C} {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} e = J (λ x₂ e → subst (λ ab → C (proj₁ ab) (proj₂ ab)) (×-create (linvΣΣ₁ e) (linvΣΣ₂ e)) c₁ ≡ proj₂ (proj₂ x₂)) refl e


isLinvΣΣ : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → B → Set ℓ'}
  → {a₁ a₂ : A} {b₁ b₂ : B} {c₁ : C a₁ b₁} {c₂ : C a₂ b₂}
  → (e : (a₁ , b₁ , c₁) ≡ (a₂ , b₂ , c₂))
  → ΣΣ-create (linvΣΣ₁ e) (linvΣΣ₂ e) (linvΣΣ₃ e) ≡ e
isLinvΣΣ {A = A} {B} {C} {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} e = J (λ x e → ΣΣ-create (linvΣΣ₁ e) (linvΣΣ₂ e) (linvΣΣ₃ e) ≡ e) refl e



-- create an equivalence between two dependent sum types with a substitution
Σ-create' : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → B → Set ℓ'}
  → {a₁ a₂ : A} (ea : a₁ ≡ a₂)  
  → {b₁ b₂ : B} (eb : b₁ ≡ b₂)
  → {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} (ec : subst (λ ab → C (proj₁ ab) (proj₂ ab)) (×-create ea eb) c₁ ≡ c₂)
  → (a₁ , subst (C a₁) eb c₁) ≡ (a₂ , c₂)
Σ-create' {A = A} {B} {C} {a₁} {a₂} ea {b₁} {b₂} eb {c₁} {c₂} ec 
  = subst (λ c₂ → (a₁ , subst (C a₁) eb c₁) ≡ (a₂ , c₂)) ec 
    (J (λ a₂ ea → (a₁ , subst (C a₁) eb c₁) ≡ (a₂ , subst (λ ab → C (proj₁ ab) (proj₂ ab)) (×-create ea eb) c₁)) 
      (J (λ b₂ eb → (a₁ , subst (C a₁) eb c₁) ≡ (a₁ , subst (λ ab → C (proj₁ ab) (proj₂ ab)) (×-create refl eb) c₁)) refl eb) ea) 

linvΣ₁' : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → B → Set ℓ'}
  → {a₁ a₂ : A} {b₁ b₂ : B} (eb : b₁ ≡ b₂) {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} 
  → (a₁ , subst (C a₁) eb c₁) ≡ (a₂ , c₂)
  → a₁ ≡ a₂ 
linvΣ₁' eb e = cong proj₁ e 

linvΣ₂' : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → B → Set ℓ'}
  → {a₁ a₂ : A} {b₁ b₂ : B} (eb : b₁ ≡ b₂) {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} 
  → (e : (a₁ , subst (C a₁) eb c₁) ≡ (a₂ , c₂))
  → subst (λ ab → C (proj₁ ab) (proj₂ ab)) (×-create (linvΣ₁' eb e) eb) c₁ ≡ c₂
linvΣ₂' {A = A} {B} {C} {a₁} eb {c₁} e = 
  J (λ x₂ e → subst (λ ab → C (proj₁ ab) (proj₂ ab)) (×-create (linvΣ₁' eb e) eb) c₁ ≡ proj₂ x₂) 
    (J (λ b₂ eb → subst (λ ab → C (proj₁ ab) (proj₂ ab)) (×-create (linvΣ₁' {C = C} eb {c₁ = c₁} refl) eb) c₁ ≡ subst (λ v → C a₁ v) eb c₁) 
      refl eb) e 

isLinvΣ' : ∀ {ℓ ℓ'} {A B : Set ℓ} {C : A → B → Set ℓ'}
  → {a₁ a₂ : A} {b₁ b₂ : B} (eb : b₁ ≡ b₂) {c₁ : C a₁ b₁} {c₂ : C a₂ b₂} 
  → (e : (a₁ , subst (C a₁) eb c₁) ≡ (a₂ , c₂))
  → Σ-create' (linvΣ₁' eb e) eb (linvΣ₂' eb e) ≡ e 
isLinvΣ' {C = C} eb {c₁} e = J (λ x e → Σ-create' (linvΣ₁' eb e) eb (linvΣ₂' eb e) ≡ e) 
                (J (λ b eb → Σ-create' (linvΣ₁' {C = C} eb {c₁ = c₁} refl) eb (linvΣ₂' eb refl) ≡ refl) refl eb) e  


-- add cong to substitution                
subst→cong : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (P : B → Set ℓ'')
  {s t : A} (e : s ≡ t) (u : P (f s)) (v : P (f t))
  → subst (λ s → P (f s)) e u ≡ v 
  → subst P (cong f e) u ≡ v
subst→cong f P {s} {t} e u = J (λ t e → (v : P (f t)) → subst (λ s → P (f s)) e u ≡ v → subst P (cong f e) u ≡ v) 
  (λ v e → e) e 

-- remove cong from substitution
cong→subst : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} (f : A → B) (P : B → Set ℓ'')
  {s t : A} (e : s ≡ t) (u : P (f s)) (v : P (f t))
  → subst P (cong f e) u ≡ v
  → subst (λ s → P (f s)) e u ≡ v 
cong→subst f P {s} {t} e u = J (λ t e → (v : P (f t)) → subst P (cong f e) u ≡ v → subst (λ s → P (f s)) e u ≡ v) 
  (λ v e → e) e 

cong→subst∘subst→cong : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {P : B → Set ℓ''}
  {s t : A} (e : s ≡ t) (u : P (f s)) (v : P (f t))
  → (e' : subst (λ s → P (f s)) e u ≡ v)
  → cong→subst f P e u v (subst→cong f P e u v e') ≡ e'
cong→subst∘subst→cong {f = f} {P} {s} {t} e u = J (λ t e → (v : P (f t)) → (e' : subst (λ s → P (f s)) e u ≡ v)
      → cong→subst f P e u v (subst→cong f P e u v e') ≡ e') (λ v e' → refl) e 

subst→cong∘cong→subst : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {f : A → B} {P : B → Set ℓ''}
  {s t : A} (e : s ≡ t) (u : P (f s)) (v : P (f t))
  → (e' : subst P (cong f e) u ≡ v)
  → subst→cong f P e u v (cong→subst f P e u v e') ≡ e'
subst→cong∘cong→subst {f = f} {P} {s} {t} e u = J (λ t e → (v : P (f t)) → (e' : subst P (cong f e) u ≡ v)
      → subst→cong f P e u v (cong→subst f P e u v e') ≡ e') (λ v e' → refl) e 

-- substituting applying f and f' on both sides of an equivalence relation and substituting with f'∘f on both sides 
-- results in the original equivalence relation
subst∘subst : ∀ {ℓ} {A B : Set ℓ} {x y : A} → (e : x ≡ y) 
  (f : A → B) (f' : B → A) (f'∘f : (a : A) → f' (f a) ≡ a)
  → subst (λ e → e ≡ y) (f'∘f x) (subst (λ e → f' (f x) ≡ e) (f'∘f y) (cong f' (cong f e))) ≡ e
subst∘subst {x = x} refl f f' f'∘f = J (λ x' e' → subst (λ e → e ≡ x') e' (subst (_≡_ (f' (f x))) e' refl) ≡ refl) refl (f'∘f x) 


data Square {ℓ} {A : Set ℓ} {a : A} : {b c d : A} (p : a ≡ b) (q : c ≡ d) (r : a ≡ c) (s : b ≡ d) → Set ℓ where
  idS : Square {a = a} refl refl refl refl

-- flip the order of a square
flipS : ∀ {ℓ} {A : Set ℓ} {w x y z : A} (t : w ≡ x) (b : y ≡ z) (l : w ≡ y) (r : x ≡ z) 
        → Square t b l r → Square l r t b
flipS refl refl refl refl idS = idS

-- create a square from a substitution relation
createSquare : ∀ {ℓ} {A : Set ℓ} {w x y z : A} (t : w ≡ x) (b : y ≡ z) (l : w ≡ y) (r : x ≡ z) 
  (p : subst (λ wy → proj₁ wy ≡ proj₂ wy) (×-create t b) l ≡ r) → Square t b l r 
createSquare refl refl refl r refl = idS 

-- create substitution relation from a square
createSquare' : ∀ {ℓ} {A : Set ℓ} {w x y z : A} (t : w ≡ x) (b : y ≡ z) (l : w ≡ y) (r : x ≡ z) 
  → Square t b l r → subst (λ wy → proj₁ wy ≡ proj₂ wy) (×-create t b) l ≡ r
createSquare' refl refl refl r idS = refl

-- flip a substitution
flipSquare : ∀ {ℓ} {A : Set ℓ} {w x y z : A} (t : w ≡ x) (b : y ≡ z) (l : w ≡ y) (r : x ≡ z) 
  → (p : subst (λ wy → proj₁ wy ≡ proj₂ wy) (×-create t b) l ≡ r) 
  → subst (λ wy → proj₁ wy ≡ proj₂ wy) (×-create l r) t ≡ b
flipSquare t b l r p = createSquare' l r t b (flipS t b l r (createSquare t b l r p)) 

-- flipping a substitution twice results in the original substitution
flipSquare∘flipSquare : ∀ {ℓ} {A : Set ℓ} {w x y z : A} (t : w ≡ x) (b : y ≡ z) (l : w ≡ y) (r : x ≡ z) 
  → (p : subst (λ wy → proj₁ wy ≡ proj₂ wy) (×-create t b) l ≡ r) 
  → flipSquare l r t b (flipSquare t b l r p) ≡ p
flipSquare∘flipSquare refl refl refl r refl = refl 

-- substituting the left- and right-hand side of r with a dependent sum type containing 
-- equivalence relations a (f' u) ≡ a (f' v) and b (f' u) ≡ b (f' v)
-- results in substituting (f' u) in the left- and right-hand side of r
×-create→cong : ∀ {ℓ ℓ'} {A : Set ℓ} {X Y : Set ℓ'} {a b : X → Y} {f' : A → X}
  {u v : A}(e : u ≡ v) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v)) 
  → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create (cong (λ xs₁ → a (f' xs₁)) e) 
      (cong (λ xs₁ → b (f' xs₁)) e)) r ≡ s
  → subst (λ x → a x ≡ b x) (cong f' e) r ≡ s 
×-create→cong {a = a} {b} {f'} e r = J (λ v e → (s : a (f' v) ≡ b (f' v)) 
    → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create (cong (λ xs₁ → a (f' xs₁)) e) 
        (cong (λ xs₁ → b (f' xs₁)) e)) r ≡ s → subst (λ x → a x ≡ b x) (cong f' e) r ≡ s) 
      (λ s e → e) e

-- substituting (f' u) in the left- and right-hand side of r results in
-- substituting the left- and right-hand side of r with a dependent sum type containing 
-- equivalence relations a (f' u) ≡ a (f' v) and b (f' u) ≡ b (f' v)
×-cong→create : ∀ {ℓ ℓ'} {A : Set ℓ} {X Y : Set ℓ'} {a b : X → Y} {f' : A → X}
  {u v : A}(e : u ≡ v) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v)) 
  → subst (λ x → a x ≡ b x) (cong f' e) r ≡ s 
  → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create (cong (λ xs₁ → a (f' xs₁)) e) 
      (cong (λ xs₁ → b (f' xs₁)) e)) r ≡ s
×-cong→create {a = a} {b} {f'} e r = J (λ v e → (s : a (f' v) ≡ b (f' v)) 
    → subst (λ x → a x ≡ b x) (cong f' e) r ≡ s  
    → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create (cong (λ xs₁ → a (f' xs₁)) e) 
      (cong (λ xs₁ → b (f' xs₁)) e)) r ≡ s) 
      (λ s e → e) e

×-cong→create∘×-create→cong : ∀ {ℓ ℓ'} {A : Set ℓ} {X Y : Set ℓ'} {a b : X → Y} {f' : A → X}
  {u v : A}(e : u ≡ v) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v)) 
  → (xs : subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create (cong (λ xs₁ → a (f' xs₁)) e) 
      (cong (λ xs₁ → b (f' xs₁)) e)) r ≡ s) 
  → ×-cong→create {a = a} {b} {f'} e r s (×-create→cong {a = a} {b} {f'} e r s xs) ≡ xs
×-cong→create∘×-create→cong {a = a} {b} {f'} e r = J (λ v e → (s : a (f' v) ≡ b (f' v)) 
    → (xs : subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create (cong (λ xs₁ → a (f' xs₁)) e) 
        (cong (λ xs₁ → b (f' xs₁)) e)) r ≡ s) 
    → ×-cong→create {a = a} {b} {f'} e r s (×-create→cong {a = a} {b} {f'} e r s xs) ≡ xs) 
      (λ s e → refl) e


-- applying cong twice with g and f results into applying cong once on g∘f
cong∘cong→cong : ∀ {ℓ ℓ'} {A : Set ℓ} {X Y : Set ℓ'} {a b : X → Y} {f' : A → X}
  {u v : A}(e : u ≡ v) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v)) 
  → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong a (cong f' e)) ≡ cong b (cong f' e)
  → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e
cong∘cong→cong {a = a} {b} {f'} {u} {v} e r s e' = J (λ v e → (s : a (f' v) ≡ b (f' v)) → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong a (cong f' e)) ≡ cong b (cong f' e)
  → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e) 
    (λ s₁ x → x) e s e'

-- applying cong once on g∘ f, results into applying cong twice with g and f
cong→cong∘cong : ∀ {ℓ ℓ'} {A : Set ℓ} {X Y : Set ℓ'} {a b : X → Y} {f' : A → X}
  {u v : A}(e : u ≡ v) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v)) 
  → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e
  → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong a (cong f' e)) ≡ cong b (cong f' e)
cong→cong∘cong {a = a} {b} {f'} {u} {v} e r s e' = J (λ v e → (s : a (f' v) ≡ b (f' v))
  → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e
  → subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong a (cong f' e)) ≡ cong b (cong f' e)) 
    (λ s₁ x → x) e s e'

cong→cong∘cong∘cong∘cong→cong : ∀ {ℓ ℓ'} {A : Set ℓ} {X Y : Set ℓ'} {a b : X → Y} {f' : A → X}
  {u v : A}(e : u ≡ v) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v)) 
  → (e' : subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong a (cong f' e)) ≡ cong b (cong f' e))
  → cong→cong∘cong e r s (cong∘cong→cong e r s e') ≡ e'
cong→cong∘cong∘cong∘cong→cong {a = a} {b} {f'} {u} {v} e r s e' = J (λ v e → (s : a (f' v) ≡ b (f' v)) → (e' : subst (λ ab → proj₁ ab ≡ proj₂ ab) (×-create r s) (cong a (cong f' e)) ≡ cong b (cong f' e))
  → cong→cong∘cong e r s (cong∘cong→cong e r s e') ≡ e') 
    (λ s₁ x → refl) e s e'