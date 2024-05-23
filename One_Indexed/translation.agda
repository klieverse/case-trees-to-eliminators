{-# OPTIONS --allow-unsolved-metas #-}
module One_Indexed.translation where 

import Non_Indexed.datatypes as NI
open import Non_Indexed.telescope
open import One_Indexed.datatypes
open import One_Indexed.casetrees
open import One_Indexed.unify

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

-- evaluation function of a case tree ct
eval : {Δ : Telescope n}{T : ⟦ Δ ⟧telD → Set ℓ} → 
  (ct : CaseTree Δ T) (args : ⟦ Δ ⟧telD) 
  → T args 
eval (leaf f) args = f args
eval {Δ = Δ} {T} (node {IΔ = IΔ} {D = D} p bs) args 
  = case-μ D (λ d' x' → (d' , x') ≡ (d , ret) → T args) cs d ret refl where 

    d : ⟦ IΔ ⟧Vec 
    d = proj₁ (args Σ[ p ])

    -- value that we split on
    ret : μ D d 
    ret = proj₂ (args Σ[ p ])

    -- from a constructor instantiation that is equivalent to the value 
    -- that we split on get the return type
    cs : (d' : ⟦ IΔ ⟧Vec) (x : ⟦ D ⟧ (μ D) d') → (d' , ⟨ x ⟩) ≡ (d , ret) → T args
    cs d' (k , xs) e = shrinkExpand p (conToTel xs) q T args (sym e) r where

      q : ⟨ k , telToCon (conToTel xs) ⟩ ≡ ⟨ k , xs ⟩
      q = cong (λ x → ⟨ k , x ⟩) (telToCon∘conToTel xs)

      -- recursively evaluate the case tree
      r : expandSort p T (expand p (conToTel xs) q args (sym e))
      r = subst (expandSort p T) (unify'∘unify (proj₁ (bs k)) (expand p (conToTel xs) q args (sym e))) 
              (eval (proj₂ (bs k)) (unify (proj₁ (bs k)) (expand p (conToTel xs) q args (sym e))))


-- example translation head function
≡Head : {X : Set}{x : X}(n : NI.μ NI.NatD)(v : μ (VecD X) (NI.suc' n , tt)) → head' X n v ≡ x 
        → eval (CTHeadRoot X) (n , v , tt) ≡ x 
≡Head n (cons' n x xs) refl = refl 

-- example translation antisym function
antisym-tel : (n m : NI.μ NI.NatD)(x : μ ≤D (n , m , tt))(y : μ ≤D (m , n , tt)) → ⟦ antisymΔ ⟧telD
antisym-tel n m x y = n , m , x , y , below antisymPx createp ((n , m , tt)) x , tt  where

        createp : (d : ⟦ ≤Tel ⟧Vec) → (x : μ ≤D d) → Below antisymPx d x → antisymPx d x
        createp d x b ( _ , _ , _ , y , _ ) refl = eval CTantisym (proj₁ d , proj₁ (proj₂ d) , x , y , b , tt) 

antisym-elim : (n m : NI.μ NI.NatD)(x : μ ≤D (n , m , tt))(y : μ ≤D (m , n , tt)) →
  {e : n ≡ m } → antisym n m x y ≡ e 
  → eval CTantisym (antisym-tel n m x y) ≡ e
antisym-elim .NI.zero' .NI.zero' (lz .NI.zero') (lz .NI.zero') refl = refl
antisym-elim .NI.zero' m (lz .m) ⟨ fsuc fzero , _ , n , _ , () ⟩ refl
antisym-elim .(NI.suc' n) .(NI.suc' m) (ls n m x) (ls .m .n y) refl = cong (λ n → cong NI.suc' n) (antisym-elim n m x y refl)


-- example translation Nat₁-K-like-elim function
Nat₁-K-like-elim-tel : (P : (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) 
        (mzero : P NI.zero' zero₁')
        (msuc : (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
                P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁))
        (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → ⟦ Nat₁-K-like-elimΔ P ⟧telD
Nat₁-K-like-elim-tel P mzero msuc n₀ n₁ = mzero , msuc , n₀ , n₁ , below (Nat₁-K-like-elimPx P) createp ((n₀ , n₀ , tt)) n₁ , tt  where

        createp : (d : ⟦ Nat₁Tel ⟧Vec) → (x : μ Nat₁D d) → Below (Nat₁-K-like-elimPx P) d x → Nat₁-K-like-elimPx P d x
        createp d x b t refl = eval (CTNat₁-K-like-elim P) (mzero , msuc , proj₁ d , x , b , tt) 

≡-Nat₁-K-like-elim : (P : (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) 
  (mzero : P NI.zero' zero₁')
  (msuc : (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
          P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁))
  (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) →
  {x : P n₀ n₁} → Nat₁-K-like-elim P mzero msuc n₀ n₁ ≡ x 
  → eval (CTNat₁-K-like-elim P) (Nat₁-K-like-elim-tel P mzero msuc n₀ n₁) ≡ x
≡-Nat₁-K-like-elim P mzero msuc n zero₁' refl = refl
≡-Nat₁-K-like-elim P mzero msuc n (suc₁' n₁ _ n₂) refl = cong (λ n → msuc n₁ n₂ n) 
        (≡-Nat₁-K-like-elim P mzero msuc n₁ n₂ refl)



                    