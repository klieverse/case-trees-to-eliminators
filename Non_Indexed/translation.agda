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

private variable
  ℓ   : Level
  n m : ℕ

-- evaluation function of a case tree ct
eval : {Δ : Telescope n} {T : ⟦ Δ ⟧telD → Set ℓ}
  (ct : CaseTree Δ T) (args : ⟦ Δ ⟧telD)
  → T args
eval (leaf f) args = f args
eval {Δ = Δ} {T} (node {D = D} p bs) args 
  = case-μ D (λ x → ret ≡ x → T args) cs ret refl where 

    -- value that we split on
    ret : μ D 
    ret = proj₂ (args Σ[ p ]) 

    -- from a constructor instantiation that is equivalent to the value 
    -- that we split on get the return type
    cs : (x : ⟦ D ⟧ (μ D)) → ret ≡ ⟨ x ⟩ → T args
    cs (k , xs) e = subst T (shrink∘expand p args _ q) r where

        q : ⟨ k , telToCon (conToTel xs) ⟩ ≡ ret
        q = trans (cong (λ x → ⟨ k , x ⟩) (telToCon∘conToTel xs)) (sym e)

        r : T (shrink p (expand p (λ ys → ⟨ k , telToCon ys ⟩) args (conToTel xs) q))
        r = eval (bs k) (expand p _ args (conToTel xs) q)


-- example translation not function
≡-not : (b : μ BoolD) → eval CTNotRoot (b , tt) ≡ not b
≡-not true'  = refl 
≡-not false' = refl 

-- call below with the evaluation function to create the telescope of +-arguments
+-tel : (n m : μ NatD) → ⟦ +Δ ⟧telD
+-tel n m = n , m , (below +P +p n , tt) where 

    +p : (n : μ NatD) → Below +P n → +P n 
    +p n' b (n , m , tt) e = eval CT+ (n , m , subst (Below +P) e b , tt)

-- example translation + function
≡-+ : (n m : μ NatD) → eval CT+ (+-tel n m) ≡ (n +' m)
≡-+ zero'    m = refl  
≡-+ (suc' n) m = cong suc' (≡-+ n m)


-- call below with the evaluation function to create the telescope of half-arguments
half-tel : (n : μ NatD) → ⟦ halfΔ ⟧telD
half-tel n = n , below (λ n → μ NatD) halfp n , tt where 

    halfp : (n : μ NatD) → Below (λ n → μ NatD) n → μ NatD
    halfp n b = eval CTHalfRoot (n , b , tt)

-- example translation half function
≡-half : (n : μ NatD) → eval CTHalfRoot (half-tel n) ≡ half n
≡-half zero'           = refl  
≡-half (suc' zero')    = refl 
≡-half (suc' (suc' n)) = cong suc' (≡-half n) 

-- example translation create function
create-tel : {X : Set} → (n : μ NatD) → (x : X) → ⟦ createΔ {X} ⟧telD
create-tel {X} n x = (n , (x , (below ((λ n → Vec X n)) createp n , tt))) where 

        createp : (d : μ NatD) → Below ((λ n → Vec X n)) d → Vec X d
        createp d b = eval CTCreateRoot (d , x , (b , tt))

≡-create : {X : Set} (n : μ NatD) (x : X)
    → eval CTCreateRoot (create-tel n x) ≡ create n x
≡-create {X} zero'    x = refl  
≡-create {X} (suc' n) x = cong (consV n x) (≡-create n x) 