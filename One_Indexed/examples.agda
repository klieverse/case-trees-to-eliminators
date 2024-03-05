module One_Indexed.examples where 

import Non_Indexed.datatypes as NI
open import Non_Indexed.telescope
open import One_Indexed.datatypes 
open import One_Indexed.casetrees
open import Non_Indexed.unification
open import Non_Indexed.unify
open import One_Indexed.translation

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Empty
open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ<; toℕ) renaming (zero to fzero; suc to fsuc)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst)
open import Data.Vec using (Vec; []; _∷_)

NatD : NI.DataDesc 2 
NatD fzero = _ , NI.one'
NatD (fsuc fzero) = _ , NI.ind×' NI.one'

pattern zero' = NI.⟨ fzero , tt ⟩ 
pattern suc' n = NI.⟨ fsuc fzero , (n , tt) ⟩

module vector-example where 
    VecTel : DVec 1
    VecTel = (_ , NatD) ∷ []

    VecD : (X : Set) → DataDesc 2 VecTel
    VecD X fzero = _ , one' (zero' , tt) 
    VecD X (fsuc fzero) = _ , Σ' (NI.μ NatD) (λ n → 
        Σ' X (λ x → ×' (n , tt) (one' (suc' n , tt))))
    
    pattern nil' = ⟨ fzero , refl ⟩ 
    pattern cons' n x xs = ⟨ fsuc fzero , (n , (x , (xs , refl))) ⟩

    head' : (X : Set) → (n : NI.μ NatD) → (xs : μ (VecD X) (suc' n , tt)) → X
    head' X n (cons' n x xs) = x

    headΔ : (X : Set) → Telescope 2 
    headΔ X = n ∈ NI.μ NatD , _ ∈ μ (VecD X) (suc' n , tt) , nil

    headT : (X : Set) → ⟦ headΔ X ⟧telD → Set
    headT X _ = X

    CTHeadRoot : (X : Set) → CaseTree (headΔ X) (headT X)
    CTHeadRoot X = node (there (λ n → here (suc' n , tt))) (λ where
                (fzero)      → UnifyZero , leaf (λ where 
                    (n , b , tt) → ⊥-elim b)
                (fsuc fzero) → UnifySuc , leaf (λ where 
                    (n , (x , (xs , _))) → x )) where 
 
        UnifyZero : Unification (n ∈ NI.μ NatD , e ∈ zero' ≡ suc' n , nil) 
        UnifyZero = UConflict (n > here n) (λ d ()) 
                        (UEnd (n ∈ NI.μ NatD , _ ∈ ⊥ , nil))

        CTSucTel : Telescope 5
        CTSucTel = n ∈ NI.μ NatD , m ∈ NI.μ NatD , x ∈ X , v ∈ μ (VecD X) (m , tt) 
                , e ∈ suc' m ≡ suc' n , nil

        UnifySuc : Unification CTSucTel 
        UnifySuc = UReorder (fsuc (fsuc fzero)) fzero (λ x → _ , (there (λ _ → there (λ _ → here)))) 
                    (UInjectivity (n > m > here (m , n)) (λ _ → refl) (λ _ → refl) 
                        (Usolution' (there (λ n → here n)) 
                            (UEnd (n ∈ NI.μ NatD , x ∈ X , v ∈ μ (VecD X) (n , tt) , nil))))

    ≡Head : {X : Set}{x : X}(n : NI.μ NatD)(v : μ (VecD X) (suc' n , tt)) → head' X n v ≡ x 
            → eval (CTHeadRoot X) (n , v , tt) ≡ x 
    ≡Head n (cons' n x xs) refl = refl 

module leq-example where 
    ≤Tel : DVec 2 
    ≤Tel = (_ , NatD) ∷  (_ , NatD) ∷ [] 

    ≤D : DataDesc 2 ≤Tel 
    ≤D fzero        = _ , Σ' (NI.μ NatD) (λ n → one' (zero' , n , tt))
    ≤D (fsuc fzero) = _ , Σ' (NI.μ NatD) (λ n → Σ' (NI.μ NatD) (λ m → ×' (n , m , tt) (one' (suc' n , suc' m , tt))))

    pattern lz n = ⟨ fzero , (n , refl) ⟩
    pattern ls n m x = ⟨ fsuc fzero , (n , m , x , refl) ⟩ 

    antisym : (n m : NI.μ NatD)(x : μ ≤D (n , m , tt))(y : μ ≤D (m , n , tt)) → n ≡ m 
    antisym .zero' .zero' (lz .zero') (lz .zero') = refl
    antisym .zero' m (lz .m) ⟨ fsuc fzero , _ , n , _ , () ⟩
    antisym .(suc' n) .(suc' m) (ls n m x) (ls .m .n y) = cong suc' (antisym n m x y)

    antisymPx : (d : ⟦ ≤Tel ⟧Vec) → μ ≤D d → Set 
    antisymPx d x = (t : ⟦ n ∈ NI.μ NatD , m ∈ NI.μ NatD , x ∈ μ ≤D (n , m , tt) , y ∈ μ ≤D (m , n , tt) , nil ⟧telD) 
                    → (d , x) ≡ (((proj₁ t) , (proj₁ (proj₂ t)) , tt) , proj₁ (proj₂ (proj₂ t)))
                    → (proj₁ t) ≡ proj₁ (proj₂ t)

    -- antisymΔ : Telescope 5 
    -- antisymΔ = n ∈ NI.μ NatD , m ∈ NI.μ NatD , x ∈ μ ≤D (n , m , tt) , y ∈ μ ≤D (m , n , tt) 
    --             , b ∈ Below antisymPx (n , m , tt) x , nil

    -- antisymT : ⟦ antisymΔ ⟧telD → Set
    -- antisymT (n , m , _) = n ≡ m 

    -- CTantisym : CaseTree antisymΔ antisymT
    -- CTantisym = node (n > m > here (n , m , tt)) (λ where 
    --                 (fzero) → Unify₀ , node (m > here (m , zero' , tt)) (λ where 
    --                     (fzero) → Unify₀₀ , leaf (λ _ → refl) 
    --                     (fsuc fzero) → Unify₀₁ , leaf (λ where 
    --                         (m , n , b , _) → ⊥-elim b))
    --                 (fsuc fzero) → Unify₁ , node (n' > m' > x > here (suc' m' , suc' n' , tt)) (λ where 
    --                     (fzero) → Unify₁₀ , leaf (λ where 
    --                         (m , n , x , b , _) → ⊥-elim b)
    --                     (fsuc fzero) → Unify₁₁ , leaf (λ where 
    --                         (n , m , x , y , ((H , _) , _) , _) → cong suc' (H (n , m , x , y , tt) refl) ))) where


    --     antisymΔ₀ : Telescope 8
    --     antisymΔ₀ = n ∈ NI.μ NatD , m ∈ NI.μ NatD , m' ∈ NI.μ NatD , 
    --                 en ∈ zero' ≡ n , em ∈ m' ≡ m , et ∈ tt ≡ tt ,
    --                 y ∈ μ ≤D (m , n , tt) , b ∈ Lift lzero ⊤ , nil
        
    --     Unify₀ : Unification antisymΔ₀ 
    --     Unify₀ = UReorder (fsuc fzero) fzero (λ x → _ , there (λ _ → there (λ _ → here))) 
    --                 (Usolution (here zero') 
    --                     (Usolution' (there (λ m → here m)) 
    --                         (UDeletion (there (λ _ → here tt)) 
    --                             (UEnd (m ∈ NI.μ NatD , y ∈ μ ≤D (m , zero' , tt) , b ∈ Lift lzero ⊤ , nil))))) 

    --     antisymΔ₀₀ : Telescope 6
    --     antisymΔ₀₀ = m ∈ NI.μ NatD , m' ∈ NI.μ NatD , 
    --                 en ∈ zero' ≡ m , em ∈ m' ≡ zero' , et ∈ tt ≡ tt ,
    --                 b ∈ Lift lzero ⊤ , nil
        
    --     Unify₀₀ : Unification antisymΔ₀₀
    --     Unify₀₀ = UReorder (fsuc fzero) fzero (λ x → _ , there (λ _ → here)) 
    --                 (Usolution (here zero') 
    --                     (Usolution' (here zero') 
    --                         (UDeletion (here tt) 
    --                             (UEnd (b ∈ Lift lzero ⊤ , nil)))))

    --     antisymΔ₀₁ : Telescope 8
    --     antisymΔ₀₁ = m ∈ NI.μ NatD , m' ∈ NI.μ NatD , n' ∈ NI.μ NatD , y ∈ μ ≤D (m' , n' , tt) ,
    --                 en ∈ suc' m' ≡ m , em ∈ suc' n' ≡ zero' , et ∈ tt ≡ tt ,
    --                 b ∈ Lift lzero ⊤ , nil 
        
    --     Unify₀₁ : Unification antisymΔ₀₁
    --     Unify₀₁ = UReorder fzero fzero (λ _ → _ , there (λ _ → here)) 
    --                 (UReorder (fsuc (fsuc fzero)) fzero (λ x → _ , there (λ _ → there (λ _ → here))) 
    --                     (Usolution (there (λ m' → here (suc' m'))) 
    --                         (UReorder (fsuc (fsuc fzero)) fzero (λ x → _ , there (λ _ → here)) 
    --                             (UConflict (there (λ m → there (λ n → here n))) (λ d ())  
    --                                 (UDeletion (_ > _ > _ > _ > here tt) 
    --                                     (UEnd ( m ∈ NI.μ NatD , n ∈ NI.μ NatD , b ∈ ⊥ , y ∈ μ ≤D (m , n , tt) 
    --                                             , _ ∈ Lift lzero ⊤ , nil )))))))

    --     antisymΔ₁ : Telescope 10
    --     antisymΔ₁ = n ∈ NI.μ NatD , m ∈ NI.μ NatD ,  
    --                 n' ∈ NI.μ NatD , m' ∈ NI.μ NatD , x ∈ μ ≤D (n' , m' , tt) ,
    --                 en ∈ suc' n' ≡ n , em ∈ suc' m' ≡ m , et ∈ tt ≡ tt ,
    --                 y ∈ μ ≤D (m , n , tt) , b ∈ (antisymPx (n' , m' , tt) x × 
    --                     Below antisymPx (n' , m' , tt) x) × Lift lzero ⊤ , nil
        
    --     Unify₁ : Unification antisymΔ₁ 
    --     Unify₁ = UReorder fzero fzero (λ _ → _ , there (λ _ → there (λ _ → here))) 
    --                 (UReorder (fsuc (fsuc fzero)) fzero (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → here)))) 
    --                     (Usolution (there (λ n' → here (suc' n'))) 
    --                         (UReorder (fsuc fzero) fzero ((λ _ → _ , there (λ _ → here))) 
    --                             (UReorder (fsuc (fsuc (fsuc fzero))) fzero (λ _ → _ , there (λ _ → here)) 
    --                                 (Usolution (there (λ n' → there (λ m' → here (suc' m')))) 
    --                                     (UDeletion (there (λ _ → there λ _ → there λ _ → here tt)) 
    --                                         (UEnd (n' ∈ NI.μ NatD , m' ∈ NI.μ NatD , x ∈ μ ≤D (n' , m' , tt) , 
    --                                             y ∈ μ ≤D (suc' m' , suc' n' , tt) , b ∈ (antisymPx (n' , m' , tt) x × 
    --                                             Below antisymPx (n' , m' , tt) x) × Lift lzero ⊤ , nil )))))))) 

    --     antisymΔ₁₀ : Telescope 8 
    --     antisymΔ₁₀ = n' ∈ NI.μ NatD , m' ∈ NI.μ NatD , x ∈ μ ≤D (n' , m' , tt) , 
    --                 m'' ∈ NI.μ NatD , en ∈ zero' ≡ suc' m' , em ∈ m'' ≡ suc' n' , 
    --                 et ∈ tt ≡ tt , b ∈ (antisymPx (n' , m' , tt) x × Below antisymPx (n' , m' , tt) x) 
    --                     × Lift lzero ⊤ , nil 

    --     Unify₁₀ : Unification antisymΔ₁₀ 
    --     Unify₁₀ = UConflict (there (λ n' → (there (λ m' → (there (λ x → (there (λ m'' → here m')))))))) (λ d ())
    --                 (UDeletion (there (λ _ → there (λ _ → there (λ _ → there (λ _ → there (λ _ → there (λ _ → here tt))))))) 
    --                     (UReorder (fsuc fzero) fzero (λ _ → _ , there (λ _ → there (λ _ → here))) 
    --                         (UReorder (fsuc (fsuc fzero)) fzero (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → here)))) 
    --                             (Usolution' (there (λ n' → here (suc' n'))) 
    --                                 (UEnd (n' ∈ NI.μ NatD , m' ∈ NI.μ NatD , x ∈ μ ≤D (n' , m' , tt) , b ∈ ⊥ , 
    --                                     b ∈ (antisymPx (n' , m' , tt) x × Below antisymPx (n' , m' , tt) x) 
    --                                     × Lift lzero ⊤ , nil)))))) 

    --     antisymΔ₁₁ : Telescope 10 
    --     antisymΔ₁₁ = n' ∈ NI.μ NatD , m' ∈ NI.μ NatD , x ∈ μ ≤D (n' , m' , tt) , 
    --                  m'' ∈ NI.μ NatD , n'' ∈ NI.μ NatD , y ∈ μ ≤D (m'' , n'' , tt) , 
    --                  em ∈ suc' m'' ≡ suc' m' , en ∈ suc' n'' ≡ suc' n' , et ∈ tt ≡ tt , 
    --                  b ∈ (antisymPx (n' , m' , tt) x × Below antisymPx (n' , m' , tt) x) 
    --                     × Lift lzero ⊤ , nil 
                        
    --     Unify₁₁ : Unification antisymΔ₁₁
    --     Unify₁₁ = UReorder (fsuc fzero) fzero (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → here)))) 
    --                 (UReorder (fsuc (fsuc (fsuc fzero))) fzero (λ _ → _ , there (λ _ → here)) 
    --                     (UReorder (fsuc (fsuc fzero)) fzero (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → there (λ _ → there (λ _ → here)))))) 
    --                         (UReorder (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) fzero (λ _ → _ , there (λ _ → there (λ _ → here))) 
    --                             (UInjectivity (there (λ n' → there (λ n'' → here (n' , n'')))) (λ _ → refl) (λ _ → refl) 
    --                                 (UInjectivity (there (λ n' → there (λ n'' → there (λ e → there (λ m' → there (λ m'' → here (m' , m''))))))) (λ _ → refl) (λ _ → refl) 
    --                                     (Usolution' (there (λ n' → here n')) 
    --                                         (Usolution' (there (λ n' → there (λ m' → here m'))) 
    --                                             (UDeletion (there (λ _ → there λ _ → there λ _ → there λ _ → here tt)) 
    --                                                 (UEnd (n' ∈ NI.μ NatD , m' ∈ NI.μ NatD , x ∈ μ ≤D (n' , m' , tt) , y ∈ μ ≤D (m' , n' , tt) , 
    --                                                     b ∈ (antisymPx (n' , m' , tt) x × Below antisymPx (n' , m' , tt) x) 
    --                                                     × Lift lzero ⊤ , nil))))))))))   
        

    -- -- translation
    -- antisym-tel : (n m : NI.μ NatD)(x : μ ≤D (n , m , tt))(y : μ ≤D (m , n , tt)) → ⟦ antisymΔ ⟧telD
    -- antisym-tel n m x y = n , m , x , y , below antisymPx createp ((n , m , tt)) x , tt  where

    --         createp : (d : ⟦ ≤Tel ⟧Vec) → (x : μ ≤D d) → Below antisymPx d x → antisymPx d x
    --         createp d x b ( _ , _ , _ , y , _ ) refl = eval CTantisym (proj₁ d , proj₁ (proj₂ d) , x , y , b , tt) 

    -- antisym-elim : (n m : NI.μ NatD)(x : μ ≤D (n , m , tt))(y : μ ≤D (m , n , tt)) →
    --     {e : n ≡ m } → antisym n m x y ≡ e 
    --     → eval CTantisym (antisym-tel n m x y) ≡ e
    -- antisym-elim .zero' .zero' (lz .zero') (lz .zero') refl = refl
    -- antisym-elim .zero' m (lz .m) ⟨ fsuc fzero , _ , n , _ , () ⟩ refl
    -- antisym-elim .(suc' n) .(suc' m) (ls n m x) (ls .m .n y) refl = cong (λ n → cong suc' n) (antisym-elim n m x y refl)

module nat₁-example where 
    Nat₁Tel : DVec 2
    Nat₁Tel = (_ , NatD) ∷  (_ , NatD) ∷ []

    Nat₁D : DataDesc 2 Nat₁Tel 
    Nat₁D fzero = _ , one' (zero' , (zero' , tt))
    Nat₁D (fsuc fzero) = _ ,  Σ' (NI.μ NatD) (λ n₁ → Σ' (NI.μ NatD) (λ n₂ 
                                → ×' (n₁ , (n₂ , tt)) (one' (suc' n₁ , (suc' n₂ , tt)))))
    
    pattern zero₁' = ⟨ fzero , refl ⟩
    pattern suc₁' n₁ n₂ n = ⟨ fsuc fzero , (n₁ , (n₂ , (n , refl))) ⟩ 
    
    Nat₁-K-like-elim : (P : (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) 
                        (mzero : P zero' zero₁')
                        (msuc : (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
                                P n₀ n₁ → P (suc' n₀) (suc₁' n₀ n₀ n₁))
                        (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → P n₀ n₁
    Nat₁-K-like-elim P mzero msuc n zero₁' = mzero
    Nat₁-K-like-elim P mzero msuc n (suc₁' n₁ _ n₂) = msuc n₁ n₂ (Nat₁-K-like-elim P mzero msuc n₁ n₂) 

    Nat₁-K-like-elimPx : (P : (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) → (d : ⟦ Nat₁Tel ⟧Vec) → μ Nat₁D d → Set 
    Nat₁-K-like-elimPx P d x = (t : ⟦ mzero ∈ P zero' zero₁' , msuc ∈ ((n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
                                P n₀ n₁ → P (suc' n₀) (suc₁' n₀ n₀ n₁)) , n₀ ∈ NI.μ NatD , n₁ ∈ μ Nat₁D (n₀ , (n₀ , tt)) , nil ⟧telD) 
                        → (d , x) ≡ ((proj₁ (proj₂ (proj₂ t)) , (proj₁ (proj₂ (proj₂ t))) , tt) , proj₁ (proj₂ (proj₂ (proj₂ t))))
                        → P (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ t))))
    
    Nat₁-K-like-elimΔ : (P : (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) → Telescope 5 
    Nat₁-K-like-elimΔ P = mzero ∈ (P zero' zero₁') , 
                          msuc ∈ ((n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
                                P n₀ n₁ → P (suc' n₀) (suc₁' n₀ n₀ n₁)) , 
                          n₀ ∈ NI.μ NatD , 
                          n₁ ∈ μ Nat₁D (n₀ , (n₀ , tt)) ,
                          b ∈ Below (Nat₁-K-like-elimPx P) (n₀ , (n₀ , tt)) n₁ ,
                          nil

    Nat₁-K-like-elimT : (P : (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) 
            → ⟦ Nat₁-K-like-elimΔ P ⟧telD → Set
    Nat₁-K-like-elimT P (mzero , (msuc , (n₀ , (n₁ , (b , tt))))) = P n₀ n₁

    -- CTNat₁-K-like-elim : (P : (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) 
    --     → CaseTree (Nat₁-K-like-elimΔ P) (Nat₁-K-like-elimT P)
    -- CTNat₁-K-like-elim P = node (there (λ mzero → there (λ msuc → there (λ n₀ → here (n₀ , (n₀ , tt)))))) (λ where
    --             (fzero) → Unify₀ , leaf (λ where 
    --                 (mzero , msuc , _) → mzero) 
    --             (fsuc fzero) → Unify₁ , leaf (λ where 
    --                 (mzero , msuc , n₀ , n , ((H , _) , _) , _ ) → msuc n₀ n (H (mzero , msuc , n₀ , n , tt) refl))) where 

    --     Δ₀ : Telescope 7 
    --     Δ₀ = mzero ∈ (P zero' zero₁') , msuc ∈ ((n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
    --             P n₀ n₁ → P (suc' n₀) (suc₁' n₀ n₀ n₁)) , n₀ ∈ NI.μ NatD , e₁ ∈ zero' ≡ n₀ , 
    --             e₂ ∈ zero' ≡ n₀ , en ∈ tt ≡ tt , b ∈ Lift lzero ⊤ , nil 

    --     Unify₀ : Unification Δ₀ 
    --     Unify₀ = Usolution (there (λ mzero → there (λ msuc → here zero'))) 
    --                 (UDeletion (there (λ mzero → there (λ msuc → here tt))) 
    --                     (UDeletion (there (λ mzero → there (λ msuc → here tt))) 
    --                         (UEnd (mzero ∈ (P zero' zero₁') , msuc ∈ ((n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
    --                             P n₀ n₁ → P (suc' n₀) (suc₁' n₀ n₀ n₁)) , b ∈ Lift lzero ⊤ , nil))))

    --     Δ₁ : Telescope 10 
    --     Δ₁ = mzero ∈ (P zero' zero₁') , msuc ∈ ((n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → P n₀ n₁ → P (suc' n₀) (suc₁' n₀ n₀ n₁)) , 
    --          n₀ ∈ NI.μ NatD , n₁ ∈ NI.μ NatD , n₂ ∈ NI.μ NatD , n ∈ μ Nat₁D (n₁ , (n₂ , tt)) , 
    --          e₁ ∈ suc' n₁ ≡ n₀ , e₂ ∈ suc' n₂ ≡ n₀ , et ∈ tt ≡ tt , 
    --          b ∈ (Nat₁-K-like-elimPx P (n₁ , n₂ , tt) n × Below (Nat₁-K-like-elimPx P) (n₁ , n₂ , tt) n) × Lift lzero ⊤ , nil

    --     Unify₁ : Unification Δ₁
    --     Unify₁ = UReorder (fsuc (fsuc (fsuc (fsuc fzero)))) fzero (λ _ → _ , there (λ _ → there (λ _ → here))) 
    --                 (UReorder (fsuc (fsuc fzero)) fzero (λ _ → _ , there λ _ → here) 
    --                     (Usolution (there (λ _ → there (λ _ → there (λ n₁ → here (suc' n₁))))) 
    --                         (UReorder (fsuc (fsuc (fsuc (fsuc fzero)))) fzero (λ _ → _ , there (λ _ → here)) 
    --                             (UInjectivity (there (λ mzero → there (λ msuc → there (λ n₁ → there (λ n₂ → here (n₁ , n₂)))))) (λ _ → refl) (λ _ → refl) 
    --                                 (Usolution' (there (λ mzero → there (λ msuc → there (λ n₁ → here n₁)))) 
    --                                     (UDeletion (there (λ mzero → there (λ msuc → there (λ n₁ → there (λ n → here tt))))) 
    --                                         (UEnd (mzero ∈ (P zero' zero₁') , msuc ∈ ((n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → P n₀ n₁ → P (suc' n₀) (suc₁' n₀ n₀ n₁)) , 
    --                                                 n₀ ∈ NI.μ NatD , n ∈ μ Nat₁D (n₀ , (n₀ , tt)) , b ∈ (Nat₁-K-like-elimPx P (n₀ , n₀ , tt) n × Below (Nat₁-K-like-elimPx P) (n₀ , n₀ , tt) n) × Lift lzero ⊤ , nil))))))))


    -- -- translation
    -- Nat₁-K-like-elim-tel : (P : (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) 
    --             (mzero : P zero' zero₁')
    --             (msuc : (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
    --                     P n₀ n₁ → P (suc' n₀) (suc₁' n₀ n₀ n₁))
    --             (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → ⟦ Nat₁-K-like-elimΔ P ⟧telD
    -- Nat₁-K-like-elim-tel P mzero msuc n₀ n₁ = mzero , msuc , n₀ , n₁ , below (Nat₁-K-like-elimPx P) createp ((n₀ , n₀ , tt)) n₁ , tt  where --  (n , (x , (below ((λ n → Vec X n)) createp n , tt))) where 

    --         createp : (d : ⟦ Nat₁Tel ⟧Vec) → (x : μ Nat₁D d) → Below (Nat₁-K-like-elimPx P) d x → Nat₁-K-like-elimPx P d x
    --         createp d x b t refl = eval (CTNat₁-K-like-elim P) (mzero , msuc , proj₁ d , x , b , tt) 

    -- ≡-Nat₁-K-like-elim : (P : (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) 
    --     (mzero : P zero' zero₁')
    --     (msuc : (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
    --             P n₀ n₁ → P (suc' n₀) (suc₁' n₀ n₀ n₁))
    --     (n₀ : NI.μ NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) →
    --     {x : P n₀ n₁} → Nat₁-K-like-elim P mzero msuc n₀ n₁ ≡ x 
    --     → eval (CTNat₁-K-like-elim P) (Nat₁-K-like-elim-tel P mzero msuc n₀ n₁) ≡ x
    -- ≡-Nat₁-K-like-elim P mzero msuc n zero₁' refl = refl
    -- ≡-Nat₁-K-like-elim P mzero msuc n (suc₁' n₁ _ n₂) refl = cong (λ n → msuc n₁ n₂ n) 
    --         (≡-Nat₁-K-like-elim P mzero msuc n₁ n₂ refl)