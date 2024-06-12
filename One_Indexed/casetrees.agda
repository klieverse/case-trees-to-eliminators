{-# OPTIONS --safe #-}
module One_Indexed.casetrees where
    
import Non_Indexed.datatypes as NI
open import One_Indexed.datatypes
open import Non_Indexed.telescope
open import One_Indexed.unify
open import lib

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Empty
open import Agda.Builtin.Unit
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _∸_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ<; toℕ) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Data.Vec using (Vec; []; _∷_)
 
private variable
  cₙ aₙ iₙ : ℕ 
  is  : DVec iₙ
  n k : ℕ
  ℓ   : Level

-- telescope of equivalent indices
vecTel : {is : DVec iₙ} (is₁ is₂ : ⟦ is ⟧Vec) → Telescope iₙ 
vecTel {is = []    } tt tt = nil 
vecTel {is = i ∷ is} (i₁ , is₁) (i₂ , is₂) = e ∈ (i₁ ≡ i₂) , vecTel is₁ is₂

-- telescope of constructor arguments for constructor description C on X
conTel : {is : DVec iₙ} → (⟦ is ⟧Vec → Set) → ConDesc is aₙ → ⟦ is ⟧Vec → Telescope (aₙ + iₙ)
conTel X (one' i') i = vecTel i' i
conTel X (Σ' S C ) i = s ∈ S , conTel X (C s) i
conTel X (×' i' C) i = μD ∈ X i' , conTel X C i

-- telescope of constructor arguments for constructor description C on X
telToVec : {is : DVec iₙ}{is₁ is₂ : ⟦ is ⟧Vec} (t : ⟦ vecTel is₁ is₂ ⟧telD) → is₁ ≡ is₂
telToVec {is = []    } tt = refl
telToVec {is = i ∷ is} (t , ts) = ×-create t (telToVec ts) 

telToCon : {X : ⟦ is ⟧Vec → Set}{C : ConDesc is aₙ}{i : ⟦ is ⟧Vec}
    → (t : ⟦ conTel X C i ⟧telD) → ⟦ C ⟧c X i
telToCon {C = one' d'} {d} v = telToVec v
telToCon {C = Σ' S C} (s , t) = s , telToCon t
telToCon {C = ×' d' C} (μD , t) = μD , telToCon t

-- instantiation of conTel from interpretation of constructor interpretation on X
vecToTel : {is : DVec iₙ}{is₁ is₂ : ⟦ is ⟧Vec}
    → is₁ ≡ is₂ → ⟦ vecTel is₁ is₂ ⟧telD
vecToTel {is = []    } e = tt
vecToTel {is = i ∷ is} e = proj×₁ e , (vecToTel (proj×₂ e))

conToTel : {X : ⟦ is ⟧Vec → Set}{C : ConDesc is aₙ}{i : ⟦ is ⟧Vec}
    → ⟦ C ⟧c X i → ⟦ conTel X C i ⟧telD
conToTel {C = one' v} e        = vecToTel e
conToTel {C = Σ' S C} (s , t)  = s , conToTel t 
conToTel {C = ×' i C} (μD , t) = μD , conToTel t

-- proof of section-retraction pair
telToVec∘vecToTel : {is : DVec iₙ}{is₁ is₂ : ⟦ is ⟧Vec} (e : is₁ ≡ is₂) → telToVec (vecToTel e) ≡ e
telToVec∘vecToTel {is = []    } {is₁ = tt} {is₂ = tt} e = J' (λ _ e' → e' ≡ e) e refl
telToVec∘vecToTel {is = i ∷ is} {is₁ = (i₁ , is₁)} {is₂ = (i₂ , is₂)} e 
  = subst (λ f → ×-create (proj×₁ e) f ≡ e) (sym (telToVec∘vecToTel (proj×₂ e))) (create∘proj× e)

telToCon∘conToTel : {X : ⟦ is ⟧Vec → Set}{C : ConDesc is aₙ}{i : ⟦ is ⟧Vec}
    → (t : ⟦ C ⟧c X i) → telToCon (conToTel t) ≡ t 
telToCon∘conToTel {C = one' v} e        = telToVec∘vecToTel e
telToCon∘conToTel {C = Σ' S C} (s , t)  = cong (s ,_) (telToCon∘conToTel t)
telToCon∘conToTel {C = ×' i C} (μD , t) = cong (μD ,_) (telToCon∘conToTel t)


-- representation of a case tree
data CaseTree (Δ : Telescope n)(T : ⟦ Δ ⟧telD → Set ℓ) : Set (lsuc ℓ) where
    leaf : (t : (args : ⟦ Δ ⟧telD) → T args) → CaseTree Δ T
    node : {D : DataDesc is cₙ}(p : Δ [ k ]∶Σ[ ⟦ is ⟧Vec ] (μ D))
        → (bs : (cᵢ : Fin cₙ) 
            -- add unification algorithm for indices
            → Σ[ u ∈ Unification (expandTel Δ (conTel (μ D) (proj₂ (D cᵢ))) 
                    p (λ args → ⟨ cᵢ , telToCon args ⟩))] 
                (CaseTree (proj₂ (unifyTel u)) 
                    (λ args → T (shrink p (unify' u args)))))
        → CaseTree Δ T


-- example case tree head function
headΔ : (X : Set) → Telescope 2 
headΔ X = n ∈ NI.μ NI.NatD , _ ∈ μ (VecD X) (NI.suc' n , tt) , nil

headT : (X : Set) → ⟦ headΔ X ⟧telD → Set
headT X _ = X

CTHeadRoot : (X : Set) → CaseTree (headΔ X) (headT X)
CTHeadRoot X = node (there (λ n → here (NI.suc' n , tt))) (λ where
            f0 → UnifyZero , leaf (λ where 
                (n , b , tt) → ⊥-elim b)
            f1 → UnifySuc X , leaf (λ where 
                (n , (x , (xs , _))) → x )) 
 
-- example antisym function 
antisymPx : (d : ⟦ ≤Tel ⟧Vec) → μ ≤D d → Set 
antisymPx d x = (t : ⟦ n ∈ NI.μ NI.NatD , m ∈ NI.μ NI.NatD , x ∈ μ ≤D (n , m , tt) , y ∈ μ ≤D (m , n , tt) , nil ⟧telD) 
                → (d , x) ≡ (((proj₁ t) , (proj₁ (proj₂ t)) , tt) , proj₁ (proj₂ (proj₂ t)))
                → (proj₁ t) ≡ proj₁ (proj₂ t)

antisymΔ : Telescope 5 
antisymΔ = n ∈ NI.μ NI.NatD , m ∈ NI.μ NI.NatD , x ∈ μ ≤D (n , m , tt) , y ∈ μ ≤D (m , n , tt) 
            , b ∈ Below antisymPx (n , m , tt) x , nil

antisymT : ⟦ antisymΔ ⟧telD → Set
antisymT (n , m , _) = n ≡ m 

CTantisym : CaseTree antisymΔ antisymT
CTantisym = node (there (λ n → there (λ m → here (n , m , tt)))) (λ where 
                f0 → Unify₀ , node (there (λ m → here (m , NI.zero' , tt))) (λ where 
                    f0 → Unify₀₀ , leaf (λ _ → refl) 
                    f1 → Unify₀₁ , leaf (λ where (m , n , b , _) → ⊥-elim b))
                f1 → Unify₁ , node (there (λ n' → there (λ m' → there (λ x → here (NI.suc' m' , NI.suc' n' , tt))))) (λ where 
                    f0 → Unify₁₀ , leaf (λ where (m , n , x , b , _) → ⊥-elim b)
                    f1 → Unify₁₁ , leaf (λ where (n , m , x , y , ((H , _) , _) , _) → cong NI.suc' (H (n , m , x , y , tt) refl) ))) where


    antisymΔ₀ : Telescope 7
    antisymΔ₀ = n ∈ NI.μ NI.NatD , m ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , 
                en ∈ NI.zero' ≡ n , em ∈ m' ≡ m , 
                y ∈ μ ≤D (m , n , tt) , b ∈ Lift lzero ⊤ , nil
    
    Unify₀ : Unification antisymΔ₀ 
    Unify₀ = UReorder f1 f0 (λ x → _ , there (λ _ → there (λ _ → here tt))) 
                (Usolution {A = ⊤} (here (tt , NI.zero')) 
                    (Usolution₁ {A = ⊤} (there (λ m → here (tt , m))) 
                            (UEnd (m ∈ NI.μ NI.NatD , y ∈ μ ≤D (m , NI.zero' , tt) , b ∈ Lift lzero ⊤ , nil)))) 

    antisymΔ₀₀ : Telescope 5
    antisymΔ₀₀ = m ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , 
                en ∈ NI.zero' ≡ m , em ∈ m' ≡ NI.zero' , 
                b ∈ Lift lzero ⊤ , nil
    
    Unify₀₀ : Unification antisymΔ₀₀
    Unify₀₀ = UReorder f1 f0 (λ x → _ , there (λ _ → here tt)) 
                (Usolution {A = ⊤} (here (tt , NI.zero')) 
                    (Usolution₁ {A = ⊤} (here (tt , NI.zero')) 
                            (UEnd (b ∈ Lift lzero ⊤ , nil))))

    antisymΔ₀₁ : Telescope 7
    antisymΔ₀₁ = m ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , n' ∈ NI.μ NI.NatD , y ∈ μ ≤D (m' , n' , tt) ,
                en ∈ NI.suc' m' ≡ m , em ∈ NI.suc' n' ≡ NI.zero' ,
                b ∈ Lift lzero ⊤ , nil 
    
    Unify₀₁ : Unification antisymΔ₀₁
    Unify₀₁ = UReorder f0 f0 (λ _ → _ , there (λ _ → here tt)) 
                (UReorder f2 f0 (λ x → _ , there (λ _ → there (λ _ → here tt))) 
                    (Usolution {A = ⊤} (there (λ m' → here (tt , NI.suc' m'))) 
                        (UReorder f2 f0 (λ x → _ , there (λ _ → here tt)) 
                            (UConflict (there (λ m → there (λ n → here n))) (λ d ())  
                                    (UEnd ( m ∈ NI.μ NI.NatD , n ∈ NI.μ NI.NatD , b ∈ ⊥ , y ∈ μ ≤D (m , n , tt) 
                                            , _ ∈ Lift lzero ⊤ , nil ))))))

    antisymΔ₁ : Telescope 9
    antisymΔ₁ = n ∈ NI.μ NI.NatD , m ∈ NI.μ NI.NatD ,  
                n' ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , x ∈ μ ≤D (n' , m' , tt) ,
                en ∈ NI.suc' n' ≡ n , em ∈ NI.suc' m' ≡ m , 
                y ∈ μ ≤D (m , n , tt) , b ∈ (antisymPx (n' , m' , tt) x × 
                    Below antisymPx (n' , m' , tt) x) × Lift lzero ⊤ , nil
    
    Unify₁ : Unification antisymΔ₁ 
    Unify₁ = UReorder f0 f0 (λ _ → _ , there (λ _ → there (λ _ → here tt))) 
                (UReorder f2 f0 (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → here tt)))) 
                    (Usolution {A = ⊤} (there (λ n' → here (tt , NI.suc' n'))) 
                        (UReorder f1 f0 ((λ _ → _ , there (λ _ → here tt))) 
                            (UReorder f3 f0 (λ _ → _ , there (λ _ → here tt)) 
                                (Usolution {A = ⊤} (there (λ n' → there (λ m' → here (tt , NI.suc' m')))) 
                                        (UEnd (n' ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , x ∈ μ ≤D (n' , m' , tt) , 
                                            y ∈ μ ≤D (NI.suc' m' , NI.suc' n' , tt) , b ∈ (antisymPx (n' , m' , tt) x × 
                                            Below antisymPx (n' , m' , tt) x) × Lift lzero ⊤ , nil )))))))

    antisymΔ₁₀ : Telescope 7 
    antisymΔ₁₀ = n' ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , x ∈ μ ≤D (n' , m' , tt) , 
                m'' ∈ NI.μ NI.NatD , en ∈ NI.zero' ≡ NI.suc' m' , em ∈ m'' ≡ NI.suc' n' , 
                b ∈ (antisymPx (n' , m' , tt) x × Below antisymPx (n' , m' , tt) x) 
                    × Lift lzero ⊤ , nil 

    Unify₁₀ : Unification antisymΔ₁₀ 
    Unify₁₀ = UConflict (there (λ n' → (there (λ m' → (there (λ x → (there (λ m'' → here m')))))))) (λ d ())
                    (UReorder f1 f0 (λ _ → _ , there (λ _ → there (λ _ → here tt))) 
                        (UReorder f2 f0 (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → here tt)))) 
                            (Usolution₁ {A = ⊤} (there (λ n' → here (tt , NI.suc' n'))) 
                                (UEnd (n' ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , x ∈ μ ≤D (n' , m' , tt) , b ∈ ⊥ , 
                                    b ∈ (antisymPx (n' , m' , tt) x × Below antisymPx (n' , m' , tt) x) 
                                    × Lift lzero ⊤ , nil)))))

    antisymΔ₁₁ : Telescope 9 
    antisymΔ₁₁ = n' ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , x ∈ μ ≤D (n' , m' , tt) , 
                    m'' ∈ NI.μ NI.NatD , n'' ∈ NI.μ NI.NatD , y ∈ μ ≤D (m'' , n'' , tt) , 
                    em ∈ NI.suc' m'' ≡ NI.suc' m' , en ∈ NI.suc' n'' ≡ NI.suc' n' ,
                    b ∈ (antisymPx (n' , m' , tt) x × Below antisymPx (n' , m' , tt) x) 
                    × Lift lzero ⊤ , nil 
                    
    Unify₁₁ : Unification antisymΔ₁₁
    Unify₁₁ = UReorder f1 f0 (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → here tt)))) 
                (UReorder f3 f0 (λ _ → _ , there (λ _ → here tt)) 
                    (UReorder f2 f0 (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → there (λ _ → there (λ _ → here tt)))))) 
                        (UReorder f5 f0 (λ _ → _ , there (λ _ → there (λ _ → here tt))) 
                            (UInjectivity (there (λ n' → there (λ n'' → here (n' , n'')))) (λ _ → refl) (λ _ → refl) 
                                (UInjectivity (there (λ n' → there (λ n'' → there (λ e → there (λ m' → there (λ m'' → here (m' , m''))))))) (λ _ → refl) (λ _ → refl) 
                                    (Usolution₁ {A = ⊤} (there (λ n' → here (tt , n'))) 
                                        (Usolution₁ {A = ⊤} (there (λ n' → there (λ m' → here (tt , m')))) 
                                                (UEnd (n' ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , x ∈ μ ≤D (n' , m' , tt) , y ∈ μ ≤D (m' , n' , tt) , 
                                                    b ∈ (antisymPx (n' , m' , tt) x × Below antisymPx (n' , m' , tt) x) 
                                                    × Lift lzero ⊤ , nil)))))))))
    



-- example Nat₁-K-like-elim case tree
Nat₁-K-like-elimPx : (P : (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) → (d : ⟦ Nat₁Tel ⟧Vec) → μ Nat₁D d → Set 
Nat₁-K-like-elimPx P d x = (t : ⟦ mzero ∈ P NI.zero' zero₁' , msuc ∈ ((n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
            P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁)) , n₀ ∈ NI.μ NI.NatD , n₁ ∈ μ Nat₁D (n₀ , (n₀ , tt)) , nil ⟧telD) 
    → (d , x) ≡ ((proj₁ (proj₂ (proj₂ t)) , (proj₁ (proj₂ (proj₂ t))) , tt) , proj₁ (proj₂ (proj₂ (proj₂ t))))
    → P (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ t))))

Nat₁-K-like-elimΔ : (P : (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) → Telescope 5 
Nat₁-K-like-elimΔ P = mzero ∈ (P NI.zero' zero₁') , 
    msuc ∈ ((n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
        P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁)) , 
    n₀ ∈ NI.μ NI.NatD , 
    n₁ ∈ μ Nat₁D (n₀ , (n₀ , tt)) ,
    b ∈ Below (Nat₁-K-like-elimPx P) (n₀ , (n₀ , tt)) n₁ ,
    nil

Nat₁-K-like-elimT : (P : (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) 
    → ⟦ Nat₁-K-like-elimΔ P ⟧telD → Set
Nat₁-K-like-elimT P (mzero , (msuc , (n₀ , (n₁ , (b , tt))))) = P n₀ n₁

CTNat₁-K-like-elim : (P : (n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → Set) 
    → CaseTree (Nat₁-K-like-elimΔ P) (Nat₁-K-like-elimT P)
CTNat₁-K-like-elim P = node (there (λ mzero → there (λ msuc → there (λ n₀ → here (n₀ , (n₀ , tt)))))) (λ where
            f0 → Unify₀ , leaf (λ where (mzero , msuc , _) → mzero) 
            f1 → Unify₁ , leaf (λ where 
                (mzero , msuc , n₀ , n , ((H , _) , _) , _ ) → msuc n₀ n (H (mzero , msuc , n₀ , n , tt) refl))) where 

    Δ₀ : Telescope 6 
    Δ₀ = mzero ∈ (P NI.zero' zero₁') , msuc ∈ ((n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
            P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁)) , n₀ ∈ NI.μ NI.NatD , e₁ ∈ NI.zero' ≡ n₀ , 
            e₂ ∈ NI.zero' ≡ n₀ , b ∈ Lift lzero ⊤ , nil 

    Unify₀ : Unification Δ₀ 
    Unify₀ = Usolution {A = ⊤} (there (λ mzero → there (λ msuc → here (tt , NI.zero')))) 
                (UInjectivity {x = λ _ → NI.zero'} {y = λ _ → NI.zero'} (there (λ mzero → there (λ msuc → here tt))) 
                    (λ _ → refl) (λ _ → refl) 
                        (UEnd (mzero ∈ (P NI.zero' zero₁') , msuc ∈ ((n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
                            P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁)) , b ∈ Lift lzero ⊤ , nil)))

    Δ₁ : Telescope 9
    Δ₁ = mzero ∈ (P NI.zero' zero₁') , msuc ∈ ((n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁)) , 
            n₀ ∈ NI.μ NI.NatD , n₁ ∈ NI.μ NI.NatD , n₂ ∈ NI.μ NI.NatD , n ∈ μ Nat₁D (n₁ , (n₂ , tt)) , 
            e₁ ∈ NI.suc' n₁ ≡ n₀ , e₂ ∈ NI.suc' n₂ ≡ n₀ , 
            b ∈ (Nat₁-K-like-elimPx P (n₁ , n₂ , tt) n × Below (Nat₁-K-like-elimPx P) (n₁ , n₂ , tt) n) × Lift lzero ⊤ , nil

    Unify₁ : Unification Δ₁
    Unify₁ = UReorder f4 f0 (λ _ → _ , there (λ _ → there (λ _ → here tt))) 
                (UReorder f2 f0 (λ _ → _ , there λ _ → here tt) 
                    (Usolution {A = ⊤} (there (λ _ → there (λ _ → there (λ n₁ → here (tt , NI.suc' n₁))))) 
                        (UReorder f4 f0 (λ _ → _ , there (λ _ → here tt)) 
                            (UInjectivity (there (λ mzero → there (λ msuc → there (λ n₁ → there (λ n₂ → here (n₁ , n₂)))))) (λ _ → refl) (λ _ → refl) 
                                (Usolution₁ {A = ⊤} (there (λ mzero → there (λ msuc → there (λ n₁ → here (tt , n₁))))) 
                                        (UEnd (mzero ∈ (P NI.zero' zero₁') , msuc ∈ ((n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁)) , 
                                                n₀ ∈ NI.μ NI.NatD , n ∈ μ Nat₁D (n₀ , (n₀ , tt)) , b ∈ (Nat₁-K-like-elimPx P (n₀ , n₀ , tt) n × Below (Nat₁-K-like-elimPx P) (n₀ , n₀ , tt) n) × Lift lzero ⊤ , nil)))))))
 