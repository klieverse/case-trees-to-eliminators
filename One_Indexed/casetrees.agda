-- {-# OPTIONS --allow-unsolved-metas #-}
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
  ℓ   : Level
  n m : ℕ
  IΔ  : DVec n

-- telescope of equivalent indices
vecTel : {IΔ : DVec n} (d₁ d₂ : ⟦ IΔ ⟧Vec) → Telescope n 
vecTel {IΔ = []    } tt tt = nil 
vecTel {IΔ = d ∷ ds} (d₁ , ds₁) (d₂ , ds₂) = e ∈ (d₁ ≡ d₂) , vecTel ds₁ ds₂

-- telescope of constructor arguments for constructor description C on X
conTel : {IΔ : DVec n}(X : ⟦ IΔ ⟧Vec → Set)(C : ConDesc IΔ m)(d : ⟦ IΔ ⟧Vec) → Telescope (m + n)
conTel X (one' d') d = vecTel d' d
conTel X (Σ' S C)  d = s ∈ S , conTel X (C s) d
conTel X (×' d' C) d = μD ∈ X d' , conTel X C d

-- telescope of constructor arguments for constructor description C on X
telToVec : {IΔ : DVec n}{d₁ d₂ : ⟦ IΔ ⟧Vec}
    → (t : ⟦ vecTel d₁ d₂ ⟧telD) → d₁ ≡ d₂
telToVec {IΔ = []    } tt = refl
telToVec {IΔ = d ∷ ds} (t , ts) = Π-create t (telToVec ts) 

telToCon : {X : ⟦ IΔ ⟧Vec → Set}{C : ConDesc IΔ m}{d : ⟦ IΔ ⟧Vec}
    → (t : ⟦ conTel X C d ⟧telD) → ⟦ C ⟧c X d
telToCon {C = one' d'} {d} v = telToVec v
telToCon {C = Σ' S C} (s , t) = s , telToCon t
telToCon {C = ×' d' C} (μD , t) = μD , telToCon t

-- instantiation of conTel from interpretation of constructor interpretation on X
vecToTel : {IΔ : DVec n}{d₁ d₂ : ⟦ IΔ ⟧Vec}
    → d₁ ≡ d₂ → ⟦ vecTel d₁ d₂ ⟧telD
vecToTel {IΔ = []    } e = tt
vecToTel {IΔ = d ∷ ds} e = projΠ₁ e , (vecToTel (projΠ₂ e))

conToTel : {X : ⟦ IΔ ⟧Vec → Set}{C : ConDesc IΔ m}{d : ⟦ IΔ ⟧Vec}
    → ⟦ C ⟧c X d → ⟦ conTel X C d ⟧telD
conToTel {C = one' v} e = vecToTel e
conToTel {C = Σ' S C} (s , t) = s , conToTel t 
conToTel {C = ×' _ C} (μD , t) = μD , conToTel t

-- proof of section-retraction pair
telToVec∘vecToTel : {IΔ : DVec n}{d₁ d₂ : ⟦ IΔ ⟧Vec} (e : d₁ ≡ d₂) → telToVec (vecToTel e) ≡ e
telToVec∘vecToTel {IΔ = []    } {d₁ = tt} {d₂ = tt} e = J' (λ _ e' → e' ≡ e) e refl
telToVec∘vecToTel {IΔ = d ∷ ds} {d₁ = (d₁ , ds₁)} {d₂ = (d₂ , ds₂)} e 
  = subst (λ f → Π-create (projΠ₁ e) f ≡ e) (sym (telToVec∘vecToTel (projΠ₂ e))) (create∘projΠ e)

telToCon∘conToTel : {X : ⟦ IΔ ⟧Vec → Set}{C : ConDesc IΔ n}{d : ⟦ IΔ ⟧Vec}
    → (t : ⟦ C ⟧c X d) → telToCon (conToTel t) ≡ t 
telToCon∘conToTel {C = one' v} e = telToVec∘vecToTel e
telToCon∘conToTel {C = Σ' S C} (s , t) = cong (s ,_) (telToCon∘conToTel t)
telToCon∘conToTel {C = ×' _ C} (μD , t) = cong (μD ,_) (telToCon∘conToTel t)


-- representation of a case tree
data CaseTree (Δ : Telescope n)(T : ⟦ Δ ⟧telD → Set ℓ) : Set (lsuc ℓ) where
    leaf : (t : (args : ⟦ Δ ⟧telD) → T args) → CaseTree Δ T
    node : {k d : ℕ}{IΔ : DVec d}{D : DataDesc m IΔ}
        → (p : Δ [ k ]∶Σ[ ⟦ IΔ ⟧Vec ] (μ D))
        → (bs : (con : Fin m) 
            -- add unification algorithm for indices
            → Σ[ u ∈ Unification (expandTel Δ (conTel (μ D) (proj₂ (D con))) 
                    (λ d args → ⟨ con , telToCon args ⟩) p)] 
                (CaseTree (proj₂ (unifyTel u)) 
                    (λ args → expandSort p T (unify' u args))))
        → CaseTree Δ T


-- example case tree head function
headΔ : (X : Set) → Telescope 2 
headΔ X = n ∈ NI.μ NI.NatD , _ ∈ μ (VecD X) (NI.suc' n , tt) , nil

headT : (X : Set) → ⟦ headΔ X ⟧telD → Set
headT X _ = X

CTHeadRoot : (X : Set) → CaseTree (headΔ X) (headT X)
CTHeadRoot X = node (there (λ n → here (NI.suc' n , tt))) (λ where
            (fzero)      → UnifyZero , leaf (λ where 
                (n , b , tt) → ⊥-elim b)
            (fsuc fzero) → UnifySuc X , leaf (λ where 
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
                (fzero) → Unify₀ , node (there (λ m → here (m , NI.zero' , tt))) (λ where 
                    (fzero) → Unify₀₀ , leaf (λ _ → refl) 
                    (fsuc fzero) → Unify₀₁ , leaf (λ where 
                        (m , n , b , _) → ⊥-elim b))
                (fsuc fzero) → Unify₁ , node (there (λ n' → there (λ m' → there (λ x → here (NI.suc' m' , NI.suc' n' , tt))))) (λ where 
                    (fzero) → Unify₁₀ , leaf (λ where 
                        (m , n , x , b , _) → ⊥-elim b)
                    (fsuc fzero) → Unify₁₁ , leaf (λ where 
                        (n , m , x , y , ((H , _) , _) , _) → cong NI.suc' (H (n , m , x , y , tt) refl) ))) where


    antisymΔ₀ : Telescope 7
    antisymΔ₀ = n ∈ NI.μ NI.NatD , m ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , 
                en ∈ NI.zero' ≡ n , em ∈ m' ≡ m , 
                y ∈ μ ≤D (m , n , tt) , b ∈ Lift lzero ⊤ , nil
    
    Unify₀ : Unification antisymΔ₀ 
    Unify₀ = UReorder (fsuc fzero) fzero (λ x → _ , there (λ _ → there (λ _ → here tt))) 
                (Usolution {X = ⊤} (here (tt , NI.zero')) 
                    (Usolution₁ {X = ⊤} (there (λ m → here (tt , m))) 
                            (UEnd (m ∈ NI.μ NI.NatD , y ∈ μ ≤D (m , NI.zero' , tt) , b ∈ Lift lzero ⊤ , nil)))) 

    antisymΔ₀₀ : Telescope 5
    antisymΔ₀₀ = m ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , 
                en ∈ NI.zero' ≡ m , em ∈ m' ≡ NI.zero' , 
                b ∈ Lift lzero ⊤ , nil
    
    Unify₀₀ : Unification antisymΔ₀₀
    Unify₀₀ = UReorder (fsuc fzero) fzero (λ x → _ , there (λ _ → here tt)) 
                (Usolution {X = ⊤} (here (tt , NI.zero')) 
                    (Usolution₁ {X = ⊤} (here (tt , NI.zero')) 
                            (UEnd (b ∈ Lift lzero ⊤ , nil))))

    antisymΔ₀₁ : Telescope 7
    antisymΔ₀₁ = m ∈ NI.μ NI.NatD , m' ∈ NI.μ NI.NatD , n' ∈ NI.μ NI.NatD , y ∈ μ ≤D (m' , n' , tt) ,
                en ∈ NI.suc' m' ≡ m , em ∈ NI.suc' n' ≡ NI.zero' ,
                b ∈ Lift lzero ⊤ , nil 
    
    Unify₀₁ : Unification antisymΔ₀₁
    Unify₀₁ = UReorder fzero fzero (λ _ → _ , there (λ _ → here tt)) 
                (UReorder (fsuc (fsuc fzero)) fzero (λ x → _ , there (λ _ → there (λ _ → here tt))) 
                    (Usolution {X = ⊤} (there (λ m' → here (tt , NI.suc' m'))) 
                        (UReorder (fsuc (fsuc fzero)) fzero (λ x → _ , there (λ _ → here tt)) 
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
    Unify₁ = UReorder fzero fzero (λ _ → _ , there (λ _ → there (λ _ → here tt))) 
                (UReorder (fsuc (fsuc fzero)) fzero (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → here tt)))) 
                    (Usolution {X = ⊤} (there (λ n' → here (tt , NI.suc' n'))) 
                        (UReorder (fsuc fzero) fzero ((λ _ → _ , there (λ _ → here tt))) 
                            (UReorder (fsuc (fsuc (fsuc fzero))) fzero (λ _ → _ , there (λ _ → here tt)) 
                                (Usolution {X = ⊤} (there (λ n' → there (λ m' → here (tt , NI.suc' m')))) 
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
                    (UReorder (fsuc fzero) fzero (λ _ → _ , there (λ _ → there (λ _ → here tt))) 
                        (UReorder (fsuc (fsuc fzero)) fzero (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → here tt)))) 
                            (Usolution₁ {X = ⊤} (there (λ n' → here (tt , NI.suc' n'))) 
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
    Unify₁₁ = UReorder (fsuc fzero) fzero (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → here tt)))) 
                (UReorder (fsuc (fsuc (fsuc fzero))) fzero (λ _ → _ , there (λ _ → here tt)) 
                    (UReorder (fsuc (fsuc fzero)) fzero (λ _ → _ , there (λ _ → there (λ _ → there (λ _ → there (λ _ → there (λ _ → here tt)))))) 
                        (UReorder (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) fzero (λ _ → _ , there (λ _ → there (λ _ → here tt))) 
                            (UInjectivity (there (λ n' → there (λ n'' → here (n' , n'')))) (λ _ → refl) (λ _ → refl) 
                                (UInjectivity (there (λ n' → there (λ n'' → there (λ e → there (λ m' → there (λ m'' → here (m' , m''))))))) (λ _ → refl) (λ _ → refl) 
                                    (Usolution₁ {X = ⊤} (there (λ n' → here (tt , n'))) 
                                        (Usolution₁ {X = ⊤} (there (λ n' → there (λ m' → here (tt , m')))) 
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
            (fzero) → Unify₀ , leaf (λ where 
                (mzero , msuc , _) → mzero) 
            (fsuc fzero) → Unify₁ , leaf (λ where 
                (mzero , msuc , n₀ , n , ((H , _) , _) , _ ) → msuc n₀ n (H (mzero , msuc , n₀ , n , tt) refl))) where 

    Δ₀ : Telescope 6 
    Δ₀ = mzero ∈ (P NI.zero' zero₁') , msuc ∈ ((n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
            P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁)) , n₀ ∈ NI.μ NI.NatD , e₁ ∈ NI.zero' ≡ n₀ , 
            e₂ ∈ NI.zero' ≡ n₀ , b ∈ Lift lzero ⊤ , nil 

    Unify₀ : Unification Δ₀ 
    Unify₀ = Usolution {X = ⊤} (there (λ mzero → there (λ msuc → here (tt , NI.zero')))) 
                (UInjectivity {s = λ _ → NI.zero'} {t = λ _ → NI.zero'} (there (λ mzero → there (λ msuc → here tt))) 
                    (λ _ → refl) (λ _ → refl) 
                        (UEnd (mzero ∈ (P NI.zero' zero₁') , msuc ∈ ((n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → 
                            P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁)) , b ∈ Lift lzero ⊤ , nil)))

    Δ₁ : Telescope 9
    Δ₁ = mzero ∈ (P NI.zero' zero₁') , msuc ∈ ((n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁)) , 
            n₀ ∈ NI.μ NI.NatD , n₁ ∈ NI.μ NI.NatD , n₂ ∈ NI.μ NI.NatD , n ∈ μ Nat₁D (n₁ , (n₂ , tt)) , 
            e₁ ∈ NI.suc' n₁ ≡ n₀ , e₂ ∈ NI.suc' n₂ ≡ n₀ , 
            b ∈ (Nat₁-K-like-elimPx P (n₁ , n₂ , tt) n × Below (Nat₁-K-like-elimPx P) (n₁ , n₂ , tt) n) × Lift lzero ⊤ , nil

    Unify₁ : Unification Δ₁
    Unify₁ = UReorder (fsuc (fsuc (fsuc (fsuc fzero)))) fzero (λ _ → _ , there (λ _ → there (λ _ → here tt))) 
                (UReorder (fsuc (fsuc fzero)) fzero (λ _ → _ , there λ _ → here tt) 
                    (Usolution {X = ⊤} (there (λ _ → there (λ _ → there (λ n₁ → here (tt , NI.suc' n₁))))) 
                        (UReorder (fsuc (fsuc (fsuc (fsuc fzero)))) fzero (λ _ → _ , there (λ _ → here tt)) 
                            (UInjectivity (there (λ mzero → there (λ msuc → there (λ n₁ → there (λ n₂ → here (n₁ , n₂)))))) (λ _ → refl) (λ _ → refl) 
                                (Usolution₁ {X = ⊤} (there (λ mzero → there (λ msuc → there (λ n₁ → here (tt , n₁))))) 
                                        (UEnd (mzero ∈ (P NI.zero' zero₁') , msuc ∈ ((n₀ : NI.μ NI.NatD) (n₁ : μ Nat₁D (n₀ , (n₀ , tt))) → P n₀ n₁ → P (NI.suc' n₀) (suc₁' n₀ n₀ n₁)) , 
                                                n₀ ∈ NI.μ NI.NatD , n ∈ μ Nat₁D (n₀ , (n₀ , tt)) , b ∈ (Nat₁-K-like-elimPx P (n₀ , n₀ , tt) n × Below (Nat₁-K-like-elimPx P) (n₀ , n₀ , tt) n) × Lift lzero ⊤ , nil)))))))
