module Non_Indexed.examples where 

open import Non_Indexed.datatypes 
open import Non_Indexed.telescope
open import Non_Indexed.casetrees
open import Non_Indexed.translation

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Unit.Base
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ<; toℕ) renaming (zero to fzero; suc to fsuc)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

module bool-example where 

    -- datatype
    BoolD : DataDesc 2
    BoolD fzero        = _ , one'
    BoolD (fsuc fzero) = _ , one'

    pattern true'  = ⟨ fzero , tt ⟩
    pattern false' = ⟨ fsuc fzero , tt ⟩

    not : μ BoolD → μ BoolD
    not true'  = false' 
    not false' = true' 

    -- case tree
    CTNotRoot : CaseTree (_ ∈ μ BoolD , nil) (λ _ → μ BoolD) 
    CTNotRoot = node (here tt) λ where
        (fzero)      → leaf (λ _ → false')
        (fsuc fzero) → leaf (λ _ → true')     

    -- translation
    ≡-not : {x : μ BoolD} (b : μ BoolD) → not b ≡ x 
        → eval CTNotRoot ( b , tt ) ≡ x
    ≡-not true' refl = refl 
    ≡-not false' refl = refl 
    
    
module natExample where 
    
    NatD : DataDesc 2 
    NatD fzero        = _ , one'
    NatD (fsuc fzero) = _ , ind×' one'

    pattern zero' = ⟨ fzero , tt ⟩ 
    pattern suc' n = ⟨ fsuc fzero , (n , tt) ⟩

    _+'_ : μ NatD → μ NatD → μ NatD 
    zero'  +' m = m 
    suc' n +' m = suc' (n +' m)

    +P : μ NatD → Set 
    +P n = (t : ⟦ n ∈ μ NatD , m ∈ μ NatD , nil ⟧telD) → n ≡ proj₁ t → μ NatD

    +Δ : Telescope 3
    +Δ = n ∈ μ NatD , m ∈ μ NatD , b ∈ Below +P n , nil

    +T : ⟦ +Δ ⟧telD → Set
    +T _ = μ NatD

    CT+ : CaseTree +Δ +T 
    CT+ = node (here tt) (λ where 
        (fzero) → leaf (λ where 
            (m , b , tt) → m) 
        (fsuc fzero) → leaf (λ where 
            (n , m , ((H , b) , _) , tt) → suc' (H (n , (m , tt)) refl)))

    +-tel : (n m : μ NatD) → ⟦ +Δ ⟧telD
    +-tel n m = n , m , (below +P +p n , tt) where 

        +p : (n : μ NatD) → Below +P n → +P n 
        +p n' b (n , m , tt) e = eval CT+ (n , m , subst (Below +P) e b , tt)

    ≡-+ : {x : μ NatD} (n m : μ NatD) → (n +' m) ≡ x → eval CT+ (+-tel n m) ≡ x
    ≡-+ zero' m refl = refl  
    ≡-+ (suc' n) m refl = cong suc' (≡-+ n m refl)


    data Vec (X : Set) : (n : μ NatD) → Set where 
        nilV : Vec X zero' 
        consV : (n : μ NatD) → (x : X) → Vec X n → Vec X (suc' n)
   
    
    half : μ NatD → μ NatD
    half zero' = zero' 
    half (suc' zero') = zero' 
    half (suc' (suc' n)) = suc' (half n) 


    halfP : μ NatD → Set 
    halfP n = (t : ⟦ _ ∈ μ NatD , nil ⟧telD) → n ≡ proj₁ t → μ NatD

    halfΔ : Telescope 2
    halfΔ = n ∈ μ NatD , (_ ∈ Below halfP n , nil)

    halfT : {i : ℕ} → {Δ : Telescope i} → ⟦ Δ ⟧telD → Set
    halfT _ = μ NatD

    -- case tree
    CTHalfRoot : CaseTree halfΔ halfT
    CTHalfRoot = node (here tt) (λ where 
            (fzero) → leaf (λ _ → zero')
            (fsuc fzero) → node (here tt) (λ where 
                (fzero) → leaf (λ _ → zero')
                (fsuc fzero) → leaf (λ where 
                    (n , (((_ , ((H , _) , _)) , _) , _)) → suc' (H (n , tt) refl)))) 
    
    -- translation
    half-tel : (n : μ NatD) → ⟦ halfΔ ⟧telD
    half-tel n = n , (below halfP halfp n , tt) where 

        halfp : (n : μ NatD) → Below halfP n → halfP n 
        halfp .n b (n , tt) refl = eval CTHalfRoot (n , (b , tt)) 

    ≡-half : {x : μ NatD} (n : μ NatD) → half n ≡ x → eval CTHalfRoot (half-tel n) ≡ x
    ≡-half zero' refl = refl  
    ≡-half (suc' zero') refl = refl 
    ≡-half (suc' (suc' n)) refl = cong (λ n → (suc' n)) (≡-half n refl) 

    create : {X : Set} (n : μ NatD) → (x : X) → Vec X n 
    create zero' x = nilV
    create (suc' n) x = consV n x (create n x)

    createΔ : {X : Set} → Telescope 3
    createΔ {X} = n ∈ μ NatD , a ∈ X , b ∈ Below (λ n → Vec X n) n , nil

    createT : {X : Set} → ⟦ createΔ {X} ⟧telD → Set
    createT {X} (n , _) = Vec X n

    -- case tree
    CTCreateRoot : {X : Set} → CaseTree (createΔ {X}) (createT {X})
    CTCreateRoot {X} = node (here tt) (λ where
            (fzero) → leaf (λ _ → nilV) 
            (fsuc fzero) → leaf (λ where 
                (n , (a , (((n' , _) , _) , _))) → consV n a n'))

    -- translation
    create-tel : {X : Set} → (n : μ NatD) → (x : X) → ⟦ createΔ {X} ⟧telD
    create-tel {X} n x = (n , (x , (below ((λ n → Vec X n)) createp n , tt))) where 

            createp : (d : μ NatD) → Below ((λ n → Vec X n)) d → Vec X d
            createp d b = eval CTCreateRoot (d , x , (b , tt))

    ≡-create : {X : Set} → (n : μ NatD) (x : X) → {v : Vec X n} → create n x ≡ v 
        → eval CTCreateRoot (create-tel n x) ≡ v
    ≡-create {X} zero' x refl = refl  
    ≡-create {X} (suc' n) x refl = cong (λ v → (consV n x v)) (≡-create n x refl) 