module Indexed.HOUnification where
    
open import Indexed.datatypes 
open import Non_Indexed.telescope
open import Indexed.unification
open import Indexed.casetrees
open import Indexed.translation
open import Indexed.unify
open import lib

open import Level renaming (zero to lzero; suc to lsuc)
open import Agda.Builtin.Sigma
open import Data.Product
open import Data.Unit.Base
open import Data.Empty
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_)
open import Data.Nat.Properties
open import Data.Fin using (Fin; fromℕ<; toℕ) renaming (zero to fzero; suc to fsuc)
open import Function.Base using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)


injectivity⊤ : (e : tt ≡ tt) → ⊤
injectivity⊤ e = tt

injectivity⊤' : ⊤ → tt ≡ tt
injectivity⊤' e = refl

injectivity⊤'∘injectivity⊤ : (e : tt ≡ tt)
    → injectivity⊤' (injectivity⊤ e) ≡ e 
injectivity⊤'∘injectivity⊤ e = J (λ _ e → injectivity⊤' (injectivity⊤ e) ≡ e) refl e 


HOUnification : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → Σ[ e ∈ u ≡ v ] (subst (λ ab → proj₁ ab ≡ proj₂ ab) (Π-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e) 
    → unify f (merge u (r , tt)) ≡ unify f (merge v (s , tt))
HOUnification a b f' f u v r s (e , xs) = cong (λ ur → unify f (merge (proj₁ ur) (snd ur , tt))) 
    (Σ-create e goal')   where 

    goal₂ : subst (λ x → a (f' x) ≡ b (f' x)) (cong id e) r ≡ s 
    goal₂ = Π-create→cong e r s (flipSquare r s (cong (λ xs → a (f' xs)) e) (cong (λ xs → b (f' xs)) e) xs) 
    
    goal' : subst (λ v₁ → a (f' v₁) ≡ b (f' v₁)) e r ≡ s 
    goal' = cong→subst id (λ x → a (f' x) ≡ b (f' x)) e r s goal₂ 
    
HOUnification' : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → unify f (merge {X = Δ} {Y = (λ x → (p ∈ a x ≡ b x , nil))} {f = f'} u (r , tt)) ≡ unify f (merge v (s , tt))
    → Σ[ e ∈ u ≡ v ] (subst (λ ab → proj₁ ab ≡ proj₂ ab) (Π-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e) 
HOUnification' {Δ = Δ} a b f' f u v r s e = (linvΣ₁ ex) , eucong where  

    e' : merge u (r , tt) ≡ merge v (s , tt) 
    e' = subst (λ e → e ≡ merge v (s , tt)) (unify'∘unify f (merge u (r , tt))) 
            (subst (λ e → unify' f (unify f (merge u (r , tt))) ≡ e) (unify'∘unify f (merge v (s , tt))) 
                (cong (unify' f) e)) 

    ≡ur : (u : ⟦ Δ ⟧telD)(r : a (f' u) ≡ b (f' u)) 
        → (_,_ {B = λ u → a (f' u) ≡ b (f' u)} u r) ≡ (mproj₁ {X = Δ} {Y = (λ x → (p ∈ a x ≡ b x , nil))} {f = f'} (merge u (r , tt)) 
            , proj₁ (mproj₂ {X = Δ} {Y = λ x → (p ∈ a x ≡ b x , nil)} {f = f'} (merge u (r , tt))))
    ≡ur u r = cong (λ { (u , r , t) → (u , r) }) (mproj∘merge {X = Δ} {Y = (λ x → (p ∈ a x ≡ b x , nil))} {f = f'} u (r , tt))

    ex : (u , r) ≡ (v , s)
    ex = subst (λ e → e ≡ (v , s)) (sym (≡ur u r)) 
        (subst (λ e → (mproj₁ (merge u (r , tt)) , proj₁ (mproj₂ {X = Δ} {Y = λ x → cons (a x ≡ b x) λ p → nil} {f = f'} (merge u (r , tt)))) ≡ e) 
            (sym (≡ur v s)) 
                (cong (λ x → mproj₁ {X = Δ} {Y = λ x → (p ∈ a x ≡ b x , nil)} {f = f'} x , proj₁ (mproj₂ {X = Δ} {Y = λ x → (p ∈ a x ≡ b x , nil)} {f = f'} x)) e'  ))

    -- eucong₁' : subst (λ x → a (f' x) ≡ b (f' x)) (cong id (linvΣ₁ ex)) r ≡ s 
    -- eucong₁' = subst→cong id (λ x → a (f' x) ≡ b (f' x)) (linvΣ₁ ex) r s (linvΣ₂ ex)

    eucong' : subst (λ wy → proj₁ wy ≡ snd wy) (Π-create (cong (λ xs → a (f' xs)) (linvΣ₁ ex))
       (cong (λ xs → b (f' xs)) (linvΣ₁ ex))) r ≡ s
    eucong' = Π-cong→create (linvΣ₁ ex) r s (subst→cong id (λ x → a (f' x) ≡ b (f' x)) (linvΣ₁ ex) r s (linvΣ₂ ex))

    eucong : subst (λ ab → proj₁ ab ≡ snd ab) (Π-create r s)
      (cong (λ xs → a (f' xs)) (linvΣ₁ ex)) ≡ cong (λ xs → b (f' xs)) (linvΣ₁ ex)
    eucong = flipSquare (cong (λ xs → a (f' xs)) (linvΣ₁ ex)) (cong (λ xs → b (f' xs)) (linvΣ₁ ex)) r s eucong'

HOUnification'∘HOUnification : {i : ℕ} {Δ : Telescope i} {X Y : Set} (a b : X → Y) 
    → (f' :  ⟦ Δ ⟧telD → X)
    → (f : Unification (mergeTel Δ (λ x → (p ∈ a x ≡ b x , nil)) f')) 
    → (u v :  ⟦ Δ ⟧telD) (r : a (f' u) ≡ b (f' u)) (s : a (f' v) ≡ b (f' v))
    → (e : Σ[ e ∈ u ≡ v ] (subst (λ ab → proj₁ ab ≡ proj₂ ab) (Π-create r s) (cong (λ xs → a (f' xs)) e) ≡ cong (λ xs → b (f' xs)) e))
    → HOUnification' a b f' f u v r s (HOUnification a b f' f u v r s e) ≡ e
HOUnification'∘HOUnification {Δ = Δ} a b f' f u v r s (e , xs) = {!   !}  -- goal where 









ΔHOUnification : (X : Set) → Telescope 6 
ΔHOUnification X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e ∈ cons₁ X n x xs ≡ cons₁ X n y ys , nil

ΔHOUnification₁ : (X : Set) → Telescope 8 
ΔHOUnification₁ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₁ ∈ (suc₁ n , tt) ≡ (suc₁ n , tt) ,
            p ∈ e₁ ≡ refl ,
            e ∈ subst (μ (VecD X)) e₁ (cons₁ X n x xs) ≡ cons₁ X n y ys , nil

ΔHOUnification₂ : (X : Set) → Telescope 8 
ΔHOUnification₂ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₁ ∈ (suc₁ n , tt) ≡ (suc₁ n , tt) ,
            e ∈ subst (μ (VecD X)) e₁ (cons₁ X n x xs) ≡ cons₁ X n y ys ,
            p ∈ e₁ ≡ refl , nil

ΔHOUnification₃ : (X : Set) → Telescope 9
ΔHOUnification₃ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
    e₁ ∈ n ≡ n , 
    e₂ ∈ proj₁ (subst (λ n' →
            ⟦ Σ' X (λ x₂ → ×' (n' , tt) (one' (suc' n' , tt))) ⟧c (μ (VecD X))
                (suc₁ n , tt)) 
                    e₁ (x , xs , refl {x = (suc' n) , tt})) ≡ y , 
    e₃ ∈ proj₁ (subst (λ x → ⟦ ×' (proj₁ 
            (subst (λ x₁ →  ⟦ snd (VecD X x₁) ⟧c (μ (VecD X))
                (suc₁ n , tt)) (sym (refl {x = fsuc fzero})) (n , y , ys , refl {x = (suc' n) , tt})) , tt)
            (one' (suc' (proj₁ (subst (λ x₁ → 
                ⟦ snd (VecD X x₁) ⟧c (μ (VecD X)) (suc₁ n , tt))
                    (sym (refl {x = fsuc fzero})) (n , y , ys , refl {x = (suc' n) , tt}))) , tt)) ⟧c
            (μ (VecD X)) (suc₁ n , tt))
        e₂ (snd (subst (λ x → ⟦ Σ' X (λ x₁ → ×' (x , tt) (one' (suc' x , tt))) ⟧c (μ (VecD X))
            (suc₁ n , tt))
        e₁ (x , xs , refl {x = (suc' n) , tt}))))
            ≡ proj₁ (snd (snd (subst (λ x → ⟦ snd (VecD X x) ⟧c (μ (VecD X)) (suc₁ n , tt))
            (sym (refl {x = fsuc fzero})) (n , y , ys , refl {x = (suc' n) , tt})))) , 
    p ∈ linvΣ₁ (injectivity'K (cons₁ X n x xs ) (cons₁ X n y ys ) refl (e₁ , e₂ , e₃ , tt))
            ≡ refl , 
    nil


ΔHOUnification₄ : (X : Set) → Telescope 9
ΔHOUnification₄ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₁ ∈ n ≡ n , 
            p  ∈ cong (λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ ,
            e₂ ∈ x ≡ y , 
            e₃ ∈ subst (λ n → μ (VecD X) (n , tt)) e₁ xs ≡ ys , nil



ΔHOUnification₅ₗ : (X : Set)(n : μ NatD tt) → Telescope 2
ΔHOUnification₅ₗ X n = w ∈ μ NatD tt , p ∈ (_,_ {B = λ x₁ → ⊤} (suc₁ w) tt) ≡ (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt) , nil

HOUnify₅ₗ : (X : Set)(n : μ NatD tt) → Unification (ΔHOUnification₅ₗ X n)
HOUnify₅ₗ X n = USplitΣ (λ w → _,_ {B = λ x₁ → ⊤} (suc₁ w) tt) (λ w → _,_ {B = λ x₁ → ⊤} (suc₁ n) tt) (there λ w → here w) 
    (UInjectivity₁ {x₁ = λ where (n , w) → suc₁ w } {x₂ = λ where (n , w) → suc₁ n } 
        (there λ w → here (n , w)) (λ _ → refl) (λ _ → refl) 
        (Usolution₁ {X = ⊤} (here (tt , n)) 
            (UAddRule₁ (here tt) nil (λ _ → injectivity⊤) (λ _ → injectivity⊤') (λ _ → injectivity⊤'∘injectivity⊤) 
                (UEnd nil)))) 

ΔHOUnification₅ : (X : Set) → Telescope 9
ΔHOUnification₅ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₁ ∈ (n , tt) ≡ (n , tt) , 
            p  ∈ cong (λ ntt → (_,_ {B = λ x₁ → ⊤} (suc₁ (proj₁ ntt)) tt)) e₁ ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ ,
            e₂ ∈ x ≡ y , 
            e₃ ∈ subst (μ (VecD X)) e₁ xs ≡ ys , nil

ΔHOUnification₄' : (X : Set) → Telescope 9
ΔHOUnification₄' X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₁ ∈ (n , tt) ≡ (n , tt) , 
            p  ∈ cong (λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) (cong proj₁ e₁) ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) (cong proj₁ e₁) ,
            e₂ ∈ x ≡ y , 
            e₃ ∈ subst (λ n → μ (VecD X) (n , tt)) (cong proj₁ e₁) xs ≡ ys , nil


ΔHOUnification₆ : (X : Set) → Telescope 7
ΔHOUnification₆ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
            e₂ ∈ x ≡ y , e₃ ∈ xs ≡ ys , nil

ΔHOUnification₇ : (X : Set) → Telescope 3
ΔHOUnification₇ X = n ∈ μ NatD tt , x ∈ X , xs ∈ μ (VecD X) (n , tt) , nil

HOUnify₆ : (X : Set) → Unification (ΔHOUnification₆ X)
HOUnify₆ X = UReorder (fsuc (fsuc (fsuc fzero))) fzero (λ _ → _ , there λ xs → there λ ys → here tt) 
                (Usolution (there λ n → there λ x → here (tt , x)) 
                    (Usolution (there λ n → there λ x → there λ xs → here (n , xs)) 
                        (UEnd (ΔHOUnification₇ X))))


HOUnify₅ : (X : Set) → Unification (ΔHOUnification₅ X)
HOUnify₅ X = UAddRule₂ (there λ n → there λ x → there λ y → there λ xs → there λ ys → here n) 
    (e ∈ tt ≡ tt , nil) (λ x e → HOUnification (λ ntt → suc₁ (proj₁ ntt) , tt) (λ _ → suc₁ x , tt) id (HOUnify₅ₗ X x) (x , tt) (x , tt) refl refl e , tt) 
        (λ x xs → HOUnification' (λ ntt → suc₁ (proj₁ ntt) , tt) (λ _ → suc₁ x , tt) id (HOUnify₅ₗ X x) (x , tt) (x , tt) refl refl (proj₁ xs)) 
        (λ x e → HOUnification'∘HOUnification (λ ntt → suc₁ (proj₁ ntt) , tt) (λ _ → suc₁ x , tt) id (HOUnify₅ₗ X x) (x , tt) (x , tt) refl refl e) 
    (UAddRule₁ (there λ n → there λ x → there λ y → there λ xs → there λ ys → here tt) nil 
        (λ _ → injectivity⊤) (λ _ → injectivity⊤') (λ _ → injectivity⊤'∘injectivity⊤) 
            (HOUnify₆ X))  

HOUnify₄' : (X : Set) → Unification (ΔHOUnification₄' X)
HOUnify₄' X = {!   !}

HOUnify₄ : (X : Set) → Unification (ΔHOUnification₄ X)
HOUnify₄ X = UCombineΣ (λ n → n) (λ n → n) (there λ n → there λ x → there λ y → there λ xs → there λ ys → here n) 
    (HOUnify₄' X) 
    
HOUnify₃ : (X : Set) → Unification (ΔHOUnification₃ X)
HOUnify₃ X = UReplaceElem {Y₂ = λ where (n , x , xs , e₁ , y) → x ≡ y} (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
                → here (n , x , xs , e₁ , y))  (λ where 
                    (n , x , xs , refl , y) → refl) 
                (UReplaceElem {Y₂ = λ where (n , x , xs , y , ys , e₁ , e₂) → subst (λ n → μ (VecD X) (n , tt)) e₁ xs ≡ ys} 
                    (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
                    → there λ e₂ → here (n , x , xs , y , ys , e₁ , e₂)) (λ where 
                        (n , x , xs , y , ys , refl , refl) → refl)
                    (UReplaceElem {Y₂ = λ { (n , x , xs , y , ys , e₁ , e₂ , e₃) → cong (λ n → (suc₁ n , tt)) e₁ ≡ cong (λ _ → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ }} 
                        (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
                            → there λ e₂ → there λ e₃ → here (n , x , xs , y , ys , e₁ , e₂ , e₃)) 
                        (λ where (n , x , xs , y , ys , refl , refl , refl) → refl)
                    (UReorder (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) fzero (λ x → _ , there λ e₂ → there λ e₃ → here tt) 
                        (HOUnify₄ X))))

HOUnify₂ : (X : Set) → Unification (ΔHOUnification₂ X)
HOUnify₂ X = UInjectivity 
    {X = Σ[ n ∈ μ NatD tt ] (Σ[ x ∈ X ] (Σ[ xs ∈ μ (VecD X) (n , tt) ] (Σ[ y ∈ X ] (μ (VecD X) (n , tt)))))} 
    {d₁ = λ where (n , x , xs , y , ys) → (suc₁ n , tt)}
    {d₂ = λ where (n , x , xs , y , ys) → (suc₁ n , tt)}
    {x₁ = λ where (n , x , xs , y , ys) → cons₁ X n x xs}
    {x₂ = λ where (n , x , xs , y , ys) → cons₁ X n y ys}
    (there λ n → there λ x → there λ y → there λ xs → there λ ys 
        → here (n , x , xs , y , ys)) 
    (λ x → refl) (λ x → refl) 
    (HOUnify₃ X)

HOUnify₁ : (X : Set) → Unification (ΔHOUnification₁ X)
HOUnify₁ X = UReorder (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) fzero (λ x → _ , (there λ p → here tt)) 
                (HOUnify₂ X)


HOUnify : (X : Set) → Unification (ΔHOUnification X)
HOUnify X = U←Solution (μ (VecD X)) (λ where (n , x , y , xs , ys) → (suc₁ n , tt)) 
                {s = λ where (n , x , y , xs , ys) → cons₁ X n x xs}
                {t = λ where (n , x , y , xs , ys) → cons₁ X n y ys}
                (there λ n → there λ x → there λ y → there λ xs → there λ ys → here (n , x , y , xs , ys)) 
                (HOUnify₁ X) 













-- ΔHOUnification : (X : Set) → Telescope 6 
-- ΔHOUnification X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
--             e ∈ cons₁ X n x xs ≡ cons₁ X n y ys , nil

-- ΔHOUnification₁ : (X : Set) → Telescope 8 
-- ΔHOUnification₁ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
--             e₁ ∈ (suc₁ n , tt) ≡ (suc₁ n , tt) ,
--             p ∈ e₁ ≡ refl ,
--             e ∈ subst (μ (VecD X)) e₁ (cons₁ X n x xs) ≡ cons₁ X n y ys , nil

-- ΔHOUnification₂ : (X : Set) → Telescope 8 
-- ΔHOUnification₂ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
--             e₁ ∈ (suc₁ n , tt) ≡ (suc₁ n , tt) ,
--             e ∈ subst (μ (VecD X)) e₁ (cons₁ X n x xs) ≡ cons₁ X n y ys ,
--             p ∈ e₁ ≡ refl , nil

-- ΔHOUnification₃ : (X : Set) → Telescope 9
-- ΔHOUnification₃ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
--     e₁ ∈ n ≡ n , 
--     e₂ ∈ proj₁ (subst (λ n' →
--             ⟦ Σ' X (λ x₂ → ×' (n' , tt) (one' (suc' n' , tt))) ⟧c (μ (VecD X))
--                 (suc₁ n , tt)) 
--                     e₁ (x , xs , refl {x = (suc' n) , tt})) ≡ y , 
--     e₃ ∈ proj₁ (subst (λ x → ⟦ ×' (proj₁ 
--             (subst (λ x₁ →  ⟦ snd (VecD X x₁) ⟧c (μ (VecD X))
--                 (suc₁ n , tt)) (sym (refl {x = fsuc fzero})) (n , y , ys , refl {x = (suc' n) , tt})) , tt)
--             (one' (suc' (proj₁ (subst (λ x₁ → 
--                 ⟦ snd (VecD X x₁) ⟧c (μ (VecD X)) (suc₁ n , tt))
--                     (sym (refl {x = fsuc fzero})) (n , y , ys , refl {x = (suc' n) , tt}))) , tt)) ⟧c
--             (μ (VecD X)) (suc₁ n , tt))
--         e₂ (snd (subst (λ x → ⟦ Σ' X (λ x₁ → ×' (x , tt) (one' (suc' x , tt))) ⟧c (μ (VecD X))
--             (suc₁ n , tt))
--         e₁ (x , xs , refl {x = (suc' n) , tt}))))
--             ≡ proj₁ (snd (snd (subst (λ x → ⟦ snd (VecD X x) ⟧c (μ (VecD X)) (suc₁ n , tt))
--             (sym (refl {x = fsuc fzero})) (n , y , ys , refl {x = (suc' n) , tt})))) , 
--     p ∈ linvΣ₁ (injectivity'K (cons₁ X n x xs ) (cons₁ X n y ys ) refl (e₁ , e₂ , e₃ , tt))
--             ≡ refl , 
--     nil

-- ΔHOUnification₄ₗ : (X : Set) → Telescope 5
-- ΔHOUnification₄ₗ X = n ∈ μ NatD tt , w ∈ μ NatD tt , p ∈ suc₁ w ≡ suc₁ n , x ∈ X , xs ∈ μ (VecD X) (w , tt) , nil

-- ΔHOUnification₄ₗ' : (X : Set) → Telescope 3
-- ΔHOUnification₄ₗ' X = n ∈ μ NatD tt , x ∈ X , xs ∈ μ (VecD X) (n , tt) , nil

-- HOUnify₄ₗ : (X : Set) → Unification (ΔHOUnification₄ₗ X)
-- HOUnify₄ₗ X = UInjectivity₁ {x₁ = λ where (n , w) → suc₁ w } {x₂ = λ where (n , w) → suc₁ n } 
--         (there λ n → there λ w → here (n , w)) (λ _ → refl) (λ _ → refl) 
--         (Usolution₁ {X = ⊤} (there λ n → here (tt , n)) (UEnd (ΔHOUnification₄ₗ' X))) 

-- ΔHOUnification₄ : (X : Set) → Telescope 9
-- ΔHOUnification₄ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
--             e₁ ∈ n ≡ n , 
--             p ∈ cong (λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) e₁ ≡ cong (λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) refl ,
--             e₂ ∈ x ≡ y , 
--             e₃ ∈ subst (λ n → μ (VecD X) (n , tt)) e₁ xs ≡ ys , nil

-- ΔHOUnification₅ : (X : Set) → Telescope 7
-- ΔHOUnification₅ X = n ∈ μ NatD tt , x ∈ X , y ∈ X , xs ∈ μ (VecD X) (n , tt) , ys ∈ μ (VecD X) (n , tt) ,
--             e₂ ∈ x ≡ y , e₃ ∈ xs ≡ ys , nil

-- ΔHOUnification₆ : (X : Set) → Telescope 3
-- ΔHOUnification₆ X = n ∈ μ NatD tt , x ∈ X , xs ∈ μ (VecD X) (n , tt) , nil

-- HOUnify₅ : (X : Set) → Unification (ΔHOUnification₅ X)
-- HOUnify₅ X = UReorder (fsuc (fsuc (fsuc fzero))) fzero (λ _ → _ , there λ xs → there λ ys → here tt) 
--                 (Usolution (there λ n → there λ x → here (tt , x)) 
--                     (Usolution (there λ n → there λ x → there λ xs → here (n , xs)) 
--                         (UEnd (ΔHOUnification₆ X))))

-- HOUnify₄ : (X : Set) → Unification (ΔHOUnification₄ X)
-- HOUnify₄ X = {!   !}
    

-- HOUnify₃ : (X : Set) → Unification (ΔHOUnification₃ X)
-- HOUnify₃ X = UReplaceElem {Y₂ = λ where (n , x , xs , e₁ , y) → x ≡ y} (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
--                 → here (n , x , xs , e₁ , y))  (λ where 
--                     (n , x , xs , refl , y) → refl) 
--                 (UReplaceElem {Y₂ = λ where (n , x , xs , y , ys , e₁ , e₂) → subst (λ n → μ (VecD X) (n , tt)) e₁ xs ≡ ys} 
--                     (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
--                     → there λ e₂ → here (n , x , xs , y , ys , e₁ , e₂)) (λ where 
--                         (n , x , xs , y , ys , refl , refl) → refl)
--                     (UReplaceElem {Y₂ = λ { (n , x , xs , y , ys , e₁ , e₂ , e₃) → cong (λ n → (suc₁ n , tt)) e₁ ≡ cong (λ n → (_,_ {B = λ x₁ → ⊤} (suc₁ n) tt)) refl }} 
--                         (there λ n → there λ x → there λ y → there λ xs → there λ ys → there λ e₁ 
--                             → there λ e₂ → there λ e₃ → here (n , x , xs , y , ys , e₁ , e₂ , e₃)) 
--                         (λ where (n , x , xs , y , ys , refl , refl , refl) → refl)
--                     (UReorder (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) fzero (λ x → _ , there λ e₂ → there λ e₃ → here tt) 
--                         (HOUnify₄ X))))

-- HOUnify₂ : (X : Set) → Unification (ΔHOUnification₂ X)
-- HOUnify₂ X = UInjectivity 
--     {X = Σ[ n ∈ μ NatD tt ] (Σ[ x ∈ X ] (Σ[ xs ∈ μ (VecD X) (n , tt) ] (Σ[ y ∈ X ] (μ (VecD X) (n , tt)))))} 
--     {d₁ = λ where (n , x , xs , y , ys) → (suc₁ n , tt)}
--     {d₂ = λ where (n , x , xs , y , ys) → (suc₁ n , tt)}
--     {x₁ = λ where (n , x , xs , y , ys) → cons₁ X n x xs}
--     {x₂ = λ where (n , x , xs , y , ys) → cons₁ X n y ys}
--     (there λ n → there λ x → there λ y → there λ xs → there λ ys 
--         → here (n , x , xs , y , ys)) 
--     (λ x → refl) (λ x → refl) 
--     (HOUnify₃ X)

-- HOUnify₁ : (X : Set) → Unification (ΔHOUnification₁ X)
-- HOUnify₁ X = UReorder (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) fzero (λ x → _ , (there λ p → here tt)) 
--                 (HOUnify₂ X)


-- HOUnify : (X : Set) → Unification (ΔHOUnification X)
-- HOUnify X = U←Solution (μ (VecD X)) (λ where (n , x , y , xs , ys) → (suc₁ n , tt)) 
--                 {s = λ where (n , x , y , xs , ys) → cons₁ X n x xs}
--                 {t = λ where (n , x , y , xs , ys) → cons₁ X n y ys}
--                 (there λ n → there λ x → there λ y → there λ xs → there λ ys → here (n , x , y , xs , ys)) 
--                 (UEnd (ΔHOUnification₁ X)) 

    

-- module squareJ-example where 
    
--     private variable
--         A : Set 

--     ≡D : DataDesc 1 (a ∈ A , a ∈ A , nil)
--     ≡D {A} fzero = _ , Σ' A (λ a → one' (a , a , tt))

--     pattern idp a = ⟨ fzero , a , refl ⟩

--     SquareD : DataDesc 1 (a ∈ A , b ∈ A , c ∈ A , d ∈ A , p ∈ μ ≡D (a , b , tt) , 
--         q ∈ μ ≡D (c , d , tt) , r ∈ μ ≡D (a , c , tt) , s ∈ μ ≡D (b , d , tt) , nil)
--     SquareD {A} fzero = _ , Σ' A (λ a → one' (a , a , a , a , idp a , idp a , idp a , idp a , tt))

--     pattern ids a = ⟨ fzero , a , refl ⟩ 

    
--     J2 : {A : Set} {a : A} {p : μ ≡D (a , a , tt)} → μ SquareD (a , a , a , a , idp a , p , idp a , idp a , tt) → A
--     J2 (ids a) = a 
     
--     J2Δ : (A : Set) → Telescope _ 
--     J2Δ A = a ∈ A , p ∈ μ ≡D (a , a , tt) , s ∈ μ SquareD (a , a , a , a , idp a , p , idp a , idp a , tt) , nil

--     J2T : (A : Set) → ⟦ J2Δ A ⟧telD → Set 
--     J2T A _ = A

--     CTJ2 : {A : Set} → CaseTree (J2Δ A) (J2T A)
--     CTJ2 {A} = node (there (λ a → there (λ p → here (a , a , a , a , idp a , p , idp a , idp a , tt)))) (λ where  
--         fzero → {!   !}) where 

--         ΔIds : Telescope 11
--         ΔIds = a ∈ A , p ∈ μ ≡D (a , a , tt) , a' ∈ A , e ∈ a' ≡ a , _

--         UnifyIds : Unification ΔIds
--         UnifyIds =  UReorder fzero fzero (λ _ → A , there (λ a → there (λ p → here tt)))
--                         (UReorder (fsuc (fsuc fzero)) fzero (λ _ → _ , there (λ p → here tt))
--                             (Usolution {X = ⊤} {A = λ a → A} (there (λ a → here a)) ?))


--     J1 : {a : A} {p : μ ≡D (a , a , tt)} → μ SquareD (a , a , a , a , p , idp a , idp a , idp a , tt) → A
--     J1 (ids a) = a 

--     ΔFlip : {A : Set} → Telescope _ 
--     ΔFlip {A} = a ∈ A , p ∈ μ ≡D (a , a , tt), s ∈ μ SquareD (a , a , a , a , p , idp a , idp a , idp a , tt) , nil
    
--     TFlip : ⟦ ΔFlip {A = A} ⟧telD → Set 
--     TFlip {A = A} _ = A

--     CTJ1 : {A : Set} → CaseTree (ΔFlip {A = A}) TFlip
--     CTJ1 {A} = node (there (λ a → there (λ p → here (a , a , a , a , p , idp a , idp a , idp a , tt)))) (λ where  
--         fzero → unifyFlip , {! leaf  !}) where 

--         -- Δsplit₇ : Telescope 2
--         -- Δsplit₇ = a' ∈ A , e ∈ idp a' ≡ idp a' , _

--         -- unifyFlip₇ : Unification Δsplit₇
--         -- unifyFlip₇ = UInjectivity (there (λ a → here (tt , (a , a , tt)))) (λ d' d → refl) (λ d' d → refl) 
--         --     (UDeletion (there (λ a' → here a')) (UEnd (a' ∈ A , nil)))
            
--         -- Δsplit₆ : Telescope 3
--         -- Δsplit₆ = a' ∈ A , e ∈ idp a' ≡ idp a' , _

--         -- unifyFlip₆ : Unification Δsplit₆
--         -- unifyFlip₆ = UInjectivity (there (λ a → here (tt , (a , a , tt)))) (λ d' d → refl) (λ d' d → refl) 
--         --     (UDeletion (there (λ a' → here a')) unifyFlip₇)

        
--         Δsplit₆ : Telescope 6
--         Δsplit₆ = a' ∈ A , ea ∈ a' ≡ a' , p ∈ ea ≡ refl , e ∈ (subst (λ a' → μ ≡D (a' , a' , tt)) ea (idp a')) ≡ idp a' , _
        
--         unifyFlip₆ : Unification Δsplit₆
--         unifyFlip₆ = {!   !}

--         Δsplit₅ : Telescope 4
--         Δsplit₅ = a' ∈ A , e ∈ idp a' ≡ idp a' , _

--         unifyFlip₅ : Unification Δsplit₅
--         unifyFlip₅ = {!   !}

--         Δsplit₄ : Telescope 6
--         Δsplit₄ = a' ∈ A , p ∈ μ ≡D (a' , a' , tt), e ∈ idp a' ≡ p , _

--         unifyFlip₄ : Unification Δsplit₄
--         unifyFlip₄ = Usolution {A = λ a → μ ≡D (a , a , tt)} (there (λ a' → here (idp a'))) unifyFlip₅

--         Δsplit₃ : Telescope 7
--         Δsplit₃ = a' ∈ A , p ∈ μ ≡D (a' , a' , tt), e ∈ a' ≡ a' , _

--         unifyFlip₃ : Unification Δsplit₃
--         unifyFlip₃ = UDeletion (there (λ a' → (there (λ p → here a')))) unifyFlip₄

--         Δsplit₂ : Telescope 8
--         Δsplit₂ = a' ∈ A , p ∈ μ ≡D (a' , a' , tt), e ∈ a' ≡ a' , _

--         unifyFlip₂ : Unification Δsplit₂
--         unifyFlip₂ = UDeletion (there (λ a' → (there (λ p → here a')))) unifyFlip₃

--         Δsplit₁ : Telescope 9
--         Δsplit₁ = a' ∈ A , p ∈ μ ≡D (a' , a' , tt), e ∈ a' ≡ a' , _

--         unifyFlip₁ : Unification Δsplit₁
--         unifyFlip₁ = UDeletion (there (λ a' → (there (λ p → here a')))) unifyFlip₂

--         Δsplit : Telescope 11
--         Δsplit = a ∈ A , p ∈ μ ≡D (a , a , tt), a' ∈ A , e ∈ a' ≡ a , _

--         unifyFlip : Unification Δsplit
--         unifyFlip = UReorder fzero fzero (λ _ → A , there (λ a → there (λ p → here tt)))
--                         (UReorder (fsuc (fsuc fzero)) fzero (λ _ → _ , there (λ p → here tt))
--                             (Usolution {X = ⊤} {A = λ a → A} (there (λ a → here a)) unifyFlip₁))


    --     test : Unification ()
    
    -- -- node (here tt) λ where
    --     -- (fzero)      → leaf (λ _ → false')
    --     -- (fsuc fzero) → leaf (λ _ → true')     
    
    -- J2 : {A : Set} {a : A} {p : μ ≡D (a , a , tt)} → μ SquareD (a , a , a , idp , p , idp , idp , tt) → Set
    -- J2 ids = ⊤ 

    -- J3 : {A : Set} {a : A} {p : μ ≡D (a , a , tt)} → μ SquareD (a , a , a , idp , idp , p , idp , tt) → Set
    -- J3 ids = ⊤ 

    -- J4 : {A : Set} {a : A} {p : μ ≡D (a , a , tt)} → μ SquareD (a , a , a , idp , idp , idp , p , tt) → Set
    -- J4 ids = ⊤   