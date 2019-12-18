module Product where

open import Relation.Binary.PropositionalEquality.Core
open import Level
open import Relation.Binary.Core
open import Data.Product using (_×_; _,_; map; zip; proj₁; proj₂; swap)
open import Function using (flip)

open import Category
open import Equivalence

infixr 5 _×c_
_×c_ : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} -> Category c₁ c₂ ℓ -> Category c₁′ c₂′ ℓ′ -> Category (c₁ ⊔ c₁′) (c₂ ⊔ c₂′) (ℓ ⊔ ℓ′)
_×c_ {c₁} {c₂} {ℓ} {c₁′} {c₂′} {ℓ′} C D = record { Obj = obj ; Hom = hom ; _≈_ = _≈_ ; _∘_ = _∘_ ; Id = id ; isCategory = isCategory }
    where
        obj : Set (c₁ ⊔ c₁′)
        obj = Obj C × Obj D
        hom : obj -> obj -> Set (c₂ ⊔ c₂′)
        hom (a₁ , a₂) (b₁ , b₂) = Hom C a₁ b₁ × Hom D a₂ b₂
        _≈_ : {a b : obj} -> Rel (hom a b) (ℓ ⊔ ℓ′)
        (f₁ , f₂) ≈ (g₁ , g₂) = (C [ f₁ ≈ g₁ ]) × (D [ f₂ ≈ g₂ ])
        _∘_ : {a b c : obj} -> hom b c -> hom a b -> hom a c
        _∘_ = zip (Category._∘_ C) (Category._∘_ D)
        id : {a : obj} -> hom a a
        id {a , b} = Id C a , Id D b
        isCategory : IsCategory obj hom _≈_ _∘_ id
        isCategory = record {
            isEquivalence = record {
                refl = IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory C)) , IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory D)) ;
                sym = map (IsEquivalence.sym (IsCategory.isEquivalence (Category.isCategory C))) (IsEquivalence.sym (IsCategory.isEquivalence (Category.isCategory D))) ;
                trans = zip (IsEquivalence.trans (IsCategory.isEquivalence (Category.isCategory C))) (IsEquivalence.trans (IsCategory.isEquivalence (Category.isCategory D))) } ;
            identityL = IsCategory.identityL (Category.isCategory C) , IsCategory.identityL (Category.isCategory D) ;
            identityR = IsCategory.identityR (Category.isCategory C) , IsCategory.identityR (Category.isCategory D) ;
            ∘-resp-≈ = zip (IsCategory.∘-resp-≈ (Category.isCategory C)) (IsCategory.∘-resp-≈ (Category.isCategory D)) ;
            associative = IsCategory.associative (Category.isCategory C) , IsCategory.associative (Category.isCategory D) }

×c-comm-F : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} -> Functor (C ×c D) (D ×c C)
×c-comm-F {C = C} {D} = record {
    FObj = swap ;
    FMap = swap ;
    isFunctor = record {
        ≈-cong = swap ;
        identity = ≈-Reasoning.refl-hom (D ×c C) ;
        distr = ≈-Reasoning.refl-hom (D ×c C) } }

×c-comm : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} -> C ×c D ≅ D ×c C
×c-comm {C = C} {D} = record {F = ×c-comm-F ; G = ×c-comm-F ; inverse = record {FG=id = record {fmapEq = ≋-Reasoning.refl-hom (D ×c C)} ; GF=id = record {fmapEq = ≋-Reasoning.refl-hom (C ×c D)}}}

×c-assoc : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ c₁″ c₂″ ℓ″ : Level} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {E : Category c₁″ c₂″ ℓ″} -> (C ×c D) ×c E ≅ C ×c (D ×c E)
×c-assoc {C = C} {D} {E} = record {
    F = record {
        FObj = \a -> proj₁ (proj₁ a) , (proj₂ (proj₁ a) , proj₂ a) ;
        FMap = \f -> proj₁ (proj₁ f) , (proj₂ (proj₁ f) , proj₂ f) ;
        isFunctor = record {
            ≈-cong = \x -> proj₁ (proj₁ x) , (proj₂ (proj₁ x) , proj₂ x) ;
            identity = ≈-Reasoning.refl-hom (C ×c (D ×c E)) ;
            distr = ≈-Reasoning.refl-hom (C ×c (D ×c E)) } } ;
    G = record {
        FObj = \a -> (proj₁ a , proj₁ (proj₂ a)) , proj₂ (proj₂ a) ;
        FMap = \f -> (proj₁ f , proj₁ (proj₂ f)) , proj₂ (proj₂ f) ;
        isFunctor = record {
            ≈-cong = \x -> (proj₁ x , proj₁ (proj₂ x)) , proj₂ (proj₂ x) ;
            identity = ≈-Reasoning.refl-hom ((C ×c D) ×c E) ;
            distr = ≈-Reasoning.refl-hom ((C ×c D) ×c E) } } ;
    inverse = record {
        FG=id = record {fmapEq = ≋-Reasoning.refl-hom (C ×c (D ×c E))} ;
        GF=id = record {fmapEq = ≋-Reasoning.refl-hom ((C ×c D) ×c E)} } }

×c-proj₁-F : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} -> Functor (C ×c D) C
×c-proj₁-F {C = C} {D} = record {FObj = proj₁ ; FMap = proj₁ ; isFunctor = record {≈-cong = proj₁ ; identity = ≈-Reasoning.refl-hom C ; distr = ≈-Reasoning.refl-hom C}}

×c-proj₂-F : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} -> Functor (C ×c D) D
×c-proj₂-F {C = C} {D} = record {FObj = proj₂ ; FMap = proj₂ ; isFunctor = record {≈-cong = proj₂ ; identity = ≈-Reasoning.refl-hom D ; distr = ≈-Reasoning.refl-hom D}}

×c-diag-F : {c₁ c₂ ℓ : Level} (C : Category c₁ c₂ ℓ) -> Functor C (C ×c C)
×c-diag-F C = record {FObj = \a -> a , a ; FMap = \f -> f , f ; isFunctor = record {≈-cong = \x -> x , x ; identity = ≈-Reasoning.refl-hom (C ×c C) ; distr = ≈-Reasoning.refl-hom (C ×c C)}}


DiscreteCat : {ℓ : Level} (A : Set ℓ) -> Category ℓ ℓ ℓ
DiscreteCat A = record {
    Obj = A ;
    Hom = _≡_ ;
    _∘_ = flip trans ;
    _≈_ = _≡_ ;
    Id = refl ;
    isCategory = record {
        isEquivalence = isEquivalence ;
        identityL = \{_ _ f} -> trans-reflʳ f;
        identityR = refl ;
        ∘-resp-≈ = \{_ _ _ f g h i} -> trans-resp f g h i ;
        associative = \{_ _ _ _ h g f} -> trans-assoc f g h } }
    where
        trans-reflʳ : {a b : A} -> (f : a ≡ b) -> trans f refl ≡ f
        trans-reflʳ refl = refl
        trans-resp : {a b c : A} -> (f g : a ≡ b) -> (h i : b ≡ c) -> h ≡ i -> f ≡ g -> trans f h ≡ trans g i
        trans-resp refl refl refl refl refl refl = refl
        trans-assoc : {a b c d : A} -> (f : a ≡ b) -> (g : b ≡ c) -> (h : c ≡ d) -> trans (trans f g) h ≡ trans f (trans g h)
        trans-assoc refl refl refl = refl

data Unit : Set where
    ⁎ : Unit

𝟙 : Category _ _ _
𝟙 = DiscreteCat Unit

𝟙×c- : {c₁ c₂ ℓ : Level} {C : Category c₁ c₂ ℓ} -> 𝟙 ×c C ≅ C
𝟙×c- {C = C} = record {
    F = F ;
    G = G ;
    inverse = record {
        FG=id = record { fmapEq = ≋-Reasoning.refl-hom C } ;
        GF=id = record {　fmapEq = sub　} } }
    where
        F : Functor (𝟙 ×c C) C
        F = ×c-proj₂-F
        G : Functor C (𝟙 ×c C)
        G = record {
            FObj = \a -> ⁎ , a ;
            FMap = \f -> refl , f ;
            isFunctor = record {
                ≈-cong = \x -> refl , x ;
                identity = \{a} -> ≈-Reasoning.refl-hom (𝟙 ×c C) {⁎ , a} {⁎ , a} ;
                distr = \{a} {_} {c} -> ≈-Reasoning.refl-hom (𝟙 ×c C) {⁎ , a} {⁎ , c} } }
        sub : {a b : Obj (𝟙 ×c C)} {f : Hom (𝟙 ×c C) a b} -> 𝟙 ×c C [ FMap (Fcomp G F) f ≋ f ]
        sub {⁎ , a} {⁎ , b} {refl , f} = ≋-Reasoning.refl-hom (𝟙 ×c C)

-×c𝟙 : {c₁ c₂ ℓ : Level} {C : Category c₁ c₂ ℓ} -> C ×c 𝟙 ≅ C
-×c𝟙 = ≅-trans ×c-comm 𝟙×c-
