module Product where

open import Level
open import Relation.Binary.Core
open import Data.Product using (_×_; _,_; map; zip; proj₁; proj₂)

open import Category
open import Equivalence

infixr 5 _×c_
_×c_ : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′} -> Category c₁ c₂ ℓ -> Category c₁′ c₂′ ℓ′ -> Category (c₁ ⊔ c₁′) (c₂ ⊔ c₂′) (ℓ ⊔ ℓ′)
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

product-assoc : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ c₁″ c₂″ ℓ″ : Level} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {E : Category c₁″ c₂″ ℓ″} -> (C ×c D) ×c E ≅ C ×c (D ×c E)
product-assoc {C = C} {D} {E} = record {F = F ; G = G ; inverse = record {FG=id = FG=id ; GF=id = GF=id}}
    where
        F : Functor ((C ×c D) ×c E) (C ×c (D ×c E))
        F = record {
            FObj = \a -> proj₁ (proj₁ a) , (proj₂ (proj₁ a) , proj₂ a) ;
            FMap = \f -> proj₁ (proj₁ f) , (proj₂ (proj₁ f) , proj₂ f) ;
            isFunctor = record {
                ≈-cong = \x -> proj₁ (proj₁ x) , (proj₂ (proj₁ x) , proj₂ x) ;
                identity = ≈-Reasoning.refl-hom (C ×c (D ×c E)) ;
                distr = ≈-Reasoning.refl-hom (C ×c (D ×c E)) } }
        G : Functor (C ×c (D ×c E)) ((C ×c D) ×c E)
        G = record {
            FObj = \a -> (proj₁ a , proj₁ (proj₂ a)) , proj₂ (proj₂ a) ;
            FMap = \f -> (proj₁ f , proj₁ (proj₂ f)) , proj₂ (proj₂ f) ;
            isFunctor = record {
                ≈-cong = \x -> (proj₁ x , proj₁ (proj₂ x)) , proj₂ (proj₂ x) ;
                identity = ≈-Reasoning.refl-hom ((C ×c D) ×c E) ;
                distr = ≈-Reasoning.refl-hom ((C ×c D) ×c E) } }
        FG=id : Fcomp F G ≡F IdFunctor
        FG=id = record {fmapEq = ≋-Reasoning.refl-hom (C ×c (D ×c E))}
        GF=id : Fcomp G F ≡F IdFunctor
        GF=id = record {fmapEq = ≋-Reasoning.refl-hom ((C ×c D) ×c E)}
