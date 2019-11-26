module Product where

open import Level
open import Relation.Binary.Core
open import Data.Product using (_×_; _,_; map; zip)

open import Category

product : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′} -> Category c₁ c₂ ℓ -> Category c₁′ c₂′ ℓ′ -> Category (c₁ ⊔ c₁′) (c₂ ⊔ c₂′) (ℓ ⊔ ℓ′)
product {c₁} {c₂} {ℓ} {c₁′} {c₂′} {ℓ′} C D = record { Obj = obj ; Hom = hom ; _≈_ = _≈_ ; _∘_ = _∘_ ; Id = id ; isCategory = isCategory }
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
