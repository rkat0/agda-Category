module Equivalence where

open import Level
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality using (_≡_; cong₂; refl; sym)

open import Category

data _[_≋_] {c₁ c₂ ℓ : Level} (C : Category c₁ c₂ ℓ) {a b : Obj C} (f : Hom C a b)
        : {a′ b′ : Obj C} -> Hom C a′ b′ -> Set (c₂ ⊔ ℓ) where
    ≈⇒≋ : {g : Hom C a b} -> C [ f ≈ g ] -> C [ f ≋ g ]

infix 4 _[_≋_]

≋⇒≈ : {c₁ c₂ ℓ : Level} {C : Category c₁ c₂ ℓ} {a b : Obj C} {f g : Hom C a b} -> C [ f ≋ g ] -> C [ f ≈ g ]
≋⇒≈ (≈⇒≋ f≈g) = f≈g

dom-eq-≋ : {c₁ c₂ ℓ : Level} {C : Category c₁ c₂ ℓ} {a b a′ b′ : Obj C} {f : Hom C a b} {g : Hom C a′ b′} -> C [ f ≋ g ] -> a ≡ a′
dom-eq-≋ (≈⇒≋ f≈g) = refl
cod-eq-≋ : {c₁ c₂ ℓ : Level} {C : Category c₁ c₂ ℓ} {a b a′ b′ : Obj C} {f : Hom C a b} {g : Hom C a′ b′} -> C [ f ≋ g ] -> b ≡ b′
cod-eq-≋ (≈⇒≋ f≈g) = refl
subst-dom : {c₁ c₂ ℓ : Level} {C : Category c₁ c₂ ℓ} {a b a′ : Obj C} -> a ≡ a′ -> Hom C a b -> Hom C a′ b
subst-dom refl f = f
subst-cod : {c₁ c₂ ℓ : Level} {C : Category c₁ c₂ ℓ} {a b b′ : Obj C} -> b ≡ b′ -> Hom C a b -> Hom C a b′
subst-cod refl f = f
subst-dom-≋ : {c₁ c₂ ℓ : Level} {C : Category c₁ c₂ ℓ} {a b a′ : Obj C} -> (p : a ≡ a′) -> (f : Hom C a b) -> C [ f ≋ subst-dom {C = C} p f ]
subst-dom-≋ {C = C} refl f = ≈⇒≋ (≈-Reasoning.refl-hom C)
subst-cod-≋ : {c₁ c₂ ℓ : Level} {C : Category c₁ c₂ ℓ} {a b b′ : Obj C} -> (p : b ≡ b′) -> (f : Hom C a b) -> C [ f ≋ subst-cod {C = C} p f ]
subst-cod-≋ {C = C} refl f = ≈⇒≋ (≈-Reasoning.refl-hom C)

module ≋-Reasoning {c₁ c₂ ℓ : Level} (C : Category c₁ c₂ ℓ) where
    _∘_ : {a b c : Obj C} -> Hom C b c -> Hom C a b -> Hom C a c
    f ∘ g = C [ f ∘ g ]
    _≈_ : {a b : Obj C} -> Rel (Hom C a b) ℓ
    f ≈ g = C [ f ≈ g ]
    _≋_ : {a b a′ b′ : Obj C} -> Hom C a b -> Hom C a′ b′ -> Set (c₂ ⊔ ℓ)
    f ≋ g = C [ f ≋ g ]
    infix 9 _∘_
    infix 4 _≈_
    infix 4 _≋_

    refl-hom : {a b : Obj C} {f : Hom C a b} -> f ≋ f
    refl-hom = ≈⇒≋ (IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory C)))
    sym-hom : {a b a′ b′ : Obj C} {f : Hom C a b} {g : Hom C a′ b′} -> f ≋ g -> g ≋ f
    sym-hom (≈⇒≋ f≈g) = ≈⇒≋ (IsEquivalence.sym (IsCategory.isEquivalence (Category.isCategory C)) f≈g)
    trans-hom : {a b a′ b′ a′′ b′′ : Obj C} {f : Hom C a b} {g : Hom C a′ b′} {h : Hom C a′′ b′′} -> f ≋ g -> g ≋ h -> f ≋ h
    trans-hom (≈⇒≋ f≈g) (≈⇒≋ g≈h) = ≈⇒≋ (IsEquivalence.trans (IsCategory.isEquivalence (Category.isCategory C)) f≈g g≈h)
    assoc-hom : {a b c d : Obj C} {f : Hom C c d} {g : Hom C b c} {h : Hom C a b} -> f ∘ (g ∘ h) ≋ (f ∘ g) ∘ h
    assoc-hom = ≈⇒≋ (IsCategory.associative (Category.isCategory C))
    ∘-resp-≋ : {a b c a′ b′ c′ : Obj C} {f : Hom C a b} {h : Hom C b c} {g : Hom C a′ b′} {i : Hom C b′ c′} -> h ≋ i -> f ≋ g -> h ∘ f ≋ i ∘ g
    ∘-resp-≋ (≈⇒≋ h≈i) (≈⇒≋ f≈g) = ≈⇒≋ (IsCategory.∘-resp-≈ (Category.isCategory C) h≈i f≈g)

    identityL : {a b : Obj C} {f : Hom C a b} -> Id C b ∘ f ≋ f
    identityL = ≈⇒≋ (IsCategory.identityL (Category.isCategory C))
    identityR : {a b : Obj C} {f : Hom C a b} -> f ∘ Id C a ≋ f
    identityR = ≈⇒≋ (IsCategory.identityR (Category.isCategory C))

    infix 3 _∎
    infixr 2 _≋⟨_⟩_ _≈⟨_⟩_ _≋⟨⟩_
    infix 1 begin≈_ begin≋_
    begin≈_ : {a b : Obj C} {f g : Hom C a b} -> f ≋ g -> f ≈ g
    begin≈ (≈⇒≋ f≈g) = f≈g
    begin≋_ : {a b a′ b′ : Obj C} {f : Hom C a b} {g : Hom C a′ b′} -> f ≋ g -> f ≋ g
    begin≋ f≋g = f≋g
    _≋⟨_⟩_ : {a b a′ b′ a′′ b′′ : Obj C} -> (f : Hom C a b) -> {g : Hom C a′ b′} {h : Hom C a′′ b′′} -> f ≋ g -> g ≋ h -> f ≋ h
    _ ≋⟨ f≋g ⟩ g≋h = trans-hom f≋g g≋h
    _≈⟨_⟩_ : {a b a′ b′ : Obj C} -> (f : Hom C a b) -> {g : Hom C a b} {h : Hom C a′ b′} -> f ≈ g -> g ≋ h -> f ≋ h
    _ ≈⟨ f≈g ⟩ g≋h = trans-hom (≈⇒≋ f≈g) g≋h
    _≋⟨⟩_ : {a b a′ b′ : Obj C} -> (f : Hom C a b) -> {g : Hom C a′ b′} -> f ≋ g -> f ≋ g
    _ ≋⟨⟩ f≋g = f≋g
    _∎ : {a b : Obj C} -> (f : Hom C a b) -> f ≋ f
    _ ∎ = refl-hom

infix 4 _≡F_
record _≡F_ {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
        {C : Category c₁ c₂ ℓ}
        {D : Category c₁′ c₂′ ℓ′}
        (F G : Functor C D)
        : Set (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′) where
    field
        fmapEq : ∀ {a b : Obj C} {f : Hom C a b} -> D [ FMap F f ≋ FMap G f ]

    fobjEq : {a : Obj C} -> FObj F a ≡ FObj G a
    fobjEq {a} = dom-eq-≋ (fmapEq {f = Id C a})

    subst-dom-eq : {a : Obj C} {c : Obj D} -> Hom D (FObj F a) c ≡ Hom D (FObj G a) c
    subst-dom-eq = cong₂ (Hom D) fobjEq refl
    subst-cod-eq : {a : Obj C} {d : Obj D} -> Hom D d (FObj F a) ≡ Hom D d (FObj G a)
    subst-cod-eq = cong₂ (Hom D) refl fobjEq

    subst⇒dom : {a : Obj C} {c : Obj D} -> Hom D (FObj F a) c -> Hom D (FObj G a) c
    subst⇒dom f = subst-dom {C = D} fobjEq f
    subst⇒cod : {a : Obj C} {d : Obj D} -> Hom D d (FObj F a) -> Hom D d (FObj G a)
    subst⇒cod f = subst-cod {C = D} fobjEq f

    subst⇒dom-≋ : {a : Obj C} {c : Obj D} {f : Hom D (FObj F a) c} -> D [ f ≋ subst⇒dom f ]
    subst⇒dom-≋ {f = f} = subst-dom-≋ fobjEq f
    subst⇒cod-≋ : {a : Obj C} {d : Obj D} {f : Hom D d (FObj F a)} -> D [ f ≋ subst⇒cod f ]
    subst⇒cod-≋ {f = f} = subst-cod-≋ fobjEq f

    subst⇒∘dom : {a : Obj C} {c d : Obj D} {f : Hom D c d} {g : Hom  D (FObj F a) c} -> D [ D [ f ∘ subst⇒dom g ] ≈ subst⇒dom (D [ f ∘ g ]) ]
    subst⇒∘dom {f = f} {g} = let open ≋-Reasoning D in
        begin≈ f ∘ subst⇒dom g
        ≋⟨ ∘-resp-≋ refl-hom (sym-hom subst⇒dom-≋) ⟩ f ∘ g
        ≋⟨ subst⇒dom-≋ ⟩ subst⇒dom (f ∘ g)
        ∎
    subst⇒∘cod : {a : Obj C} {c d : Obj D} {f : Hom D d (FObj F a)} {g : Hom  D c d} -> D [ D [ subst⇒cod f ∘ g ] ≈ subst⇒cod (D [ f ∘ g ]) ]
    subst⇒∘cod {f = f} {g} = let open ≋-Reasoning D in
        begin≈ subst⇒cod f ∘ g
        ≋⟨ ∘-resp-≋ (sym-hom subst⇒cod-≋) refl-hom ⟩ f ∘ g
        ≋⟨ subst⇒cod-≋ ⟩ subst⇒cod (f ∘ g)
        ∎

sym-≡F : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {F G : Functor C D} -> F ≡F G -> G ≡F F
sym-≡F {D = D} F≡G = record {fmapEq = ≋-Reasoning.sym-hom D (_≡F_.fmapEq F≡G)}

infix 4 _≡N_
record _≡N_ {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
        {C : Category c₁ c₂ ℓ}
        {D : Category c₁′ c₂′ ℓ′}
        {F G : Functor C D}
        (α β : NatTrans F G)
        : Set (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′) where
    field
        tmapEq : ∀ {a : Obj C} -> D [ TMap α a ≈ TMap β a ]

record FInverse {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
        {C : Category c₁ c₂ ℓ}
        {D : Category c₁′ c₂′ ℓ′}
        (F : Functor C D)
        (G : Functor D C)
        : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
    field
        FG=id : Fcomp F G ≡F IdFunctor
        GF=id : Fcomp G F ≡F IdFunctor

record Isomorphic {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
        (C : Category c₁ c₂ ℓ)
        (D : Category c₁′ c₂′ ℓ′)
        : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
    field
        F : Functor C D
        G : Functor D C
        inverse : FInverse F G

infix 4 _≅_
_≅_ : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} -> Category c₁ c₂ ℓ -> Category c₁′ c₂′ ℓ′ -> Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′))
C ≅ D = Isomorphic C D

record NatInverse {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
        {C : Category c₁ c₂ ℓ}
        {D : Category c₁′ c₂′ ℓ′}
        {F G : Functor C D}
        (α : NatTrans F G)
        (β : NatTrans G F)
        : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
    field
        αβ=id : α ◯ β ≡N IdNatTrans G
        βα=id : β ◯ α ≡N IdNatTrans F

record NatIsomorphic {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
        {C : Category c₁ c₂ ℓ}
        {D : Category c₁′ c₂′ ℓ′}
        (F G : Functor C D)
        : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
    field
        F⇒G : NatTrans F G
        G⇒F : NatTrans G F
        inverse : NatInverse F⇒G G⇒F

record Equivalence {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
        (C : Category c₁ c₂ ℓ)
        (D : Category c₁′ c₂′ ℓ′)
        : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
    field
        F : Functor C D
        G : Functor D C
        FG≃id : NatIsomorphic (Fcomp F G) IdFunctor
        GF≃id : NatIsomorphic (Fcomp G F) IdFunctor

infix 4 _≃_
_≃_ : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} -> Category c₁ c₂ ℓ -> Category c₁′ c₂′ ℓ′ -> Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′))
C ≃ D = Equivalence C D

◯-idL : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {F G : Functor C D} {α : NatTrans F G} -> IdNatTrans G ◯ α ≡N α
◯-idL {D = D} = record {tmapEq = IsCategory.identityL (Category.isCategory D)}

◯-idR : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {F G : Functor C D} {α : NatTrans F G} -> α ◯ IdNatTrans F ≡N α
◯-idR {D = D} = record {tmapEq = IsCategory.identityR (Category.isCategory D)}

≡F⇒NatIso : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {F G : Functor C D} -> F ≡F G -> NatIsomorphic F G
≡F⇒NatIso {C = C} {D} {F} {G} F≡G = record {
    F⇒G = α ;
    G⇒F = β ;
    inverse = record {αβ=id = record {tmapEq = tmapEq1}; βα=id = record {tmapEq = tmapEq2}} }
    where
        open _≡F_
        α : NatTrans F G
        α = record {
            TMap = \a -> subst⇒cod F≡G (Id D (FObj F a));
            isNatTrans = record {commute = \{a} {b} {f} -> let open ≋-Reasoning D in
                begin≈ subst⇒cod F≡G (Id D (FObj F b)) ∘ FMap F f
                ≋⟨ ∘-resp-≋ (sym-hom (subst⇒cod-≋ F≡G)) refl-hom ⟩ Id D (FObj F b) ∘ FMap F f
                ≋⟨ identityL ⟩ FMap F f
                ≋⟨ sym-hom identityR ⟩ FMap F f ∘ Id D (FObj F a)
                ≋⟨ ∘-resp-≋ (fmapEq F≡G) (subst⇒cod-≋ F≡G) ⟩ FMap G f ∘ subst⇒cod F≡G (Id D (FObj F a))
                ∎
            }}
        G≡F : G ≡F F
        G≡F = sym-≡F F≡G
        β : NatTrans G F
        β = record {
            TMap = \a -> subst⇒cod G≡F (Id D (FObj G a));
            isNatTrans = record {commute = \{a} {b} {f} -> let open ≋-Reasoning D in
                begin≈ subst⇒cod G≡F (Id D (FObj G b)) ∘ FMap G f
                ≋⟨ ∘-resp-≋ (sym-hom (subst⇒cod-≋ G≡F)) refl-hom ⟩ Id D (FObj G b) ∘ FMap G f
                ≋⟨ identityL ⟩ FMap G f
                ≋⟨ sym-hom identityR ⟩ FMap G f ∘ Id D (FObj G a)
                ≋⟨ ∘-resp-≋ (fmapEq G≡F) (subst⇒cod-≋ G≡F) ⟩ FMap F f ∘ subst⇒cod G≡F (Id D (FObj G a))
                ∎
            }}
        tmapEq1 : {a : Obj C} -> D [ TMap (α ◯ β) a ≈ TMap (IdNatTrans G) a ]
        tmapEq1 {a} = let open ≋-Reasoning D in
            begin≈ TMap (α ◯ β) a
            ≋⟨⟩ subst⇒cod F≡G (Id D (FObj F a)) ∘ subst⇒cod G≡F (Id D (FObj G a))
            ≋⟨ ∘-resp-≋ (sym-hom (subst⇒cod-≋ F≡G)) refl-hom ⟩ Id D (FObj F a) ∘ subst⇒cod G≡F (Id D (FObj G a))
            ≋⟨ identityL ⟩ subst⇒cod G≡F (Id D (FObj G a))
            ≋⟨ sym-hom (subst⇒cod-≋ G≡F) ⟩ Id D (FObj G a)
            ≋⟨⟩ TMap (IdNatTrans G) a
            ∎
        tmapEq2 : {a : Obj C} -> D [ TMap (β ◯ α) a ≈ TMap (IdNatTrans F) a ]
        tmapEq2 {a} = let open ≋-Reasoning D in
            begin≈ TMap (β ◯ α) a
            ≋⟨⟩ subst⇒cod G≡F (Id D (FObj G a)) ∘ subst⇒cod F≡G (Id D (FObj F a))
            ≋⟨ ∘-resp-≋ (sym-hom (subst⇒cod-≋ G≡F)) refl-hom ⟩ Id D (FObj G a) ∘ subst⇒cod F≡G (Id D (FObj F a))
            ≋⟨ identityL ⟩ subst⇒cod F≡G (Id D (FObj F a))
            ≋⟨ sym-hom (subst⇒cod-≋ F≡G) ⟩ Id D (FObj F a)
            ≋⟨⟩ TMap (IdNatTrans F) a
            ∎

Iso⇒Equ : {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} -> Isomorphic C D -> Equivalence C D
Iso⇒Equ iso = record {
    F = Isomorphic.F iso ;
    G = Isomorphic.G iso ;
    FG≃id = ≡F⇒NatIso (FInverse.FG=id (Isomorphic.inverse iso)) ;
    GF≃id = ≡F⇒NatIso (FInverse.GF=id (Isomorphic.inverse iso)) }
