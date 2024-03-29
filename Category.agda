module Category where

open import Level
open import Function using (flip; id)
open import Relation.Binary
open import Relation.Binary.Core

record IsCategory {c₁ c₂ ℓ : Level}
        (Obj : Set c₁)
        (Hom : Obj -> Obj -> Set c₂)
        (_≈_ : {A B : Obj} -> Rel (Hom A B) ℓ)
        (_∘_ : {A B C : Obj} -> Hom B C -> Hom A B -> Hom A C)
        (Id : {A : Obj} -> Hom A A) : Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
    field
        isEquivalence : {A B : Obj} -> IsEquivalence {c₂} {ℓ} {Hom A B} _≈_
        identityL : {A B : Obj} -> {f : Hom A B} -> (Id ∘ f) ≈ f
        identityR : {A B : Obj} -> {f : Hom A B} -> (f ∘ Id) ≈ f
        ∘-resp-≈ : {A B C : Obj} -> {f g : Hom A B} -> {h i : Hom B C} -> h ≈ i -> f ≈ g -> (h ∘ f) ≈ (i ∘ g)
        associative : {A B C D : Obj} -> {f : Hom C D} -> {g : Hom B C} -> {h : Hom A B} -> (f ∘ (g ∘ h)) ≈ ((f ∘ g) ∘ h)

record Category c₁ c₂ ℓ : Set (suc (c₁ ⊔ c₂ ⊔ ℓ)) where
    infixr 9 _∘_
    infix 4 _≈_
    field
        Obj : Set c₁
        Hom : Obj -> Obj -> Set c₂
        _∘_ : {A B C : Obj} -> Hom B C -> Hom A B -> Hom A C
        _≈_ : {A B : Obj} -> Rel (Hom A B) ℓ
        Id : {A : Obj} -> Hom A A
        isCategory : IsCategory Obj Hom _≈_ _∘_ Id

    op : Category c₁ c₂ ℓ
    op = record {Obj = Obj ; Hom = flip Hom ; _∘_ = flip _∘_ ; _≈_ = _≈_ ; Id = Id ; isCategory = opIsCategory}
        where
            opIsCategory : IsCategory {c₁} {c₂} {ℓ} Obj (flip Hom) _≈_ (flip _∘_) Id
            opIsCategory = record {
                    isEquivalence = IsCategory.isEquivalence isCategory ;
                    identityL = IsCategory.identityR isCategory ;
                    identityR = IsCategory.identityL isCategory ;
                    ∘-resp-≈ = flip (IsCategory.∘-resp-≈ isCategory) ;
                    associative = IsEquivalence.sym (IsCategory.isEquivalence isCategory) (IsCategory.associative isCategory)
                }
    dom : {A B : Obj} -> Hom A B -> Obj
    dom {A} _ = A
    cod : {A B : Obj} -> Hom A B -> Obj
    cod {_} {B} _ = B

Obj : ∀ {c₁ c₂ ℓ} -> (C : Category c₁ c₂ ℓ) -> Set c₁
Obj C = Category.Obj C

Hom : ∀ {c₁ c₂ ℓ} -> (C : Category c₁ c₂ ℓ) -> Obj C -> Obj C -> Set c₂
Hom C = Category.Hom C

_[_≈_] : ∀ {c₁ c₂ ℓ} -> (C : Category c₁ c₂ ℓ) -> {A B : Obj C} -> Rel (Hom C A B) ℓ
C [ f ≈ g ] = Category._≈_ C f g

_[_∘_] : ∀ {c₁ c₂ ℓ} -> (C : Category c₁ c₂ ℓ) -> {a b c : Obj C} -> Hom C b c -> Hom C a b -> Hom C a c
C [ f ∘ g ] = Category._∘_ C f g

infixr 9 _[_∘_]
infix 4 _[_≈_]

Id : ∀ {c₁ c₂ ℓ} -> (C : Category c₁ c₂ ℓ) -> (A : Obj C) -> Hom C A A
Id C A = Category.Id C {A}

record IsFunctor {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
        (C : Category c₁ c₂ ℓ)
        (D : Category c₁′ c₂′ ℓ′)
        (FObj : Obj C -> Obj D)
        (FMap : {A B : Obj C} -> Hom C A B -> Hom D (FObj A) (FObj B))
        : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
    field
        ≈-cong : {A B : Obj C} {f g : Hom C A B} -> C [ f ≈ g ] -> D [ FMap f ≈ FMap g ]
        identity : {A : Obj C} -> D [ FMap {A} {A} (Id C A) ≈ Id D (FObj A) ]
        distr : {a b c : Obj C} {f : Hom C b c} {g : Hom C a b} -> D [ FMap (C [ f ∘ g ]) ≈ D [ FMap f ∘ FMap g ] ]

record Functor {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
        (domain : Category c₁ c₂ ℓ)
        (codomain : Category c₁′ c₂′ ℓ′)
        : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
    field
        FObj : Obj domain -> Obj codomain
        FMap : {A B : Obj domain} -> Hom domain A B -> Hom codomain (FObj A) (FObj B)
        isFunctor : IsFunctor domain codomain FObj FMap

FObj : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} -> (F : Functor C D) -> Obj C -> Obj D
FObj F = Functor.FObj F

FMap : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {A B : Obj C} -> (F : Functor C D) -> Hom C A B -> Hom D (FObj F A) (FObj F B)
FMap {A = A} {B = B} F = Functor.FMap F {A} {B}

record IsNatTrans {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
        {C : Category c₁ c₂ ℓ}
        {D : Category c₁′ c₂′ ℓ′}
        (F G : Functor C D)
        (TMap : (A : Obj C) -> Hom D (FObj F A) (FObj G A))
        : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
    field
        commute : {a b : Obj C} {f : Hom C a b} -> D [ D [ TMap b ∘ FMap F f ] ≈ D [ FMap G f ∘ TMap a ] ]

record NatTrans {c₁ c₂ ℓ c₁′ c₂′ ℓ′ : Level}
        {C : Category c₁ c₂ ℓ}
        {D : Category c₁′ c₂′ ℓ′}
        (F G : Functor C D)
        : Set (suc (c₁ ⊔ c₂ ⊔ ℓ ⊔ c₁′ ⊔ c₂′ ⊔ ℓ′)) where
    field
        TMap : (A : Obj C) -> Hom D (FObj F A) (FObj G A)
        isNatTrans : IsNatTrans F G TMap

TMap : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {F G : Functor C D} -> (α : NatTrans F G) -> (A : Obj C) -> Hom D (FObj F A) (FObj G A)
TMap α = NatTrans.TMap α


module ≈-Reasoning {c₁ c₂ ℓ : Level} (C : Category c₁ c₂ ℓ) where
    _∘_ : {a b c : Obj C} -> Hom C b c -> Hom C a b -> Hom C a c
    f ∘ g = C [ f ∘ g ]
    _≈_ : {a b : Obj C} -> Rel (Hom C a b) ℓ
    f ≈ g = C [ f ≈ g ]
    infixr 9 _∘_
    infix 4 _≈_

    refl-hom : {a b : Obj C} {f : Hom C a b} -> f ≈ f
    refl-hom = IsEquivalence.refl (IsCategory.isEquivalence (Category.isCategory C))
    sym-hom : {a b : Obj C} {f g : Hom C a b} -> f ≈ g -> g ≈ f
    sym-hom = IsEquivalence.sym (IsCategory.isEquivalence (Category.isCategory C))
    trans-hom : {a b : Obj C} {f g h : Hom C a b} -> f ≈ g -> g ≈ h -> f ≈ h
    trans-hom = IsEquivalence.trans (IsCategory.isEquivalence (Category.isCategory C))
    identityL : {a b : Obj C} {f : Hom C a b} -> Id C b ∘ f ≈ f
    identityL = IsCategory.identityL (Category.isCategory C)
    identityR : {a b : Obj C} {f : Hom C a b} -> f ∘ Id C a ≈ f
    identityR = IsCategory.identityR (Category.isCategory C)
    ∘-resp-≈ : {a b c : Obj C} {f g : Hom C a b} {h i : Hom C b c} -> h ≈ i -> f ≈ g -> h ∘ f ≈ i ∘ g
    ∘-resp-≈ = IsCategory.∘-resp-≈ (Category.isCategory C)
    assoc-hom : {a b c d : Obj C} {f : Hom C c d} {g : Hom C b c} {h : Hom C a b} -> f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
    assoc-hom = IsCategory.associative (Category.isCategory C)

    infix 3 _∎
    infixr 2 _≈⟨_⟩_ _≈⟨⟩_
    infix 1 begin_
    begin_ : {a b : Obj C} {f g : Hom C a b} -> f ≈ g -> f ≈ g
    begin f≈g = f≈g
    _≈⟨_⟩_ : {a b : Obj C} -> (f : Hom C a b) -> {g h : Hom C a b} -> f ≈ g -> g ≈ h -> f ≈ h
    _ ≈⟨ f≈g ⟩ g≈h = trans-hom f≈g g≈h
    _≈⟨⟩_ : {a b : Obj C} -> (f : Hom C a b) -> {g : Hom C a b} -> f ≈ g -> f ≈ g
    _ ≈⟨⟩ f≈g = f≈g
    _∎ : {a b : Obj C} -> (f : Hom C a b) -> f ≈ f
    _ ∎ = refl-hom

IdFunctor : ∀ {c₁ c₂ ℓ} {C : Category c₁ c₂ ℓ} -> Functor C C
IdFunctor {C = C} = record {FObj = id ; FMap = id ; isFunctor = isFunctor}
    where
        isFunctor : IsFunctor C C id id
        isFunctor = record {≈-cong = id ; identity = ≈-Reasoning.refl-hom C ; distr = ≈-Reasoning.refl-hom C}

Fcomp : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′ c₁″ c₂″ ℓ″} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {E : Category c₁″ c₂″ ℓ″} -> Functor D E -> Functor C D -> Functor C E
Fcomp {C = C} {E = E} F G = record {FObj = FObj_FG ; FMap = FMap_FG ; isFunctor = isFunctor}
    where
        FObj_FG : Obj C -> Obj E
        FObj_FG a = FObj F (FObj G a)
        FMap_FG : {a b : Obj C} -> Hom C a b -> Hom E (FObj_FG a) (FObj_FG b)
        FMap_FG f = FMap F (FMap G f)
        isFunctor : IsFunctor C E FObj_FG FMap_FG
        isFunctor = record {≈-cong = ≈-cong ; identity = identity ; distr = distr}
            where
                ≈-cong : {a b : Obj C} {f g : Hom C a b} -> C [ f ≈ g ] -> E [ FMap_FG f ≈ FMap_FG g ]
                ≈-cong f≈g = (IsFunctor.≈-cong (Functor.isFunctor F) (IsFunctor.≈-cong (Functor.isFunctor G) f≈g))
                identity : {a : Obj C} -> E [ FMap_FG (Id C a) ≈ Id E (FObj_FG a) ]
                identity = IsEquivalence.trans (IsCategory.isEquivalence (Category.isCategory E)) (IsFunctor.≈-cong (Functor.isFunctor F) (IsFunctor.identity (Functor.isFunctor G))) (IsFunctor.identity (Functor.isFunctor F))
                distr : {a b c : Obj C} {f : Hom C b c} {g : Hom C a b} -> E [ FMap_FG (C [ f ∘ g ]) ≈ E [ FMap_FG f ∘ FMap_FG g ] ]
                distr = IsEquivalence.trans (IsCategory.isEquivalence (Category.isCategory E)) (IsFunctor.≈-cong (Functor.isFunctor F) (IsFunctor.distr (Functor.isFunctor G))) (IsFunctor.distr (Functor.isFunctor F))

IdNatTrans : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} (F : Functor C D) -> NatTrans F F
IdNatTrans {C = C} {D} F = record {TMap = tmap ; isNatTrans = isNatTrans}
    where
        tmap : (a : Obj C) -> Hom D (FObj F a) (FObj F a)
        tmap a = Id D (FObj F a)
        isNatTrans : IsNatTrans F F tmap
        isNatTrans = record {commute = commute}
            where
                commute : {a b : Obj C} {f : Hom C a b} -> D [ D [ tmap b ∘ FMap F f ] ≈ D [ FMap F f ∘ tmap a ] ]
                commute {a} {b} {f} = let open ≈-Reasoning D in
                    begin tmap b ∘ FMap F f
                    ≈⟨ IsCategory.identityL (Category.isCategory D) ⟩ FMap F f
                    ≈⟨ sym-hom (IsCategory.identityR (Category.isCategory D)) ⟩ FMap F f ∘ tmap a
                    ∎

infixr 8 _◯_ _⁎_

_◯_ : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {F G H : Functor C D} -> NatTrans G H -> NatTrans F G -> NatTrans F H
_◯_ {C = C} {D} {F} {G} {H} α β = record {TMap = tmap ; isNatTrans = isNatTrans}
    where
        tmap : (A : Obj C) -> Hom D (FObj F A) (FObj H A)
        tmap A = D [ TMap α A ∘ TMap β A ]
        isNatTrans : IsNatTrans F H tmap
        isNatTrans = record {commute = commute}
            where
                commute : {a b : Obj C} {f : Hom C a b} -> D [ D [ tmap b ∘ FMap F f ] ≈ D [ FMap H f ∘ tmap a ] ]
                commute {a} {b} {f} = let open ≈-Reasoning D in
                    begin (TMap α b ∘ TMap β b) ∘ FMap F f
                    ≈⟨ sym-hom (IsCategory.associative (Category.isCategory D)) ⟩ TMap α b ∘ (TMap β b ∘ FMap F f)
                    ≈⟨ IsCategory.∘-resp-≈ (Category.isCategory D) refl-hom (IsNatTrans.commute (NatTrans.isNatTrans β)) ⟩ TMap α b ∘ (FMap G f ∘ TMap β a)
                    ≈⟨ IsCategory.associative (Category.isCategory D) ⟩ (TMap α b ∘ FMap G f) ∘ TMap β a
                    ≈⟨ IsCategory.∘-resp-≈ (Category.isCategory D) (IsNatTrans.commute (NatTrans.isNatTrans α)) refl-hom ⟩ (FMap H f ∘ TMap α a) ∘ TMap β a
                    ≈⟨ sym-hom (IsCategory.associative (Category.isCategory D)) ⟩ FMap H f ∘ (TMap α a ∘ TMap β a)
                    ∎

_⁎_ : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′ c₁″ c₂″ ℓ″} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {E : Category c₁″ c₂″ ℓ″} {F G : Functor C D} {H I : Functor D E} -> NatTrans H I -> NatTrans F G -> NatTrans (Fcomp H F) (Fcomp I G)
_⁎_ {C = C} {D} {E} {F} {G} {H} {I} α β = record {TMap = tmap ; isNatTrans = isNatTrans}
    where
        HF : Functor C E
        HF = Fcomp H F
        IG : Functor C E
        IG = Fcomp I G
        tmap : (a : Obj C) -> Hom E (FObj HF a) (FObj IG a)
        tmap a = E [ TMap α (FObj G a) ∘ FMap H (TMap β a) ]
        isNatTrans : IsNatTrans HF IG tmap
        isNatTrans = record {commute = commute}
            where
                commute : {a b : Obj C} {f : Hom C a b} -> E [ E [ tmap b ∘ FMap HF f ] ≈ E [ FMap IG f ∘ tmap a ] ]
                commute {a} {b} {f} = let open ≈-Reasoning E in
                    begin (TMap α (FObj G b) ∘ FMap H (TMap β b)) ∘ FMap H (FMap F f)
                    ≈⟨ sym-hom assoc-hom ⟩ TMap α (FObj G b) ∘ (FMap H (TMap β b) ∘ FMap H (FMap F f))
                    ≈⟨ ∘-resp-≈ refl-hom (sym-hom (IsFunctor.distr (Functor.isFunctor H))) ⟩ TMap α (FObj G b) ∘ (FMap H (D [ TMap β b ∘ FMap F f ]))
                    ≈⟨ ∘-resp-≈ refl-hom (IsFunctor.≈-cong (Functor.isFunctor H) (IsNatTrans.commute (NatTrans.isNatTrans β))) ⟩ TMap α (FObj G b) ∘ (FMap H (D [ FMap G f ∘ TMap β a ]))
                    ≈⟨ ∘-resp-≈ refl-hom (IsFunctor.distr (Functor.isFunctor H)) ⟩ TMap α (FObj G b) ∘ (FMap H (FMap G f) ∘ FMap H (TMap β a))
                    ≈⟨ assoc-hom ⟩ (TMap α (FObj G b) ∘ FMap H (FMap G f)) ∘ FMap H (TMap β a)
                    ≈⟨ ∘-resp-≈ (IsNatTrans.commute (NatTrans.isNatTrans α)) refl-hom ⟩ (FMap I (FMap G f) ∘ TMap α (FObj G a)) ∘ FMap H (TMap β a)
                    ≈⟨ sym-hom assoc-hom ⟩ FMap I (FMap G f) ∘ (TMap α (FObj G a) ∘ FMap H (TMap β a))
                    ∎

NT-interchange : ∀ {c₁ c₂ ℓ c₁′ c₂′ ℓ′ c₁″ c₂″ ℓ″} {C : Category c₁ c₂ ℓ} {D : Category c₁′ c₂′ ℓ′} {E : Category c₁″ c₂″ ℓ″} {F G H : Functor C D} {F′ G′ H′ : Functor D E} {α : NatTrans G H} {β : NatTrans F G} {α′ : NatTrans G′ H′} {β′ : NatTrans F′ G′} {a : Obj C} -> E [ TMap ((α′ ◯ β′) ⁎ (α ◯ β)) a ≈ TMap ((α′ ⁎ α) ◯ (β′ ⁎ β)) a ]
NT-interchange {D = D} {E} {F} {G} {H} {F′} {G′} {H′} {α} {β} {α′} {β′} {a} = let open ≈-Reasoning E in
    begin TMap ((α′ ◯ β′) ⁎ (α ◯ β)) a
    ≈⟨⟩ TMap (α′ ◯ β′) (FObj H a) ∘ FMap F′ (TMap (α ◯ β) a)
    ≈⟨⟩ (TMap α′ (FObj H a) ∘ TMap β′ (FObj H a)) ∘ FMap F′ (D [ TMap α a ∘ TMap β a ])
    ≈⟨ ∘-resp-≈ refl-hom (IsFunctor.distr (Functor.isFunctor F′)) ⟩ (TMap α′ (FObj H a) ∘ TMap β′ (FObj H a)) ∘ (FMap F′ (TMap α a) ∘ FMap F′ (TMap β a))
    ≈⟨ assoc-hom ⟩ ((TMap α′ (FObj H a) ∘ TMap β′ (FObj H a)) ∘ FMap F′ (TMap α a)) ∘ FMap F′ (TMap β a)
    ≈⟨ ∘-resp-≈ (sym-hom assoc-hom) refl-hom ⟩ (TMap α′ (FObj H a) ∘ (TMap β′ (FObj H a) ∘ FMap F′ (TMap α a))) ∘ FMap F′ (TMap β a)
    ≈⟨ ∘-resp-≈ (∘-resp-≈ refl-hom (IsNatTrans.commute (NatTrans.isNatTrans β′))) refl-hom ⟩ (TMap α′ (FObj H a) ∘ (FMap G′ (TMap α a) ∘ TMap β′ (FObj G a))) ∘ FMap F′ (TMap β a)
    ≈⟨ ∘-resp-≈ assoc-hom refl-hom ⟩ ((TMap α′ (FObj H a) ∘ FMap G′ (TMap α a)) ∘ TMap β′ (FObj G a)) ∘ FMap F′ (TMap β a)
    ≈⟨ sym-hom assoc-hom ⟩ (TMap α′ (FObj H a) ∘ FMap G′ (TMap α a)) ∘ (TMap β′ (FObj G a) ∘ FMap F′ (TMap β a))
    ≈⟨⟩ (TMap (α′ ⁎ α) a) ∘ (TMap (β′ ⁎ β) a)
    ≈⟨⟩ TMap ((α′ ⁎ α) ◯ (β′ ⁎ β)) a
    ∎
