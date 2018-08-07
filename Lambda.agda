{-# OPTIONS --cubical #-}

-- TODO :
--  * decidable
--  * monads 
--  * the syntax is horrible 
--  * more expressive error checking
--  * cubical

module Lambda where

open import Agda.Primitive renaming (lsuc to ℓₛ)
open import Data.Bool hiding (_≟_)
open import Data.Nat hiding (erase; _≟_; _⊔_)
open import Data.Maybe
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])
-- open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≡ᵖ_ ; refl to reflᵖ ; cong to congᵖ ; _≢_ to _≢ᵖ_) hiding ([_])
open import Relation.Nullary using (Dec ; yes ; no)
open import Data.String renaming (String to Name ; _≟_ to _≟ˢ_) 
open import Data.List hiding ([_] ; lookup)
open import Data.Unit hiding (_≟_ ; _≤?_)
open import Data.Empty using (⊥-elim)

open import Cubical.FromStdLib hiding (⊥-elim)
-- open import Cubical.PathPrelude 
-- open import Cubical.PushOut renaming (P to _⊎_ ; inl to inj₁ ; inr to inj₂)

data World : Set where
  observer   : World
  observable : World
  varʷ       : Name → World

-- inj-varʷ : ∀ {n₁ n₂} → (varʷ n₁) ≡ (varʷ n₂) → n₁ ≡ n₂
-- inj-varʷ refl = refl 

-- postulate eq-to-path : ∀ {α β : Set} → α ≡ᵖ β → α ≡ β

record Monad {ℓ₁ ℓ₂} (m : Set ℓ₁ → Set ℓ₂) : Set (ℓₛ ℓ₁ ⊔ ℓ₂) where 
    infixl 1 _>>=_ _>>_
    field 
        return : ∀ {a} → a → m a
        _>>=_ : ∀ {a b} → m a → (a → m b) → m b 
        
    _>>_ : ∀ {a b} → m a → m b → m b
    m₁ >> m₂ = m₁ >>= λ _ → m₂ 
    
open Monad {{...}}

instance 
    MonadMaybe : ∀ {ℓ} → Monad {ℓ} Maybe 
    _>>=_ {{MonadMaybe}} m f = maybe f nothing m
    return {{MonadMaybe}} z = just z
    
_≟ʷ_ : (ω₁ : World) → (ω₂ : World) → Maybe (ω₁ ≡ ω₂)
observer    ≟ʷ observer   = just refl
observable  ≟ʷ observable = just refl
(varʷ ω₁)   ≟ʷ (varʷ ω₂) with ω₁ ≟ˢ ω₂
...                      | yes p = just (cong varʷ p)
...                      | _     = nothing
_           ≟ʷ _         = nothing 

⌊_⌋ : ∀ {ℓ} {p : Set ℓ} → Dec p → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false



data Type : Set where
  𝟙ᵀ 𝟚ᵀ ℕᵀ      : Type
  □ ◇           : Type → Type
  _⇒_ _×ᵀ_ _⊎ᵀ_ : Type → Type  → Type
  _at_          : Type → World → Type

⟦_⟧ : Type → Set
⟦ ℕᵀ     ⟧ = ℕ
⟦ 𝟚ᵀ     ⟧ = Bool
⟦ 𝟙ᵀ     ⟧ = ⊤
⟦ □ τ    ⟧ = ⟦ τ ⟧
⟦ ◇ τ    ⟧ = ⟦ τ ⟧
⟦ τ at ω ⟧ = ⟦ τ ⟧
⟦ α ⇒  β ⟧ = ⟦ α ⟧ → ⟦ β ⟧
⟦ α ×ᵀ β ⟧ = ⟦ α ⟧ × ⟦ β ⟧
⟦ α ⊎ᵀ β ⟧ = ⟦ α ⟧ ⊎ ⟦ β ⟧

Context : Set
Context = List (Name × Type × World)

data _∈_<_> (n : Name) : Context → World → Set where
  inside  : ∀ {Γ τ ω} → n ∈ ((n , τ , ω) ∷ Γ) < ω >
  outside : ∀ {Γ y τ ω₁ ω₂} → n ∈ Γ < ω₁ > → n ∈ ((y , τ , ω₂) ∷ Γ) < ω₁ >

lookupType : (x : Name) (ω : World) (Γ : Context)  → x ∈ Γ < ω > → Type
lookupType x _ [] ()
lookupType x _ ((_ , τ , _) ∷ Γ) inside       = τ
lookupType x ω (_ ∷ Γ)           (outside pf) = lookupType x ω Γ pf

skipOne : ∀ {Γ x y τ ω₁ ω₂} → ((x ≢ y) ⊎ (ω₁ ≢ ω₂)) → x ∈ ((y , τ , ω₂) ∷ Γ) < ω₁ > → x ∈ Γ < ω₁ >
skipOne (inj₁ xneq) inside      = ⊥-elim (xneq refl)
skipOne (inj₂ ωneq) inside      = ⊥-elim (ωneq refl)
skipOne neq         (outside i) = i

lookup : (x : Name) (ω : World) (Γ : Context)  → Maybe (x ∈ Γ < ω >)
lookup x ω [] = nothing
lookup x ω₁ ((y , τ , ω₂) ∷ Γ) with x ≟ˢ y | ω₁ ≟ʷ ω₂  | lookup x ω₁ Γ
...                            | yes refl  | just refl | _       = just inside 
...                            | yes p     | _         | just a  = just (outside a)
...                            | yes p     | _         | _       = nothing
...                            | _         | _         | just a  = just (outside a)
...                            | _         | _         | _       = nothing

data is_mobile : Type → Set where
  𝟚ᵀᵐ   :                                              is 𝟚ᵀ           mobile
  ℕᵀᵐ   :                                              is ℕᵀ           mobile
  𝟙ᵀᵐ   :                                              is 𝟙ᵀ           mobile
  □ᵐ_   : ∀ {A   : Type}                             → is (□ A)        mobile
  ◇ᵐ_   : ∀ {A   : Type}                             → is (◇ A)        mobile
  _atᵐ_ : ∀ {A   : Type} → {ω : World}               → is (  A at ω  ) mobile
  _×ᵐ_  : ∀ {A B : Type} → is A mobile → is B mobile → is (  A ×ᵀ B  ) mobile
  _⊎ᵐ_  : ∀ {A B : Type} → is A mobile → is B mobile → is (  A ⊎ᵀ B  ) mobile

inj≡⇒ : ∀ {σ₁ σ₂ τ₁ τ₂ : Type} → σ₁ ⇒ τ₁ ≡ σ₂ ⇒ τ₂ → (σ₁ ≡ σ₂) × (τ₁ ≡ τ₂)
inj≡⇒ refl = refl , refl

inj≡× : ∀ {σ₁ σ₂ τ₁ τ₂ : Type} → σ₁ ×ᵀ τ₁ ≡ σ₂ ×ᵀ τ₂ → (σ₁ ≡ σ₂) × (τ₁ ≡ τ₂)
inj≡× refl = refl , refl

inj≡⊎ : ∀ {σ₁ σ₂ τ₁ τ₂ : Type} → σ₁ ⊎ᵀ τ₁ ≡ σ₂ ⊎ᵀ τ₂ → (σ₁ ≡ σ₂) × (τ₁ ≡ τ₂)
inj≡⊎ refl = refl , refl

inj≡□ : ∀ {σ τ : Type} → □ σ ≡ □ τ → σ ≡ τ
inj≡□ refl = refl

inj≡◇ : ∀ {σ τ : Type} → ◇ σ ≡ ◇ τ → σ ≡ τ
inj≡◇ refl = refl

inj≡at : ∀ {σ₁ σ₂ : Type} {ω₁ ω₂ : World} → σ₁ at ω₁ ≡ σ₂ at ω₂ → (σ₁ ≡ σ₂) × (ω₁ ≡ ω₂)
inj≡at refl = refl , refl

inj×ᵐ : ∀ {τ σ : Type} → is ( τ ×ᵀ σ ) mobile → is τ mobile × is σ mobile
inj×ᵐ ( x ×ᵐ y ) = x , y

inj⊎ᵐ : ∀ {τ σ : Type} → is ( τ ⊎ᵀ σ ) mobile → is τ mobile × is σ mobile
inj⊎ᵐ ( x ⊎ᵐ y ) = x , y

≟ᵐ : (τ : Type) → Maybe (is τ mobile)
≟ᵐ ℕᵀ         = just ℕᵀᵐ
≟ᵐ 𝟚ᵀ         = just 𝟚ᵀᵐ
≟ᵐ 𝟙ᵀ         = just 𝟙ᵀᵐ
≟ᵐ (□ τ)      = just □ᵐ_
≟ᵐ (◇ τ)      = just ◇ᵐ_
≟ᵐ ( τ at ω ) = just _atᵐ_
≟ᵐ ( τ ⇒  σ ) = nothing 
≟ᵐ ( τ ×ᵀ σ ) with ≟ᵐ τ | ≟ᵐ σ
...           | just p  | just q = just ( p ×ᵐ q )
...           | _       | _      = nothing 
≟ᵐ ( τ ⊎ᵀ σ ) with ≟ᵐ τ | ≟ᵐ σ
...           | just p  | just q = just ( p ⊎ᵐ q )
...           | _       | _      = nothing

mutual
  binRel≟ : (x₁ y₁ x₂ y₂ : Type) → (R : Type → Type → Type)
            → (∀ {σ σ′ τ τ′} → R σ τ ≡ R σ′ τ′ → (σ ≡ σ′) × (τ ≡ τ′))
            → Maybe ((R x₁ y₁) ≡ (R x₂ y₂))
  binRel≟ x₁ y₁ x₂ y₂ R inj≡R with x₁ ≟ x₂ | y₁ ≟ y₂
  ...                         | just refl  | just refl = just refl
  ...                         | _          | _         = nothing

  unRel≟ : (x y : Type) → (R : Type → Type) → (∀ {σ τ} → R σ ≡ R τ → σ ≡ τ) → Maybe (R x ≡ R y)
  unRel≟ x y R inj≡R with x ≟ y
  ...                | just p = just (cong R p)
  ...                | _      = nothing

  _≟_ : (τ σ : Type) → Maybe (τ ≡ σ)
  ℕᵀ          ≟ ℕᵀ           = just refl
  𝟚ᵀ          ≟ 𝟚ᵀ           = just refl
  𝟙ᵀ          ≟ 𝟙ᵀ           = just refl
  □ σ         ≟ □ τ          = unRel≟ σ τ □ inj≡□
  ◇ σ         ≟ ◇ τ          = unRel≟ σ τ ◇ inj≡◇
  ( σ₁ ⇒  τ ) ≟ ( σ₂ ⇒  τ₂ ) = binRel≟ σ₁ τ σ₂ τ₂ _⇒_ inj≡⇒
  ( σ₁ ×ᵀ τ ) ≟ ( σ₂ ×ᵀ τ₂ ) = binRel≟ σ₁ τ σ₂ τ₂ _×ᵀ_ inj≡×
  ( σ₁ ⊎ᵀ τ ) ≟ ( σ₂ ⊎ᵀ τ₂ ) = binRel≟ σ₁ τ σ₂ τ₂ _⊎ᵀ_ inj≡⊎
  ( x  at ω ) ≟ ( y  at ω₂ ) with x ≟ y | ω ≟ʷ ω₂
  ...                        | just refl | just refl = just refl
  ...                        | _         | _         = nothing 
  _           ≟ _            = nothing 

data _⊢_<_> (Γ : Context) : Type → World → Set where
  `tt : ∀ {ω} 
      --------------
      → Γ ⊢ 𝟙ᵀ < ω >
  

  `true : ∀ {ω} 
        --------------
        → Γ ⊢ 𝟚ᵀ < ω >
        
  `false : ∀ {ω} 
         --------------
         → Γ ⊢ 𝟚ᵀ < ω >
  
  `_∧_ : ∀ {ω} 
       → Γ ⊢ 𝟚ᵀ < ω > 
       → Γ ⊢ 𝟚ᵀ < ω > 
       --------------
       → Γ ⊢ 𝟚ᵀ < ω >
  
  `_∨_ : ∀ {ω} 
       → Γ ⊢ 𝟚ᵀ < ω > 
       → Γ ⊢ 𝟚ᵀ < ω > 
       --------------
       → Γ ⊢ 𝟚ᵀ < ω >
  
  `¬_ : ∀ {ω} 
      → Γ ⊢ 𝟚ᵀ < ω > 
      --------------
      → Γ ⊢ 𝟚ᵀ < ω >
  
  ⟨if_then_else_⟩ : ∀ {τ ω} 
                   → Γ ⊢ 𝟚ᵀ < ω > 
                   → Γ ⊢  τ < ω > 
                   → Γ ⊢  τ < ω > 
                   --------------
                   → Γ ⊢  τ < ω >
  

  `n_ : ∀ {ω} → ℕ 
      --------------
      → Γ ⊢ ℕᵀ < ω >
      
  `_≤_ : ∀ {ω} 
       → Γ ⊢ ℕᵀ < ω > 
       → Γ ⊢ ℕᵀ < ω > 
       ---------------
       →  Γ ⊢ 𝟚ᵀ < ω >
       
  `_+_ : ∀ {ω} 
       → Γ ⊢ ℕᵀ < ω > 
       → Γ ⊢ ℕᵀ < ω > 
       --------------
       → Γ ⊢ ℕᵀ < ω >
       
  `_*_ : ∀ {ω} 
       → Γ ⊢ ℕᵀ < ω > 
       → Γ ⊢ ℕᵀ < ω > 
       --------------
       → Γ ⊢ ℕᵀ < ω >
       

  `v : (x : Name) (ω : World) (i : x ∈ Γ < ω >) 
     ------------------------------------------
     → Γ ⊢ lookupType x ω Γ i < ω >
     
  `_·_ : ∀ {τ σ ω} 
       → Γ ⊢ ( τ ⇒ σ ) < ω > 
       → Γ ⊢ τ < ω > 
       ---------------------
       → Γ ⊢ σ < ω >

  ⟨λ_꞉_⇒_⟩ : ∀ {τ ω} 
           → (x : Name) (σ : Type) 
           → ((x , σ , ω) ∷ Γ) ⊢ τ < ω > 
           -----------------------------
           → Γ ⊢ ( σ ⇒ τ) < ω >


  `_,_ : ∀ {τ σ ω} 
       → Γ ⊢ τ < ω > 
       → Γ ⊢ σ < ω > 
       ----------------------
       → Γ ⊢ ( τ ×ᵀ σ ) < ω >
       
  `fst : ∀ {τ σ ω} 
       → Γ ⊢ ( τ ×ᵀ σ ) < ω > 
       ----------------------
       → Γ ⊢ τ < ω >
       
  `snd : ∀ {τ σ ω} 
       → Γ ⊢ ( τ ×ᵀ σ ) < ω > 
       ----------------------
       → Γ ⊢ σ < ω >
       
  ⟨inl_as_⟩ : ∀ {τ ω} 
            → Γ ⊢ τ < ω > → (σ : Type) 
            --------------------------
            → Γ ⊢ ( τ ⊎ᵀ σ ) < ω >
            
  ⟨inr_as_⟩ : ∀ {σ ω} 
            → Γ ⊢ σ < ω > → (τ : Type) 
            --------------------------
            → Γ ⊢ ( τ ⊎ᵀ σ ) < ω >
            
  ⟨case_of_||_⟩ : ∀ {τ σ υ ω} 
                → Γ ⊢ ( τ ⊎ᵀ σ ) < ω > 
                → Γ ⊢ ( τ ⇒ υ ) < ω > 
                → Γ ⊢ ( σ ⇒ υ ) < ω > 
                ----------------------
                → Γ ⊢ υ < ω >
                

  `hold : ∀ {τ ω} 
        → Γ ⊢ τ < ω > 
        -----------------------
        → Γ ⊢ ( τ at ω ) < ω >

  ⟨leta_≔_∈_⟩ : ∀ {τ σ ω ω₂} 
                → (x : Name) → Γ ⊢ ( τ at ω₂ ) < ω > 
                → ((x , τ , ω₂) ∷ Γ) ⊢ σ < ω > 
                -------------------------------------
                → Γ ⊢ σ < ω >


  `box : ∀ {τ ω} 
       → (id : Name) → Γ ⊢ τ < varʷ id > 
       ---------------------------------
       → Γ ⊢ (□ τ) < ω >
       
  `unbox : ∀ {τ ω} 
         → Γ ⊢ (□ τ) < ω > 
         ------------------
         → Γ ⊢ τ < ω >
         

  `here : ∀ {τ ω} 
        → Γ ⊢ τ < ω > 
        ------------------
        → Γ ⊢ (◇ τ) < ω >
        
  ⟨letd_,_≔_∈_⟩ : ∀ {τ σ ω} 
                   → (n : Name) → (x : Name) 
                   → Γ ⊢ (◇ τ) < ω > 
                   → ((x , τ , (varʷ n)) ∷ Γ) ⊢ σ < ω > 
                   ------------------------------------
                   → Γ ⊢ σ < ω >


  get : ∀ {τ ω ω₂} 
      → is τ mobile 
      → Γ ⊢ τ < ω₂ > 
      --------------
      → Γ ⊢ τ < ω >

[_]<_> : Type → World → Set
[ τ ]< ω > = [] ⊢ τ < ω >

data LDSL : Set where
    𝟙ᵉ Trueᵉ Falseᵉ     : LDSL
    Varᵉ                : Name  → World → LDSL
    ℕᵉ                  : ℕ     → LDSL
    _∧ᵉ_ _∨ᵉ_ _⊎ᵉ_ _×ᵉ_ : LDSL  → LDSL  → LDSL
    _≤ᵉ_ _·ᵉ_ _,ᵉ_      : LDSL  → LDSL  → LDSL
    ¬ᵉ fstᵉ sndᵉ        : LDSL  → LDSL
    holdᵉ unboxᵉ hereᵉ  : LDSL  → LDSL
    condᵉ caseᵉ         : LDSL  → LDSL  → LDSL → LDSL
    λᵉ                  : Name  → Type  → LDSL → LDSL
    □ᵉ                  : Name  → LDSL  → LDSL
    inlᵉ                : LDSL  → Type  → LDSL
    inrᵉ                : LDSL  → Type  → LDSL
    letaᵉ               : Name  → LDSL  → LDSL → LDSL
    letdᵉ               : Name  → Name  → LDSL → LDSL → LDSL
    getᵉ                : World → LDSL  → LDSL

erase : ∀ {Γ τ ω} → Γ ⊢ τ < ω > → LDSL
erase `tt                         = 𝟙ᵉ
erase `true                       = Trueᵉ
erase `false                      = Falseᵉ
erase (`n x                     ) = ℕᵉ x
erase (` x ∧ y                  ) = (erase x) ∧ᵉ (erase y)
erase (` x ∨ y                  ) = (erase x) ∨ᵉ (erase y)
erase (`¬ x                     ) = ¬ᵉ (erase x)
erase ⟨if c then x else y       ⟩ = condᵉ (erase c) (erase x) (erase y)
erase (` x ≤ y                  ) = (erase x) ≤ᵉ (erase y)
erase (` x + y                  ) = (erase x) ⊎ᵉ (erase y)
erase (` x * y                  ) = (erase x) ×ᵉ (erase y)
erase (`v id ω i                ) = Varᵉ id ω
erase (` f · x                  ) = (erase f) ·ᵉ (erase x)
erase (⟨λ id ꞉ σ ⇒ y ⟩          ) = λᵉ id σ (erase y)
erase (` x , y                  ) = (erase x) ,ᵉ (erase y)
erase (`fst p                   ) = fstᵉ (erase p)
erase (`snd p                   ) = sndᵉ (erase p)
erase ⟨inl x as σ               ⟩ = inlᵉ (erase x) σ
erase ⟨inr x as τ               ⟩ = inrᵉ (erase x) τ
erase ⟨case x of f || g         ⟩ = caseᵉ (erase x) (erase f) (erase g)
erase (`hold x                  ) = holdᵉ (erase x)
erase ⟨leta id ≔ x ∈ y          ⟩ = letaᵉ id (erase x) (erase y)
erase (`box ω x                 ) = □ᵉ ω (erase x)
erase (`unbox x                 ) = unboxᵉ (erase x)
erase (`here  x                 ) = hereᵉ (erase x)
erase ⟨letd n , id ≔ x ∈ y      ⟩ = letdᵉ n id (erase x) (erase y)
erase (get {ω₂ = ω₂} m x        ) = getᵉ ω₂ (erase x)

data Infer (Γ : Context) : LDSL → Set where
  well : (τ : Type) (ω : World) (t : Γ ⊢ τ < ω >) → Infer Γ (erase t)
  ill  : {e : LDSL} → Infer Γ e
  
-- instance 
--     MonadInfer : ∀ {ℓ} {Γ : Context} → Monad {ℓ} (Infer Γ)
--     _>>=_ {{MonadInfer}} m (well p) = m p
--     _>>=_ {{MonadInfer}} m ill      = ill
 
infer : (ω : World) (Γ : Context) (e : LDSL) → Infer Γ e
infer ω₁ Γ 𝟙ᵉ     = well 𝟙ᵀ ω₁ `tt
infer ω₁ Γ Trueᵉ  = well 𝟚ᵀ ω₁ `true
infer ω₁ Γ Falseᵉ = well 𝟚ᵀ ω₁ `false
infer ω₁ Γ (ℕᵉ x) = well ℕᵀ ω₁ (`n x)

infer ω₁ Γ (Varᵉ x ω₂) with ω₁ ≟ʷ ω₂ | lookup x ω₁ Γ
...                   | just refl    | just p = well (lookupType x ω₁ Γ p) ω₁ (`v x ω₁ p)
...                   | _            | _      = ill

infer ω₁ Γ (x ∧ᵉ y) with infer ω₁ Γ x | infer ω₁ Γ y
...                 | well 𝟚ᵀ  ω₂ t   | well 𝟚ᵀ  ω₃ u with ω₁ ≟ʷ ω₂ | ω₂ ≟ʷ ω₃
...                                                   | just refl   | just refl = well 𝟚ᵀ ω₁ (` t ∧ u )
...                                                   | _           | _         = ill
infer ω₁ Γ (_ ∧ᵉ _) | _               | _ = ill

infer ω₁ Γ (x ∨ᵉ y) with infer ω₁ Γ x | infer ω₁ Γ y
...                 | well 𝟚ᵀ ω₂ t    | well 𝟚ᵀ ω₃ u with ω₁ ≟ʷ ω₂ | ω₂ ≟ʷ ω₃
...                                                  | just refl   | just refl = well 𝟚ᵀ ω₂ (` t ∨ u )
...                                                  | _           | _         = ill
infer ω₁ Γ (_ ∨ᵉ _) | _               | _ = ill

infer ω₁ Γ (x ⊎ᵉ y) with infer ω₁ Γ x | infer ω₁ Γ y
...                 | well ℕᵀ ω₂ t    | well ℕᵀ ω₃ u with ω₁ ≟ʷ ω₂ | ω₂ ≟ʷ ω₃
...                                                  | just refl   | just refl = well ℕᵀ ω₂ (` t + u )
...                                                  | _           | _         = ill
infer ω₁ Γ (_ ⊎ᵉ _) | _               | _ = ill

infer ω₁ Γ (x ×ᵉ y) with infer ω₁ Γ x | infer ω₁ Γ y
...                 | well ℕᵀ ω₂ t    | well ℕᵀ ω₃ u with ω₁ ≟ʷ ω₂ | ω₂ ≟ʷ ω₃
...                                                  | just refl   | just refl = well ℕᵀ ω₂ (` t * u )
...                                                  | _           | _         = ill
infer ω₁ Γ (_ ×ᵉ _) | _               | _ = ill

infer ω₁ Γ (x ≤ᵉ y) with infer ω₁ Γ x | infer ω₁ Γ y
...                 | well ℕᵀ ω₂ t    | well ℕᵀ ω₃ u with ω₁ ≟ʷ ω₂ | ω₂ ≟ʷ ω₃
...                                                  | just refl   | just refl = well 𝟚ᵀ ω₂ (` t ≤ u )
...                                                  | _           | _         = ill
infer ω₁ Γ (_ ≤ᵉ _) | _               | _ = ill

infer ω₁ Γ (f ·ᵉ x) with infer ω₁ Γ f       | infer ω₁ Γ x
...                 | well ( σ₁ ⇒ τ ) ω₂ t | well σ₂ ω₃ u with σ₁ ≟ σ₂ | ω₁ ≟ʷ ω₂ | ω₂ ≟ʷ ω₃
...                                                       | just refl | just refl | just refl = well τ ω₂ (` t · u )
...                                                       | _         | _         | _         = ill
infer ω₁ Γ (_ ·ᵉ _) | _                     | _ = ill

infer ω₁ Γ (x ,ᵉ y) with infer ω₁ Γ x | infer ω₁ Γ y
...                 | well σ ω₂ t     | well τ ω₃ u with ω₁ ≟ʷ ω₂ | ω₂ ≟ʷ ω₃
...                                                 | just refl   | just refl = well ( σ ×ᵀ τ ) ω₂ (` t , u )
...                                                 | _           | _         = ill
infer ω₁ Γ (_ ,ᵉ _) | _ | _ = ill

infer ω₁ Γ (¬ᵉ x) with infer ω₁ Γ x
...               | well 𝟚ᵀ ω₂ t with ω₁ ≟ʷ ω₂
...                              | just refl = well 𝟚ᵀ ω₂ (`¬ t)
...                              | _         = ill
infer ω₁ Γ (¬ᵉ x) | _ = ill

infer ω₁ Γ (fstᵉ p) with infer ω₁ Γ p
...                 | well ( τ ×ᵀ σ ) ω₂ t with ω₁ ≟ʷ ω₂
...                                        | just refl = well τ ω₂ (`fst t)
...                                        | _         = ill
infer ω₁ Γ (fstᵉ p) | _ = ill


infer ω₁ Γ (sndᵉ p) with infer ω₁ Γ p
...                 | well ( τ ×ᵀ σ ) ω₂ t with ω₁ ≟ʷ ω₂
...                                        | just refl = well σ ω₁ (`snd t)
...                                        | _         = ill
infer ω₁ Γ (sndᵉ p) | _ = ill

infer ω₁ Γ (condᵉ c x y) with infer ω₁ Γ c | infer ω₁ Γ x | infer ω₁ Γ y
...                      | well 𝟚ᵀ ω₂ t    | well τ ω₃ u  | well τ₂ ω₄ v with τ ≟ τ₂ | ω₁ ≟ʷ ω₂  | ω₂ ≟ʷ ω₃  | ω₃ ≟ʷ ω₄
...                                                                      | just refl | just refl | just refl | just refl = well τ₂ ω₂ ⟨if t then u else v ⟩
...                                                                      | _         | _         | _         | _         = ill
infer ω₁ Γ (condᵉ c x y) | _               | _            | _ = ill

infer ω₁ Γ (caseᵉ x f g) with infer ω₁ Γ x        | infer ω₁ Γ f           | infer ω₁ Γ g
...                      | well ( τ₁ ⊎ᵀ σ₁ ) ω₂ t | well ( τ₂ ⇒ υ₁ ) ω₃ u  | well ( σ₂ ⇒ υ₂ ) ω₄ v with τ₁ ≟ τ₂ | σ₁ ≟ σ₂    | υ₁ ≟ υ₂    | ω₁ ≟ʷ ω₂   | ω₂ ≟ʷ ω₃  | ω₃ ≟ʷ ω₄
...                                                                                                | just refl  | just refl  | just refl  | just refl  | just refl | just refl = well υ₂ ω₂ ⟨case t of u || v ⟩
...                                                                                                | _          | _          | _          | _          | _         | _         = ill
infer ω₁ Γ (caseᵉ x f g) | _                      | _                      | _ = ill

infer ω₁ Γ (λᵉ id σ y) with infer ω₁ ((id , σ , ω₁) ∷ Γ) y
...                    | well τ ω₂ t with ω₁ ≟ʷ ω₂
...                                  | just refl = well ( σ ⇒ τ ) ω₁ ⟨λ id ꞉ σ ⇒ t ⟩
...                                  | _         = ill
infer ω₁ Γ (λᵉ id σ y) | _ = ill

infer ω₁ Γ (□ᵉ n e) with infer (varʷ n) Γ e
...                 | well τ ω₂ t with ω₂ ≟ʷ (varʷ n)
...                               | just refl = well (□ τ) ω₁ (`box n t)
...                               | _         = ill
infer ω₁ Γ (□ᵉ n e) | _ = ill

infer ω₁ Γ (inlᵉ e σ) with infer ω₁ Γ e
...                   | well τ ω₂ t with ω₁ ≟ʷ ω₂
...                                 | just refl = well ( τ ⊎ᵀ σ ) ω₂ ⟨inl t as σ ⟩
...                                 | _         = ill
infer ω₁ Γ (inlᵉ e σ) | _ = ill

infer ω₁ Γ (inrᵉ e τ) with infer ω₁ Γ e
...                   | well σ ω₂ t with ω₁ ≟ʷ ω₂
...                                 | just refl = well ( τ ⊎ᵀ σ ) ω₂ ⟨inr t as τ ⟩
...                                 | _         = ill
infer ω₁ Γ (inrᵉ e τ) | _ = ill

infer ω₁ Γ (holdᵉ x) with infer ω₁ Γ x
...                  | well τ ω₂ t with ω₁ ≟ʷ ω₂
...                                | just refl = well ( τ at ω₂ ) ω₂ (`hold t)
...                                | _         = ill
infer ω₁ Γ (holdᵉ x) | _ = ill

infer ω₁ Γ (unboxᵉ x) with infer ω₁ Γ x
...                   | well (□ τ) ω₂ t with ω₁ ≟ʷ ω₂
...                                      | just refl = well τ ω₂ (`unbox t)
...                                      | _         = ill
infer ω₁ Γ (unboxᵉ x) | _ = ill

infer ω₁ Γ (hereᵉ x) with infer ω₁ Γ x
...                  | well τ ω₂ t with ω₁ ≟ʷ ω₂
...                                | just p = well (◇ τ) ω₂ (`here t)
...                                | _      = ill
infer ω₁ Γ (hereᵉ x) | _ = ill

infer ω₁ Γ (letaᵉ id x y) with infer ω₁ Γ x
...                       | well ( τ at ω₃ ) ω₂ t with infer ω₁ ((id , τ , ω₃) ∷ Γ) y
...                                               | well σ ω₄ u with ω₁ ≟ʷ ω₂ | ω₁ ≟ʷ ω₄
...                                                             | just refl   | just refl = well σ ω₁ ⟨leta id ≔ t ∈ u ⟩ 
...                                                             | _           | _         = ill
infer ω₁ Γ (letaᵉ id .(erase t) y) | well ( τ at ω₃) ω₂ t | _ = ill
infer ω₁ Γ (letaᵉ id x y)          | _ = ill

infer ω₁ Γ (letdᵉ n id x y) with infer ω₁ Γ x
...                         | well (◇ τ) ω₂ t with infer ω₁ ((id , τ , varʷ n) ∷ Γ ) y
...                                            | well σ ω₃ u with ω₁ ≟ʷ ω₂ | ω₁ ≟ʷ ω₃
...                                                          | just refl | just refl = well σ ω₁ ⟨letd n , id ≔ t ∈ u ⟩
...                                                          | _         | _         = ill
infer ω₁ Γ (letdᵉ n id .(erase t) y) | well (◇ τ) ω₂ t | ill = ill
infer ω₁ Γ (letdᵉ n id x y)          | _                     = ill

infer ω₁ Γ (getᵉ ω₂ e) with infer ω₂ Γ e
...                    | well τ ω₃ t with ω₂ ≟ʷ ω₃ | ≟ᵐ τ
...                                  | just refl   | just m = well τ ω₁ (get m t)
...                                  | _           | _      = ill
infer ω₁ Γ (getᵉ ω₂ e) | ill = ill

data Env : Context → Set₁ where
  E  : Env  []
  C  : ∀ {Γ : Context} {x : Name} {τ : Type} {ω : World} → ⟦ τ ⟧ → Env Γ → Env ((x , τ , ω) ∷ Γ)

lookupEnv : ∀ {Γ : Context} {x} {ω : World} → Env Γ → (mem : x ∈ Γ < ω >) → ⟦ lookupType x ω Γ mem ⟧
lookupEnv E ()
lookupEnv (C τᵗ env) inside =  τᵗ
lookupEnv (C _ env) (outside mem) = lookupEnv env mem

interpret : ∀ {Γ : Context} {τ : Type} {ω : World} → Env Γ → Γ ⊢ τ < ω > → ⟦ τ ⟧
interpret env `tt                        = tt
interpret env `true                      = true
interpret env `false                     = false
interpret env (` x ∧ y                 ) = (interpret env x) ∧ (interpret env y)
interpret env (` x ∨ y                 ) = (interpret env x) ∨ (interpret env y)
interpret env (`¬ x                    ) = not (interpret env x)
interpret env ⟨if c then x else y      ⟩ = if (interpret env c) then (interpret env x) else (interpret env y)
interpret env ⟨case x of f || g        ⟩ = [ interpret env f , interpret env g ] (interpret env x)
interpret env (`n x                    ) = x
interpret env (` x ≤ y                 ) = ⌊ ( interpret env x ) ≤? ( interpret env y ) ⌋
interpret env (` x + y                 ) = (interpret env x) + (interpret env y)
interpret env (` x * y                 ) = (interpret env x) * (interpret env y)
interpret env (`v x ω i                ) = lookupEnv env i
interpret env (` f · x                 ) = (interpret env f) (interpret env x)
interpret env ⟨λ _ ꞉ σ ⇒ τ             ⟩ = λ (x : ⟦ σ ⟧) → interpret (C x env) τ
interpret env (` x , y                 ) = interpret env x , interpret env y
interpret env (`fst p                  ) = fst (interpret env p)
interpret env (`snd p                  ) = snd (interpret env p)
interpret env ⟨inl x as _              ⟩ = inj₁ (interpret env x)
interpret env ⟨inr y as _              ⟩ = inj₂ (interpret env y)
interpret env (`hold x                 ) = interpret env x
interpret env (get _ y                 ) = interpret env y
interpret env (`unbox x                ) = interpret env x
interpret env (`box id x               ) = interpret env x
interpret env (`here x                 ) = interpret env x
interpret env ⟨leta _     ≔ x ∈ y      ⟩ = let val = interpret env x in interpret (C val env) y
interpret env ⟨letd _ , _ ≔ x ∈ y      ⟩ = let val = interpret env x in interpret (C val env) y

⦅_⦆ : ∀ {τ ω} → [ τ ]< ω > → ⟦ τ ⟧
⦅ x ⦆ = interpret E x

module _ {τ α β : Type} where 
    ω = observer

    2+2 : [ ℕᵀ ]< ω >
    2+2 = ` ⟨λ "x" ꞉ ℕᵀ ⇒ (` (`v "x" ω inside) + (`v "x" ω inside)) ⟩ · `n 2

    2+2≡4 : ⦅ 2+2 ⦆ ≡ 4
    2+2≡4 = refl

    expr+double : LDSL
    expr+double = λᵉ "x" ℕᵀ ((Varᵉ "x" ω) ⊎ᵉ (Varᵉ "x" ω))

    term+double : [ ℕᵀ ⇒ ℕᵀ ]< ω >
    term+double = ⟨λ "x" ꞉ ℕᵀ ⇒ (` (`v "x" ω inside) + (`v "x" ω inside)) ⟩

    infer+double : infer ω [] expr+double ≡ well ( ℕᵀ ⇒ ℕᵀ) ω term+double
    infer+double = refl

    nat-ex : [ ℕᵀ ⇒ □ ℕᵀ ]< ω >
    nat-ex = ⟨λ "x" ꞉ ℕᵀ ⇒ `box "ω" (get ℕᵀᵐ (`v "x" ω inside)) ⟩

    nat-ex-erase-infer : infer ω [] (erase nat-ex) ≡ well ( ℕᵀ ⇒ □ ℕᵀ) ω nat-ex
    nat-ex-erase-infer = refl

    e₁ : [ □ τ ⇒ τ ]< ω >
    e₁ = ⟨λ "x" ꞉ _ ⇒ `unbox (`v "x" ω inside) ⟩

    e₂ : [ τ ⇒ ◇ τ ]< ω >
    e₂ = ⟨λ "x" ꞉ _ ⇒ `here (`v "x" ω inside) ⟩

    e₃ : [ ◇ (◇ τ) ⇒ ◇ τ ]< ω >
    e₃ = ⟨λ "x" ꞉ _ ⇒ ⟨letd "ω" , "y" ≔ `v "x" ω inside ∈ get ◇ᵐ_ (`v "y" (varʷ "ω") inside) ⟩ ⟩

    e₄ : [ ◇ (□ τ) ⇒ □ τ ]< ω >
    e₄ = ⟨λ "x" ꞉ _ ⇒ ⟨letd "ω" , "y" ≔ `v "x" ω inside ∈ get □ᵐ_ (`v "y" (varʷ "ω") inside) ⟩ ⟩

    e₅ : [ □ τ ⇒ □ (□ τ) ]< ω >
    e₅ = ⟨λ "x" ꞉ _ ⇒ `box "ω" (get □ᵐ_ (`v "x" ω inside)) ⟩

    e₆ : [ ◇ τ ⇒ □ (◇ τ) ]< ω >
    e₆ = ⟨λ "x" ꞉ _ ⇒ `box "ω" (get ◇ᵐ_ (`v "x" ω inside)) ⟩

    e₇ : [ □ ( α ⇒ β) ⇒ ( ◇ α ⇒ ◇ β) ]< ω >
    e₇ = ⟨λ "f" ꞉ _ ⇒ ⟨λ "x" ꞉ _ ⇒
            ⟨letd "ω" , "y" ≔ `v "x" ω inside ∈ get ◇ᵐ_ (`here (` 
                `unbox (get □ᵐ_ (`v "f" ω (outside (outside inside)))) · `v "y" (varʷ "ω") inside)) ⟩ ⟩ ⟩
