module Lambda where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤?_; _≥_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no)
open import Function using (_∘_; _$_)
open import Data.Product

postulate fun_ext : ∀ {A B : Set} {f g : A → B} → ({x : A} → f x ≡ g x) → f ≡ g

data Fromℕ (n : ℕ) : ℕ → Set where
  inside  : (m : Fin n) → Fromℕ n (toℕ m)
  outside : (m : ℕ)     → Fromℕ n (n + m)

fromℕ : ∀ n m → Fromℕ n m
fromℕ zero    m    = outside m
fromℕ (suc n) zero = inside zero
fromℕ (suc n) (suc m)     with fromℕ n m
fromℕ (suc n) (suc .(toℕ m)) | inside m = inside (suc m)
fromℕ (suc n) (suc .(n + m)) | outside  m = outside m

infixr 30 _⇒_
data Type : Set where
  ı   : Type
  _⇒_ : Type → Type → Type

≡⇒₁ : ∀ {σ σ' τ τ' : Type} → σ ⇒ τ ≡ σ' ⇒ τ' → σ ≡ σ'
≡⇒₁ refl = refl 

≡⇒₂ : ∀ {σ σ' τ τ'} → σ ⇒ τ ≡ σ' ⇒ τ' → τ ≡ τ'
≡⇒₂ refl = refl

_≟_ : (τ σ : Type) → Dec (τ ≡ σ)
ı ≟ ı = yes refl 
ı ≟ _ ⇒ _ = no λ ()
_ ⇒ _ ≟ ı = no λ () 
σ₁ ⇒ τ₁ ≟ σ₂ ⇒ τ₂ with σ₁ ≟ σ₂  | τ₁ ≟ τ₂
...              | yes refl       | yes refl = yes refl
...              | no σ₁≢σ₂       | _        = no (σ₁≢σ₂ ∘ ≡⇒₁)
...              | _              | no τ₁≢τ₂ = no (τ₁≢τ₂ ∘ ≡⇒₂)

infixl 80 _∙_
data LDSL : Set where
  lit : ℕ → LDSL 
  var : ℕ → LDSL
  -- _⊕_ : LDSL → LDSL → LDSL
  _∙_ : LDSL → LDSL → LDSL
  lam : Type → LDSL → LDSL

Ctx : ℕ → Set
Ctx = Vec Type 

⟦_⟧ : Type → Set
⟦ ı ⟧ = ℕ
⟦ σ ⇒ τ ⟧ = ⟦ σ ⟧ → ⟦ τ ⟧

infixr 5 _∷_
data Env : ∀ {n : ℕ} → Ctx n → Set where
  []  : Env []
  _∷_ : ∀ {n : ℕ} {Γ : Ctx n} {τ : Type} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)

lookupEnv : ∀ {n : ℕ} {Γ : Ctx n} (m : Fin n) → Env Γ → ⟦ lookup m Γ ⟧
lookupEnv zero (x ∷ _) = x 
lookupEnv (suc n) (_ ∷ env) = lookupEnv n env 

data Term {n : ℕ} (Γ : Ctx n) : Type → Set where
  lit : ℕ
      ----------
      → Term Γ ı

  var : ∀ {τ : Type} → (v : Fin n) → τ ≡ lookup v Γ 
      ---------------------------------------------
      → Term Γ τ

  -- _⊕_ : Term Γ ı → Term Γ ı
  --     ----------------------
  --     → Term Γ ı
  
  _∙_ : ∀ {σ τ : Type} → Term Γ (σ ⇒ τ) 
      ---------------------------------
      → Term Γ σ → Term Γ τ
  
  lam : ∀ σ {τ : Type} → Term (σ ∷ Γ) τ 
      ---------------------------------
      → Term Γ (σ ⇒ τ)


Closed : Type → Set 
Closed = Term []

erase : ∀ {n : ℕ} {Γ : Ctx n} {τ : Type} → Term Γ τ → LDSL
erase (lit v)   = lit v 
erase (var x _) = var (toℕ x)
-- erase (f ⊕ g)   = erase f ⊕ erase g 
erase (f ∙ g)   = erase f ∙ erase g
erase (lam σ t) = lam σ (erase t)

data ErrorTerm {n : ℕ} (Γ : Ctx n) : Set where
  !var     : LDSL → ErrorTerm Γ
  _bad∙_   : ErrorTerm Γ → LDSL → ErrorTerm Γ
  _∙bad_   : ErrorTerm Γ → LDSL → ErrorTerm Γ
  dom      : LDSL → ErrorTerm Γ
  ı∙       : LDSL → ErrorTerm Γ
  lam-expr : LDSL → ErrorTerm Γ

eraseError : ∀ {n : ℕ} {Γ : Ctx n} → ErrorTerm Γ → LDSL
eraseError (!var     x) = x
eraseError (_ bad∙   x) = x
eraseError (ı∙       x) = x
eraseError (_ ∙bad   x) = x
eraseError (dom      x) = x
eraseError (lam-expr x) = x

data Infer {n : ℕ} (Γ : Ctx n) : LDSL → Set where
  yes : (τ : Type) (t : Term Γ τ) → Infer Γ (erase t)
  no  : (b : ErrorTerm Γ) → Infer Γ (eraseError b)

infer : ∀ {n : ℕ} (Γ : Ctx n) (e : LDSL) → Infer Γ e
infer Γ (lit v) = yes ı (lit v)

infer {n} Γ (var v)     with fromℕ n v 
infer {n} Γ (var .(n + m)) | outside m = no (!var (var (n + m)))
infer {n} Γ (var .(toℕ v)) | inside v = yes (lookup v Γ) (var v refl)

-- infer Γ (e₁ ⊕ e₂)                             with infer Γ e₁ | infer Γ e₂
-- infer Γ (.(eraseError b) ⊕ e₂)              | no b            | _    = no (b bad∙ ((eraseError b) ⊕ e₂))
-- infer Γ (.(erase t )     ⊕ e₂)              | yes ı t         | _    = no (ı∙ ((erase t) ⊕ e₂))
-- infer Γ (.(erase t )     ⊕ .(eraseError b)) | yes (σ  ⇒ τ) t  | no b = no (b ∙bad ((erase t) ⊕ (eraseError b)))
-- infer Γ (.(erase t₁)     ⊕ .(erase t₂))     | yes (σ  ⇒ τ) t₁ | yes  σ' t₂   with σ ≟ σ'
-- infer Γ (.(erase t₁)     ⊕ .(erase t₂))     | yes (σ' ⇒ τ) t₁ | yes .σ' t₂ | yes refl = yes τ (t₁ ⊕ t₂)
-- infer Γ (.(erase t₁)     ⊕ .(erase t₂))     | yes (σ  ⇒ τ) t₁ | yes  σ' t₂ | no x     = no (dom ((erase t₁) ⊕ (erase t₂)) )

infer Γ (e1 ∙ e₂)                             with infer Γ e1 | infer Γ e₂
infer Γ (.(eraseError b) ∙ e₂)              | no b            | _    = no (b bad∙ ((eraseError b) ∙ e₂))
infer Γ (.(erase t )     ∙ e₂)              | yes ı t         | _    = no (ı∙ ((erase t) ∙ e₂))
infer Γ (.(erase t )     ∙ .(eraseError b)) | yes (σ  ⇒ τ) t  | no b = no (b ∙bad ((erase t) ∙ (eraseError b)))
infer Γ (.(erase t₁)     ∙ .(erase t₂))     | yes (σ  ⇒ τ) t₁ | yes  σ' t₂   with σ ≟ σ'
infer Γ (.(erase t₁)     ∙ .(erase t₂))     | yes (σ' ⇒ τ) t₁ | yes .σ' t₂ | yes refl = yes τ (t₁ ∙ t₂)
infer Γ (.(erase t₁)     ∙ .(erase t₂))     | yes (σ  ⇒ τ) t₁ | yes  σ' t₂ | no x     = no (dom ((erase t₁) ∙ (erase t₂)) )

infer Γ (lam σ e)                 with infer (σ ∷ Γ) e
infer Γ (lam σ .(erase t))      | yes τ t = yes (σ ⇒ τ) (lam σ t)
infer Γ (lam σ .(eraseError b)) | no b = no (lam-expr (lam σ (eraseError b)))

infix 30 _[_]
_[_] : ∀ {n : ℕ} {Γ : Ctx n} {τ : Type} → Env Γ → Term Γ τ → ⟦ τ ⟧
env [ var v refl ] = lookupEnv v env 
env [ lit n ] = n 
-- env [ t ⊕ u ] = env [ t ] + env [ u ]
env [ t ∙ u ] = (env [ t ]) (env [ u ])
env [ lam _ t ] = λ x → (x ∷ env) [ t ]

record Opt {n : ℕ} {Γ : Ctx n} {σ : Type} (t : Term Γ σ) : Set where 
  constructor opt 
  field 
    optimised : Term Γ σ
    sound     : ∀ {env} → env [ t ] ≡ env [ optimised ]

ccata : ∀ {n : ℕ} {Γ : Ctx n} {τ : Type} (t : Term Γ τ) → Opt t 
ccata (var v p) = opt (var v p) refl 
ccata (lit x)   = opt (lit x)   refl 
ccata (f ∙ g) with ccata f  | ccata g
...              | opt f' p | opt g' q = opt (f' ∙ g') (cong₂ _$_ p q)
ccata (lam σ τ) with ccata τ
...                | opt t' p = opt (lam σ t') (fun_ext p)
