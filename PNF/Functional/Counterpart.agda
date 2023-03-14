{-# OPTIONS --guardedness #-}

{-
  Base definitions for counterpart-based semantics: models, traces, theorems and properties used in the main theorems relating semantics and negations.
-}
module PNF.Functional.Counterpart where

open import Data.Empty
open import Data.Maybe
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Induction
open import Data.Product using (_,_; _×_)
open import Data.Fin
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit
open import Relation.Unary
open import Relation.Binary.PropositionalEquality using (_≡_; trans; subst; refl; sym)
open import Relation.Nullary

-- For simplicity, we do not consider models in full, and directly work with counterpart traces.
-- Each trace defines autonomously the set of Assignment it works on pointwise.
record CounterpartTrace (A : Set) : Set₁ where
  coinductive
  field
    {B}  : Set
    rel  : A → Maybe B
    tail : CounterpartTrace B

open CounterpartTrace public

-- World of the trace after i steps
wi : ∀ {A : Set} → ℕ → CounterpartTrace A → Set
wi {A} zero T = A
wi (suc n) T = wi n (tail T)

-- Suffix of a trace
s : ∀ {A} → (n : ℕ) → (σ : CounterpartTrace A) → CounterpartTrace (wi n σ)
s zero T = T
s (suc n) T = s n (tail T)

-- Kleisli composition of partial functions
_>=>_ : ∀ {A B C : Set} → (A → Maybe B) → (B → Maybe C) → A → Maybe C
_>=>_ f g = λ x → f x >>= g

-- Composition of the first i counterpart relations
C≤ : ∀ {A} → (n : ℕ) → (σ : CounterpartTrace A) → A → Maybe (wi n σ)
C≤ zero σ = just
C≤ (suc n) σ = rel σ >=> C≤ n (tail σ)

-- Applicative-like definition combining two partial functions into into their product
<*,*> : ∀ {A B C D : Set} → (A → Maybe C) → (B → Maybe D) → (A × B) → Maybe (C × D)
<*,*> f g (a , b) with f a | g b
... | just x | just y = just (x , y)
... | _ | _ = nothing

-- First monad law with just as unit
monad-law1 : ∀ {A B} {f : A → Maybe B} x
           → (f >=> just) x ≡ f x
monad-law1 {f = f} x with f x
... | just x₁ = refl
... | nothing = refl

-- Associativity of Kleisli composition
monad-law2 : ∀ {A B C D} {f : A → Maybe B} {g : B → Maybe C} {h : C → Maybe D} x
           → ((f >=> g) >=> h) x ≡ (f >=> (g >=> h)) x
monad-law2 {f = f} x with f x
... | just x₁ = refl
... | nothing = refl

-- Assignment for a given set A with n variables, simply defined as the cartesian product
Assignment : ℕ → Set → Set
Assignment zero A = ⊤
Assignment (suc n) A = A × Assignment n A

-- Lookup function for an assignment with n variables
_[_] : ∀ {A n} → Assignment n A → (i : Fin n) → A
(x , μ) [ zero  ] = x
(x , μ) [ suc i ] = μ [ i ]

-- Lifting of a counterpart function to assignments
↑ : ∀ {n} {A B : Set} → (A → Maybe B) → Assignment n A → Maybe (Assignment n B)
↑ {n = zero} f = λ { tt → just tt }
↑ {n = suc n} f = <*,*> f (↑ f)

-- Extensionality-like property for the product of partial functions
<*,*>-ext : ∀ {A B C D} {f f′ : A → Maybe B} {g g′ : C → Maybe D} {x e}
          → (∀ {x} → f x ≡ f′ x)
          → (∀ {x} → g x ≡ g′ x)
          → <*,*> f g (x , e)
          ≡ <*,*> f′ g′ (x , e)
<*,*>-ext {f = f} {g = g} {x = x} {e = e} eq1 eq2 rewrite eq1 {x} | eq2 {e} = refl

-- <*,*> distributes over the Kleisli composition of arrows
<*,*>-dec : ∀ {A B C D E F} {f : A → Maybe B} {f′ : B → Maybe C} {g : D → Maybe E} {g′ : E → Maybe F} {x e}
          → (<*,*> (f >=> f′) (g >=> g′)) (x , e)
          ≡ (<*,*> f g >=> <*,*> f′ g′) (x , e)
<*,*>-dec {f = f} {f′ = f′} {g = g} {g′ = g′} {x = x} {e = e} with f x | g e
... | nothing | just x₁ = refl
... | nothing | nothing = refl
... | just x₁ | nothing with f′ x₁
... | just x₂ = refl
... | nothing = refl
<*,*>-dec {f = f} {f′ = f′} {g = g} {g′ = g′} {x = x} {e = e} | just x₁ | just x₂ with f′ x₁ | g′ x₂
... | just x₃ | just x₄ = refl
... | just x₃ | nothing = refl
... | nothing | just x₃ = refl
... | nothing | nothing = refl

-- The lifting ↑ behaves homomorphically with respect to Kleisli composition
↑-homomorphism : ∀ {A B C} {f : A → Maybe B} {g : B → Maybe C} {n} (μ : Assignment n A)
              → ↑ (f >=> g) μ ≡ (↑ f >=> ↑ g) μ
↑-homomorphism {n = zero} μ = refl
↑-homomorphism {f = f} {g = g} {n = suc n} (x , e)
   rewrite <*,*>-ext {f = f >=> g} {g = (↑ (f >=> g))} {x = x} {e = e} refl λ {x} → (↑-homomorphism {f = f} {g = g} {n = n} x)
   rewrite <*,*>-dec {f = f} {f′ = g} {g = ↑ f} {g′ = ↑ g} {x = x} {e = e}
     with f x | ↑ f e
... | just x₁ | nothing = refl
... | nothing | just x₁ = refl
... | nothing | nothing = refl
... | just x₁ | just x₂ with g x₁ | ↑ g x₂
... | just x₃ | just x₄ = refl
... | just x₃ | nothing = refl
... | nothing | just x₃ = refl
... | nothing | nothing = refl

-- Extensionality for lifted partial functions
↑-ext-cong : ∀ {n} {A B : Set} {f g : A → Maybe B} {μ : Assignment n A}
           → (∀ x → f x ≡ g x)
           → ↑ f μ ≡ ↑ g μ
↑-ext-cong {zero} x = refl
↑-ext-cong {suc n} {μ = a , b} x rewrite ↑-ext-cong {μ = b} x | x a = refl

-- Lifting the monadic unit corresponds to the unit
lift-unit : ∀ {n} {A : Set} {μ : Assignment n A}
          → ↑ just μ ≡ just μ
lift-unit {zero} {μ = tt} = refl
lift-unit {suc n} {μ = a , μ} rewrite lift-unit {n} {μ = μ} = refl

-- If a counterpart exists after one step, taking the tail of a trace and advancing it is equivalent
switch-tail-suc : ∀ {k} {A} {σ : CounterpartTrace A} {n} {μ : Assignment k _} {μ′}
    → ↑ (C≤ 1 σ) μ ≡ just μ′
    → ↑ (C≤ n (tail σ)) μ′
    ≡ ↑ (C≤ (suc n) σ) μ
switch-tail-suc {_} {_} {σ} {n} {μ} eq rewrite ↑-ext-cong {μ = μ} (monad-law1 {f = rel σ})
                      | ↑-homomorphism {f = rel σ} {g = C≤ n (tail σ)} μ
                      | eq = refl

-- If a counterpart does not exist after 1 step, it does not exist for any n>=1
del-counterparts : ∀ {k} {A} {σ : CounterpartTrace A} {n} {μ : Assignment k _}
    → ↑ (C≤ 1 σ) μ ≡ nothing
    → ↑ (C≤ (suc n) σ) μ ≡ nothing
del-counterparts {_} {_} {σ} {n} {μ} eq rewrite ↑-ext-cong {μ = μ} (monad-law1 {f = rel σ})
                    | ↑-homomorphism {f = rel σ} {g = C≤ n (tail σ)} μ
                    | eq = refl

-- Lifting a predicate to Maybe A universally: either a counterpart is absent or A holds on it
∀C∈_⇒_ : ∀ {A : Set} → Maybe A → (A → Set) → Set
∀C∈ nothing ⇒ P = ⊤
∀C∈ just x ⇒ P = P x

-- Lifting a predicate to Maybe A existentially: a counterpart exists and A holds on it
∃C∈_⇒_ : ∀ {A : Set} → Maybe A → (A → Set) → Set
∃C∈ nothing ⇒ P = ⊥
∃C∈ just x ⇒ P = P x

-- Negation of existential and universal liftings for counterparts
¬∃C←∀C¬ : ∀ {A : Set} → {P : A → Set} → {x : Maybe A} → ∀C∈ x ⇒ (λ x → ¬ P x) → ¬ (∃C∈ x ⇒ P)
¬∃C←∀C¬ {x = nothing} e = λ z → z
¬∃C←∀C¬ {x = just x} e = e

¬∀C←∃C¬ : ∀ {A : Set} → {P : A → Set} → {x : Maybe A} → ∃C∈ x ⇒ (λ x → ¬ P x) → ¬ (∀C∈ x ⇒ P)
¬∀C←∃C¬ {x = nothing} e = λ _ → e
¬∀C←∃C¬ {x = just x} e = e

¬∃C→∀C¬ : ∀ {A : Set} → {P : A → Set} → {x : Maybe A} → ¬ (∃C∈ x ⇒ P) → ∀C∈ x ⇒ (λ x → ¬ P x)
¬∃C→∀C¬ {x = nothing} e = tt
¬∃C→∀C¬ {x = just x} e = e

¬∀C→∃C¬ : ∀ {A : Set} → {P : A → Set} → {x : Maybe A} → ¬ (∀C∈ x ⇒ P) → ∃C∈ x ⇒ (λ x → ¬ P x)
¬∀C→∃C¬ {x = nothing} e = e tt
¬∀C→∃C¬ {x = just x} e = e

∀→∩ : ∀ {S : Set} → {A B : S → Set} → {x : Maybe S} → (∀C∈ x ⇒ A) → (∀C∈ x ⇒ B) → (∀C∈ x ⇒ (A ∩ B))
∀→∩ {x = just x} = _,_
∀→∩ {x = nothing} = λ _ _ → tt

conjunct∃ : ∀ {S : Set} → {A B : S → Set} → {x : Maybe S} → (∃C∈ x ⇒ A) → (∃C∈ x ⇒ B) → (∃C∈ x ⇒ (λ x → A x × B x))
conjunct∃ {x = just x} = _,_
conjunct∃ {x = nothing} = λ _ z → z

∀←∩ : ∀ {S : Set} → {A B : S → Set} → {x : Maybe S} → (∀C∈ x ⇒ (A ∩ B)) → (∀C∈ x ⇒ A) × (∀C∈ x ⇒ B)
∀←∩ {x = just x} = λ z → z
∀←∩ {x = nothing} = λ _ → tt , tt

∃→∩ : ∀ {S : Set} → {A B : S → Set} → {x : Maybe S} → (∃C∈ x ⇒ (A ∩ B)) → (∃C∈ x ⇒ A) × (∃C∈ x ⇒ B)
∃→∩ {x = just x} = λ z → z
∃→∩ {x = nothing} = λ z → z , z

-- Pointwise-implication for universal and existential lifting of predicates
imply∀ : ∀ {S : Set} → {A B : S → Set} → {x : Maybe S} → A ⊆ B → (∀C∈ x ⇒ A) → (∀C∈ x ⇒ B)
imply∀ {x = just x} = λ z → z
imply∀ {x = nothing} = λ _ _ → tt

imply∃ : ∀ {S : Set} → {A B : S → Set} → {x : Maybe S} → A ⊆ B → (∃C∈ x ⇒ A) → (∃C∈ x ⇒ B)
imply∃ {x = just x} = λ z → z
imply∃ {x = nothing} = λ _ z → z

-- Lifting actual existing counterparts into their existential and universal prediates
lift-exists : ∀ {n} {A} {μ : Assignment n A} {P}
     → P μ
     → ∃C∈ ↑ just μ ⇒ P
lift-exists {μ = μ} x rewrite lift-unit {μ = μ} = x

lift-exists′ : ∀ {n} {A} {μ : Assignment n A} {P}
     → ∃C∈ ↑ just μ ⇒ P
     → P μ
lift-exists′ {μ = μ} x rewrite lift-unit {μ = μ} = x

lift-forall : ∀ {n} {A} {μ : Assignment n A} {P}
     → P μ
     → ∀C∈ ↑ just μ ⇒ P
lift-forall {μ = μ} x rewrite lift-unit {μ = μ} = x

-- If a counterpart does not exist then P is universally always satisfied
lift-nothing : ∀ {A} {P : A → Set}
             → ∀C∈ nothing ⇒ P
lift-nothing = tt
