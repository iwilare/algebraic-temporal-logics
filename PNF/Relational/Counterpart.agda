{-# OPTIONS --guardedness #-}

{-
  Base definitions for counterpart-based semantics: models, traces, theorems and properties used in the main theorems relating semantics and negations.
-}
module PNF.Relational.Counterpart {ℓ} where

open import Data.Empty
open import Data.Maybe
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Induction
open import Data.Product using (_,_; _×_; Σ; ∃-syntax; proj₁; proj₂)
open import Data.Fin
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; subst; refl; sym)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Unary
open import Relation.Binary.Construct.Composition using (_;_)
open import Level renaming (suc to sucℓ)
open import Function
open import Data.Vec using (replicate)

open import VecT
open import PNF.Negation

import Data.Unit
open import Data.Unit.Polymorphic using (⊤)

pattern * = lift Data.Unit.tt

Relation : Set ℓ → Set ℓ → Set (sucℓ ℓ)
Relation A B = REL A B ℓ

-- For simplicity, we do not consider models in full, and directly work with counterpart traces.
-- Each trace defines autonomously the set of Assignment it works on pointwise.
record CounterpartTrace (A : Set ℓ) : Set (sucℓ ℓ) where
  coinductive
  field
    {B}  : Set ℓ
    rel  : Relation A B
    tail : CounterpartTrace B

open CounterpartTrace public

-- World of the trace after i steps
wi : ∀ {A} → ℕ → CounterpartTrace A → Set ℓ
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
C≤ : ∀ {A} → (n : ℕ) → (σ : CounterpartTrace A) → Relation A (wi n σ)
C≤ zero σ = _≡_
C≤ (suc n) σ = rel σ ; C≤ n (tail σ)

-- Assignment for a given set A with n variables, simply defined as the cartesian product
Assignment : ℕ → Set ℓ → Set ℓ
Assignment n A = mapT (const A) (replicate {n = n} Data.Unit.tt)

-- Lifting a predicate universally: either a counterpart is absent or A holds on it
∀C∈_⇒_ : ∀ {A : Set ℓ} → (A → Set ℓ) → (A → Set ℓ) → Set ℓ
∀C∈ C ⇒ P = ∀ c → C c → P c

-- Lifting a predicate existentially: a counterpart exists and A holds on it
∃C∈_⇒_ : ∀ {A : Set ℓ} → (A → Set ℓ) → (A → Set ℓ) → Set ℓ
∃C∈ C ⇒ P = ∃[ c ] C c × P c

-- Negation of existential and universal liftings for counterparts
¬∃C⟶∀C¬ : ∀ {A : Set ℓ} → {P Q : A → Set ℓ} → ¬ (∃C∈ P ⇒ Q) → ∀C∈ P ⇒ (∁ Q)
¬∃C⟶∀C¬ x = ¬∃⟶∀¬ ∘ ¬∃⟶∀¬ x

¬∀C⟶∃C¬ : ∀ {A : Set ℓ} → {P Q : A → Set ℓ} → ¬ (∀C∈ P ⇒ Q) → ∃C∈ P ⇒ (∁ Q)
¬∀C⟶∃C¬ x with ¬∀⟶∃¬ x
... | a , b = a , ¬∀⟶∃¬ b

¬∃C←∀C¬ : ∀ {A : Set ℓ} → {P Q : A → Set ℓ} → ∀C∈ P ⇒ (∁ Q) → ¬ (∃C∈ P ⇒ Q)
¬∃C←∀C¬ f (a , b , c) = f a b c

¬∀C←∃C¬ : ∀ {A : Set ℓ} → {P Q : A → Set ℓ} → ∃C∈ P ⇒ (∁ Q) → ¬ (∀C∈ P ⇒ Q)
¬∀C←∃C¬ (a , b , c) f = c (f a b)

-- Conjunction for universal and existential lifting of predicates
∀→∩ : ∀ {A : Set ℓ} → {P A B : A → Set ℓ} → (∀C∈ P ⇒ A) → (∀C∈ P ⇒ B) → (∀C∈ P ⇒ (A ∩ B))
∀→∩ = λ z z₁ c z₂ → z c z₂ , z₁ c z₂

∀←∩ : ∀ {A : Set ℓ} → {P A B : A → Set ℓ} → (∀C∈ P ⇒ (A ∩ B)) → (∀C∈ P ⇒ A) × (∀C∈ P ⇒ B)
∀←∩ = λ x → (λ c z → proj₁ (x c z)) , λ c z → proj₂ (x c z)

∃→∪ : ∀ {A : Set ℓ} → {P A B : A → Set ℓ} → (∃C∈ P ⇒ A) ⊎ (∃C∈ P ⇒ B) → (∃C∈ P ⇒ (A ∪ B))
∃→∪ = λ { (inj₁ (fst , fst₁ , snd)) → fst , fst₁ , inj₁ snd
        ; (inj₂ (fst , fst₁ , snd)) → fst , fst₁ , inj₂ snd }

∃→∩ : ∀ {A : Set ℓ} → {P A B : A → Set ℓ} → (∃C∈ P ⇒ (A ∩ B)) → (∃C∈ P ⇒ A) × (∃C∈ P ⇒ B)
∃→∩ = λ { (fst , fst₁ , fst₂ , snd) → (fst , fst₁ , fst₂) , fst , fst₁ , snd }

imply∃ : ∀ {A : Set ℓ} → {P Q Q′ : A → Set ℓ} → Q ⊆ Q′ → ∃C∈ P ⇒ Q → ∃C∈ P ⇒ Q′
imply∃ x (a , b , c) = a , b , x c

imply∀ : ∀ {A : Set ℓ} → {P Q Q′ : A → Set ℓ} → Q ⊆ Q′ → ∀C∈ P ⇒ Q → ∀C∈ P ⇒ Q′
imply∀ x f = λ a pc → x (f a pc)

-- Properties on zipping
zip-id-right : ∀ {k} {R B} {μ : Assignment k R} {μ′ : Assignment k B} {r}
           → VecT.zip r μ μ′
           → VecT.zip (r ; _≡_) μ μ′
zip-id-right = zip-imply λ x → _ , x , refl

zip-id-right-inv : ∀ {k} {R B} {μ : Assignment k R} {μ′ : Assignment k B} {r}
           → VecT.zip (r ; _≡_) μ μ′
           → VecT.zip r μ μ′
zip-id-right-inv = zip-imply λ { (a , b , refl) → b }

switch-tail-suc : ∀ {A} {σ : CounterpartTrace A} {k} {n} {μ : Assignment k _} {μ′ : Assignment k _} {μ″ : Assignment k _}
    → VecT.zip (C≤ 1 σ)        μ μ′
    → VecT.zip (C≤ n (tail σ)) μ′ μ″
    → VecT.zip (C≤ (suc n) σ)  μ μ″
switch-tail-suc z1 z2 = zip-imply (λ { (fst , (fst₁ , fst₂ , refl) , snd) → fst , fst₂ , snd }) (zip-rel-comp z1 z2)

switch-tail-suc-inv : ∀ {k} {A} {σ : CounterpartTrace A} {n} {μ : Assignment k _} {μ″}
    → VecT.zip (C≤ (suc n) σ)  μ μ″
    → ∃[ μ′ ]
      VecT.zip (C≤ 1 σ)        μ μ′
    × VecT.zip (C≤ n (tail σ)) μ′ μ″
switch-tail-suc-inv z with zip-rel-decomp z
... | a , b , c = a , zip-imply (λ x → _ , x , refl) b , c
