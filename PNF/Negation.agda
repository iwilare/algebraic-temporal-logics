{-# OPTIONS --guardedness #-}

{-
  Classical notions of negation for the predicates of LTL, and classical negations for connectives.
-}
module PNF.Negation where

open import Axiom.DoubleNegationElimination using (em⇒dne)
open import Axiom.ExcludedMiddle
open import Axiom.Extensionality.Propositional
open import Data.Empty
open import Data.Fin using (Fin)
open import Data.Maybe
open import Data.Nat using (ℕ; _∸_; _+_; _<_; _≤_; suc; zero; _<′_; _<‴_; _≤‴_)
open import Data.Nat.Induction
open import Data.Nat.Properties using (≤⇒≤′; ≤⇒≤‴; <-transˡ; <-trans; <⇒≤; <-cmp; ≤-<-connex)
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≤_)
open import Function using (_∘_)
open import Function using (id)
open import Level using (0ℓ; Level)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary
open import Relation.Nullary.Negation using (¬∃⟶∀¬; contraposition)
open import Relation.Unary renaming (∁ to ¬′; _∩_ to _∧′_)

open import Predicates

private
  variable
    ℓ : Level

-- Postulate classical principles
postulate
  LEM : ExcludedMiddle ℓ

-- Classical reasoning on conjunction and disjunction
¬×→¬⊎¬ : ∀ {A B : Set ℓ} → ¬ (A × B) → (¬ A ⊎ ¬ B)
¬×→¬⊎¬ {ℓ} {A} neg with LEM {ℓ} {A}
... | yes p = inj₂ λ x → neg (p , x)
... | no ¬p = inj₁ ¬p

-- Classical reasoning on conjunction and disjunction
¬×←¬⊎¬ : ∀ {A B : Set ℓ} → (¬ A ⊎ ¬ B) → ¬ (A × B)
¬×←¬⊎¬ {ℓ} {A} (inj₁ x) = λ z → x (proj₁ z)
¬×←¬⊎¬ {ℓ} {A} (inj₂ y) = λ z → y (proj₂ z)

¬⊎→¬×¬ : ∀ {A B : Set ℓ} → ¬ (A ⊎ B) → (¬ A × ¬ B)
¬⊎→¬×¬ {ℓ} {A} neg with LEM {ℓ} {A}
... | yes p = (λ x → neg (inj₁ x)) , (λ x → neg (inj₁ p))
... | no ¬p = ¬p , (λ x → neg (inj₂ x))

-- Classical reasoning on existential and universal quantification
¬∀¬⟶∃ : ∀ {A : Set ℓ} {P : A → Set ℓ} → ¬ (∀ x → ¬ P x) → (∃[ n ] P n)
¬∀¬⟶∃ x = em⇒dne LEM λ z → x (λ x z₁ → z (x , z₁))

¬∀⟶∃¬ : ∀ {A : Set ℓ} {P : A → Set ℓ} → ¬ (∀ x → P x) → (∃[ n ] ¬ P n)
¬∀⟶∃¬ {P = P} x = ¬∀¬⟶∃ {P = λ x → ¬ P x} λ x₁ → x λ x₂ → em⇒dne LEM (x₁ x₂)

open import Relation.Nullary.Negation using (¬∃⟶∀¬) public

-- Alternative form for the negation of until: whenever A before n, then not B
_¬untilLeft_ : ∀ (A B : ℕ → Set) → Set
A ¬untilLeft B = ∀ n → (A before n → B n)

_¬weakUntilLeft_ : ∀ (A B : ℕ → Set) → Set
A ¬weakUntilLeft B = A ¬untilLeft B × eventually A

-- The negation of until can be expressed as untilLeft with B negated
u¬ul : ∀ {A B} → ¬ A until B → A ¬untilLeft (¬′ B)
u¬ul nu = λ i → [ (λ x → λ z _ → x z) , (λ x → λ _ → x) ] (¬×→¬⊎¬ ((¬∃⟶∀¬ nu) i))

-- The negation of weak until can be expressed as untilLeft with B negated along with eventually not A
wu¬wul : ∀ {A B} → ¬ A weakUntil B → A ¬untilLeft (¬′ B) × eventually (¬′ A)
wu¬wul nu = < (λ x → u¬ul (proj₁ x)) , (λ x → ¬∀⟶∃¬ (proj₂ x)) > (¬⊎→¬×¬ nu)

-- Either there exists a point where A does not hold or A always holds
strong-prefix-lem : ∀ {A} → A until (¬′ A) ⊎ always A
strong-prefix-lem {A} with LEM {P = A until (¬′ A)}
... | yes y = inj₁ y
... | no n = inj₂ (λ i → wf-induction-always-A i (<′-wellFounded i))
    where
      wf-induction-always-A : ∀ i → Acc _<′_ i → A i
      wf-induction-always-A i (acc rs) =
        em⇒dne LEM (u¬ul n i (λ i′ i′<i → wf-induction-always-A i′ (rs i′ (≤⇒≤′ i′<i))))

-- Classical negations of until and weak until

¬until→weakUntil : ∀ {A B} → ¬ A until B → (¬′ B) weakUntil (¬′ A ∧′ ¬′ B)
¬until→weakUntil {A} nu =
    [ (λ (n , Ai<n , !An) →
      inj₁ (n ,
            (λ k k<n → u¬ul nu k λ i i<k → Ai<n i (<-trans i<k k<n))
            , !An , u¬ul nu n λ i i<k → Ai<n i i<k))
    , (λ Ai → inj₂ λ i x → u¬ul nu i (λ k k<i → Ai k) x)
    ]′ (strong-prefix-lem {A})

¬weakUntil→until : ∀ {A B} → ¬ A weakUntil B → (¬′ B) until (¬′ A ∧′ ¬′ B)
¬weakUntil→until {A} nu with wu¬wul nu
... | then , (n , !An) with strong-prefix-lem {A}
... | inj₁ (n , Ai<n , !An) =
       n , (λ k k<n → then k λ i i<k → Ai<n i (<-trans i<k k<n)) , !An , then n Ai<n
... | inj₂ Ai = ⊥-elim (!An (Ai n))

¬until←weakUntil : ∀ {ℓ} {A B : Pred _ ℓ} → (¬′ B) weakUntil (¬′ A ∧′ ¬′ B) → ¬ A until B
¬until←weakUntil (inj₁ (m , !Bi<m , !Am , !Bm)) (n , Ai<n , Bn) with <-cmp m n
... | tri< m<n _ _ = !Am (Ai<n m m<n)
... | tri≈ _ refl _ = !Bm Bn
... | tri> _ _ n<m = !Bi<m n n<m Bn
¬until←weakUntil (inj₂ !Bi) (n , Ai<n , Bn) = !Bi n Bn

¬weakUntil←until : ∀ {ℓ} {A B : Pred _ ℓ} → (¬′ B) until (¬′ A ∧′ ¬′ B) → ¬ A weakUntil B
¬weakUntil←until (n , !Bi<n , !An , !Bn) (inj₁ (m , Ai<m , Bm)) with <-cmp m n
... | tri< m<n _ _ = !Bi<n m m<n Bm
... | tri≈ _ refl _ = !Bn Bm
... | tri> _ _ n<m = !An (Ai<m n n<m)
¬weakUntil←until (n , !Bi<n , !An , !Bn) (inj₂ Ai) = !An (Ai n)
