{-# OPTIONS --guardedness #-}

{-
  Equi-expressiveness between extended QLTL and its extended positive normal form PNF.
  The translation function is defined as ^ and split into two definitions ^ and ^¬
  to show to Agda that the procedure terminates in a finite number of steps.
-}
module PNF.Relational.Conversion where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function using (_∘_)
open import Relation.Nullary.Negation using (¬∃⟶∀¬)

open import Axiom.DoubleNegationElimination using (em⇒dne)

open import Predicates
open import PNF.Negation
open import PNF.Relational.Counterpart
open import PNF.Relational.QLTL renaming (_,_⊨_ to _,_⊨QLTL_)
open import PNF.Relational.PNF renaming (_,_⊨_ to _,_⊨PNF_)

-- Iff between satisfiability in QLTL and PNF for two formulas
_≣_ : ∀ {n} → QLTL n → PNF n → Set₁
ϕ₁ ≣ ϕ₂ = ∀ {A} {σ : CounterpartTrace A} {μ} → (σ , μ ⊨QLTL ϕ₁ → σ , μ ⊨PNF ϕ₂) × (σ , μ ⊨PNF ϕ₂ → σ , μ ⊨QLTL ϕ₁)

interleaved mutual

  ^¬ : ∀ {n} → QLTL n → PNF n
  ^  : ∀ {n} → QLTL n → PNF n

  -- Translation function with no negation
  ^ true      = true
  ^ (x == y)  = x == y
  ^ (! ϕ)     = ^¬ ϕ
  ^ (∃<> ϕ)   = ∃<> ^ ϕ
  ^ (◯ ϕ)     = ◯ ^ ϕ
  ^ (ϕ₁ ∨ ϕ₂) = ^ ϕ₁ ∨ ^ ϕ₂
  ^ (ϕ₁ U ϕ₂) = ^ ϕ₁ U ^ ϕ₂
  ^ (ϕ₁ W ϕ₂) = ^ ϕ₁ W ^ ϕ₂

  -- Translation function implicitly carrying a negation
  ^¬ true      = false
  ^¬ (x == y)  = x != y
  ^¬ (! ϕ)     = ^ ϕ
  ^¬ (∃<> ϕ)   = ∀<> (^¬ ϕ)
  ^¬ (◯ ϕ)     = A (^¬ ϕ)
  ^¬ (ϕ₁ ∨ ϕ₂) = ^¬ ϕ₁ ∧ ^¬ ϕ₂
  ^¬ (ϕ₁ U ϕ₂) = (^¬ ϕ₂) T (^¬ ϕ₁ ∧ ^¬ ϕ₂)
  ^¬ (ϕ₁ W ϕ₂) = (^¬ ϕ₂) F (^¬ ϕ₁ ∧ ^¬ ϕ₂)

interleaved mutual

  -- Main theorems:
  -- Given a QLTL formula ϕ, ^ ϕ in PNF is equisatisfiable with the original formula ϕ.
  ^-equivalence : ∀ {n} (ϕ : QLTL n) →     ϕ ≣ ^ ϕ
  -- Dually, ^¬ ϕ in PNF is equisatisfiable with the negation of the original formula.
  ^¬-negation   : ∀ {n} (ϕ : QLTL n) → (! ϕ) ≣ ^¬ ϕ

  -- The proofs are similar to QLTL.Negation and PNF.Negation; however, here
  -- we need to apply the inductive hypotheses on subformulas, and reusing the previously
  -- shown theorem becomes non-trivial.

  -- Show that ^ produces an equivalent formula:
  ^-equivalence (! ϕ) = ^¬-negation ϕ
  ^-equivalence true = (λ x → tt) , (λ x → tt)
  ^-equivalence (x == y) = (λ z → z) , λ z → z
  ^-equivalence (ϕ₁ ∨ ϕ₂) = [ inj₁ ∘ proj₁ (^-equivalence ϕ₁) , inj₂ ∘ proj₁ (^-equivalence ϕ₂) ]
                          , [ inj₁ ∘ proj₂ (^-equivalence ϕ₁) , inj₂ ∘ proj₂ (^-equivalence ϕ₂) ]
  ^-equivalence (∃<> ϕ) = (λ (s , p) → s , proj₁ (^-equivalence ϕ) p)
                        , (λ (s , p) → s , proj₂ (^-equivalence ϕ) p)
  ^-equivalence (◯ ϕ) {σ = σ} {μ = μ} = imply∃ (proj₁ (^-equivalence ϕ))
                                      , imply∃ (proj₂ (^-equivalence ϕ))
  ^-equivalence (ϕ₁ U ϕ₂) {σ = σ} {μ = μ} = congUntil (imply∃ (proj₁ (^-equivalence _)))
                                                      (imply∃ (proj₁ (^-equivalence _)))
                                          , congUntil (imply∃ (proj₂ (^-equivalence _)))
                                                      (imply∃ (proj₂ (^-equivalence _)))
  ^-equivalence (ϕ₁ W ϕ₂)  {σ = σ} {μ = μ} = congWeakUntil (imply∃ (proj₁ (^-equivalence _)))
                                                           (imply∃ (proj₁ (^-equivalence _)))
                                           , congWeakUntil (imply∃ (proj₂ (^-equivalence _)))
                                                           (imply∃ (proj₂ (^-equivalence _)))

  -- Show that ^¬ negates the formula:
  ^¬-negation true = (λ x → x tt) , (λ x x₁ → x)
  ^¬-negation (x == y) = (λ x → x) , (λ x → x)
  ^¬-negation (! ϕ) {σ = σ} {μ = μ} with ^-equivalence ϕ {σ = σ} {μ = μ}
  ... | ⇒ , ⇐ = (λ x → ⇒ (em⇒dne LEM x)) , (λ x → λ z → z (⇐ x)) -- Go back to standard equivalence using DNE
  ^¬-negation (◯ ϕ) {σ = σ} {μ = μ} = (λ x → imply∀ (proj₁ (^¬-negation _)) (¬∃C⟶∀C¬ x))
                                    , (λ x → ¬∃C←∀C¬ (imply∀ (proj₂ (^¬-negation _)) x))
  ^¬-negation (ϕ₁ U ϕ₂) {σ = σ} {μ = μ} =
        (λ x → congWeakUntil (λ {i} → imply∀ (proj₁ (^¬-negation ϕ₂)) ∘ (¬∃C⟶∀C¬))
                            (λ {i} (p1 , p2) → ∀→∩ (imply∀ (proj₁ (^¬-negation ϕ₁)) (¬∃C⟶∀C¬ p1))
                                                                            (imply∀ (proj₁ (^¬-negation ϕ₂)) (¬∃C⟶∀C¬ p2)))
                            (¬until→weakUntil x))
    ,  (λ x → ¬until←weakUntil (congWeakUntil (λ {i} → ¬∃C←∀C¬ ∘ imply∀ (proj₂ (^¬-negation ϕ₂)))
                                                (λ {i} x → let a , b = (∀←∩ x) in
                                                    (¬∃C←∀C¬ (imply∀ (proj₂ (^¬-negation ϕ₁)) a))
                                                  , (¬∃C←∀C¬ (imply∀ (proj₂ (^¬-negation ϕ₂)) b)))
                                                x))
  ^¬-negation (ϕ₁ W ϕ₂) {σ = σ} {μ = μ} =
        (λ x → congUntil (λ {i} → imply∀ (proj₁ (^¬-negation ϕ₂)) ∘ (¬∃C⟶∀C¬))
                            (λ {i} (p1 , p2) → ∀→∩ (imply∀ (proj₁ (^¬-negation ϕ₁)) (¬∃C⟶∀C¬ p1))
                                                                            (imply∀ (proj₁ (^¬-negation ϕ₂)) (¬∃C⟶∀C¬ p2)))
                            (¬weakUntil→until x))
      , (λ x → ¬weakUntil←until (congUntil (λ {i} → ¬∃C←∀C¬ ∘ imply∀ (proj₂ (^¬-negation ϕ₂)))
                                                (λ {i} x → let a , b = (∀←∩ x) in
                                                    (¬∃C←∀C¬ (imply∀ (proj₂ (^¬-negation ϕ₁)) a))
                                                  , (¬∃C←∀C¬ (imply∀ (proj₂ (^¬-negation ϕ₂)) b)))
                                                x))
  ^¬-negation (ϕ₁ ∨ ϕ₂) = (λ x → let a , b = ¬⊎→¬×¬ x in proj₁ (^¬-negation ϕ₁) a , proj₁ (^¬-negation ϕ₂) b)
                        , λ { (a , b) (inj₁ x) → proj₂ (^¬-negation ϕ₁) a x
                            ; (a , b) (inj₂ y) → proj₂ (^¬-negation ϕ₂) b y
                            }
  ^¬-negation (∃<> ϕ) = (λ x → λ i → proj₁ (^¬-negation ϕ) ((¬∃⟶∀¬ x) i))
                      , (λ x → λ (a , b) → (proj₂ (^¬-negation ϕ)) (x a) b)
