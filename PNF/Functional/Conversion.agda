{-# OPTIONS --guardedness #-}

{-
  Equi-expressiveness between extended QLTL and its extended positive normal form PNF.
  The translation function is defined as ^ and split into two definitions ^ and ^¬
  to show to Agda that the procedure terminates in a finite number of steps.
-}
module PNF.Functional.Conversion where

open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function using (_∘_)
open import Relation.Nullary.Negation using (¬∃⟶∀¬)

open import Axiom.DoubleNegationElimination using (em⇒dne)

open import Predicates
open import PNF.Negation
open import PNF.Functional.Counterpart
open import PNF.Functional.QLTL renaming (_,_⊨_ to _,_⊨QLTL_)
open import PNF.Functional.PNF renaming (_,_⊨_ to _,_⊨PNF_)

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
  ^-equivalence (◯ ϕ) {σ = σ} {μ = μ} = (λ x → imply∃ {x = ↑ (C≤ 1 σ) μ} (proj₁ (^-equivalence ϕ)) x)
                                      , (λ x → imply∃ {x = ↑ (C≤ 1 σ) μ} (proj₂ (^-equivalence ϕ)) x)
  ^-equivalence (ϕ₁ U ϕ₂) {σ = σ} {μ = μ} = congUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₁ (^-equivalence ϕ₁)))
                                                      (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₁ (^-equivalence ϕ₂)))
                                          , congUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₂ (^-equivalence ϕ₁)))
                                                      (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₂ (^-equivalence ϕ₂)))
  ^-equivalence (ϕ₁ W ϕ₂)  {σ = σ} {μ = μ} = congWeakUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₁ (^-equivalence ϕ₁)))
                                                           (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₁ (^-equivalence ϕ₂)))
                                           , congWeakUntil (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₂ (^-equivalence ϕ₁)))
                                                           (λ {i} → imply∃ {x = ↑ (C≤ i σ) μ} (proj₂ (^-equivalence ϕ₂)))

  -- Show that ^¬ negates the formula:
  ^¬-negation true = (λ x → x tt) , (λ x x₁ → x)
  ^¬-negation (x == y) = (λ x → x) , (λ x → x)
  ^¬-negation (! ϕ) {σ = σ} {μ = μ} with ^-equivalence ϕ {σ = σ} {μ = μ}
  ... | ⇒ , ⇐ = (λ x → ⇒ (em⇒dne LEM x)) , (λ x → λ z → z (⇐ x)) -- Go back to standard equivalence using DNE
  ^¬-negation (ϕ₁ U ϕ₂) {σ = σ} {μ = μ} =
        (λ x → congWeakUntil (λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₂)) ∘ (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ}))
                            (λ {i} (p1 , p2) → ∀→∩ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₁)) (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p1))
                                                                            (imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₂)) (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p2)))
                            (¬until→weakUntil x))
    ,  (λ x → ¬until←weakUntil (congWeakUntil (λ {i} → ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} ∘ imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₂)))
                                                (λ {i} x → let a , b = (∀←∩ {x = ↑ (C≤ i σ) μ} x) in
                                                    (¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₁)) a))
                                                  , (¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₂)) b)))
                                                x))
  ^¬-negation (ϕ₁ W ϕ₂) {σ = σ} {μ = μ} =
        (λ x → congUntil (λ {i} → imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₂)) ∘ (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ}))
                            (λ {i} (p1 , p2) → ∀→∩ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₁)) (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p1))
                                                                            (imply∀ {x = ↑ (C≤ i σ) μ} (proj₁ (^¬-negation ϕ₂)) (¬∃C→∀C¬ {x = ↑ (C≤ i σ) μ} p2)))
                            (¬weakUntil→until x))
      , (λ x → ¬weakUntil←until (congUntil (λ {i} → ¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} ∘ imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₂)))
                                                (λ {i} x → let a , b = (∀←∩ {x = ↑ (C≤ i σ) μ} x) in
                                                    (¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₁)) a))
                                                  , (¬∃C←∀C¬ {x = ↑ (C≤ i σ) μ} (imply∀ {x = ↑ (C≤ i σ) μ} (proj₂ (^¬-negation ϕ₂)) b)))
                                                x))
  ^¬-negation (ϕ₁ ∨ ϕ₂) = (λ x → let a , b = ¬⊎→¬×¬ x in proj₁ (^¬-negation ϕ₁) a , proj₁ (^¬-negation ϕ₂) b)
                        , λ { (a , b) (inj₁ x) → proj₂ (^¬-negation ϕ₁) a x
                            ; (a , b) (inj₂ y) → proj₂ (^¬-negation ϕ₂) b y
                            }
  ^¬-negation (∃<> ϕ) = (λ x → λ i → proj₁ (^¬-negation ϕ) ((¬∃⟶∀¬ x) i))
                      , (λ x → λ (a , b) → (proj₂ (^¬-negation ϕ)) (x a) b)
  ^¬-negation (◯ ϕ){σ = σ} {μ = μ} = (imply∀ {x = ↑ (C≤ 1 σ) μ} (proj₁ (^¬-negation ϕ)) ∘ (¬∃C→∀C¬ {x = ↑ (C≤ 1 σ) μ}))
                                    , ((¬∃C←∀C¬ {x = ↑ (C≤ 1 σ) μ}) ∘ (imply∀ {x = ↑ (C≤ 1 σ) μ} (proj₂ (^¬-negation ϕ))))
