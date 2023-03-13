{-# OPTIONS --sized-types --guardedness #-}

open import SortedAlgebra

module Example where

open import Data.Nat using (zero; suc; _+_)
open import Data.Fin using () renaming (zero to fz; suc to fs)

open import Data.Unit.Polymorphic using (⊤)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Empty using (⊥-elim)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Unary using (_∈_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; isEquivalence; sym; trans; cong; cong-app; cong₂)
open import Size using (Size; ∞; ↑_; Size<_)
open import Data.Vec using (_∷_; [])
open import Level using (lift)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; _◅_; ε)

open import Codata.Thunk as Thunk using (Thunk; force)

import Data.Unit
pattern * = lift Data.Unit.tt

data Gr-Sorts : Set where
  Edge : Gr-Sorts
  Node : Gr-Sorts

data Gr-Functions : Set where
  s : Gr-Functions
  t : Gr-Functions

Gr : Signature
Gr = record { 𝓢 = Gr-Sorts
            ; 𝓕 = Gr-Functions
            ; sign𝓕 = λ { s → [ Edge ] ↦ Node
                        ; t → [ Edge ] ↦ Node
                        }
            } where open import Data.Vec using ([_])

data G₀-Edges : Set where e0 e1 e2 : G₀-Edges
data G₀-Nodes : Set where n0 n1 n2 : G₀-Nodes

G₀ : Σ-Algebra Gr
G₀ = record { S = λ { Edge → G₀-Edges ; Node → G₀-Nodes }
            ; F = λ { s → λ { (e0 , *) → n0
                            ; (e1 , *) → n1
                            ; (e2 , *) → n2
                            }
                    ; t → λ { (e0 , *) → n1
                            ; (e1 , *) → n2
                            ; (e2 , *) → n0
                            }
                    }
            }

data G₁-Edges : Set where e3 e4 : G₁-Edges
data G₁-Nodes : Set where n3 n4 : G₁-Nodes

G₁ : Σ-Algebra Gr
G₁ = record { S = λ { Edge → G₁-Edges ; Node → G₁-Nodes }
            ; F = λ { s → λ { (e3 , *) → n3
                            ; (e4 , *) → n4
                            }
                    ; t → λ { (e3 , *) → n4
                            ; (e4 , *) → n3
                            }
                    }
            }

data G₂-Edges : Set where e5 : G₂-Edges
data G₂-Nodes : Set where n5 : G₂-Nodes

G₂ : Σ-Algebra Gr
G₂ = record { S = λ { Edge → G₂-Edges ; Node → G₂-Nodes }
            ; F = λ { s → λ { (e5 , *) → n5
                            }
                    ; t → λ { (e5 , *) → n5
                            }
                    }
            }

data F₀-Edges : G₀-Edges → G₁-Edges → Set where
  e0e4 : F₀-Edges e0 e4
  e1e3 : F₀-Edges e1 e3

data F₀-Nodes : G₀-Nodes → G₁-Nodes → Set where
  n0n4 : F₀-Nodes n0 n4
  n1n3 : F₀-Nodes n1 n3
  n2n4 : F₀-Nodes n2 n4

F₀ : Σ-Rel G₀ G₁
F₀ = record { ρ = λ { {Edge} → F₀-Edges
                    ; {Node} → F₀-Nodes
                    }
            ; ρ-homo = λ { s (e0e4 , *) → n0n4
                          ; s (e1e3 , *) → n1n3
                          ; t (e0e4 , *) → n1n3
                          ; t (e1e3 , *) → n2n4
                          }
            }

data F₁-Edges : G₁-Edges → G₂-Edges → Set where
  e3e5₁ : F₁-Edges e3 e5
data F₁-Nodes : G₁-Nodes → G₂-Nodes → Set where
  n3n5₁ : F₁-Nodes n3 n5
  n4n5₁ : F₁-Nodes n4 n5

F₁ : Σ-Rel G₁ G₂
F₁ = record { ρ = λ { {Edge} → F₁-Edges
                    ; {Node} → F₁-Nodes
                    }
            ; ρ-homo = λ { s (e3e5₁ , *) → n3n5₁
                          ; t (e3e5₁ , *) → n4n5₁
                          }
            }

data F₂-Edges : G₁-Edges → G₂-Edges → Set where
  e4e5₂ : F₂-Edges e4 e5
data F₂-Nodes : G₁-Nodes → G₂-Nodes → Set where
  n3n5₂ : F₂-Nodes n3 n5
  n4n5₂ : F₂-Nodes n4 n5

F₂ : Σ-Rel G₁ G₂
F₂ = record { ρ = λ { {Edge} → F₂-Edges
                    ; {Node} → F₂-Nodes
                    }
            ; ρ-homo = λ { s (e4e5₂ , *) → n4n5₂
                          ; t (e4e5₂ , *) → n3n5₂
                          }
            }

data F₃-Edges : G₂-Edges → G₂-Edges → Set where
  e5e5 : F₃-Edges e5 e5
data F₃-Nodes : G₂-Nodes → G₂-Nodes → Set where
  n5n5 : F₃-Nodes n5 n5

F₃ : Σ-Rel G₂ G₂
F₃ = record { ρ = λ { {Edge} → F₃-Edges
                    ; {Node} → F₃-Nodes
                    }
            ; ρ-homo = λ { s (e5e5 , *) → n5n5
                          ; t (e5e5 , *) → n5n5
                          }
            }

data W : Set where
  ω₀ ω₁ ω₂ : W

data _⇝_ : W → W → Set where
  f₀    : ω₀ ⇝ ω₁
  f₁ f₂ : ω₁ ⇝ ω₂
  f₃    : ω₂ ⇝ ω₂

d : W → Σ-Algebra Gr
d ω₀ = G₀
d ω₁ = G₁
d ω₂ = G₂

𝓒 : ∀ {A B} → A ⇝ B → Σ-Rel (d A) (d B)
𝓒 f₀ = F₀
𝓒 f₁ = F₁
𝓒 f₂ = F₂
𝓒 f₃ = F₃

open import CounterpartModel

M : CounterpartModel Gr
M = record { W = W ; d = d ; _⇝_ = _⇝_ ; 𝓒 = 𝓒 }

open Signature Gr
open import QLTL Gr
open SortedAlgebra.Term Gr

open import Semantics M

infix 27 _$_

_$_ : ∀ {s n} {Γ : Ctx n} f → _ → Γ ⊢ _ ⟨ ↑ s ⟩
_$_ = fun

v0 : ∀ {n} {Γ : Ctx (1 + n)} → Γ ⊢ _ ⟨ ∞ ⟩
v0 = var fz

v1 : ∀ {n} {Γ : Ctx (2 + n)} → Γ ⊢ _ ⟨ ∞ ⟩
v1 = var (fs fz)

present : ∀ {τ} → QLTL (τ ∷ [])
present {τ} = ∃< τ > v1 ≡ᵗ v0

notPresent : ∀ {τ} → QLTL (τ ∷ [])
notPresent {τ} = ∀< τ > v1 ≢ᵗ v0

nextStepPreserved : ∀ {τ} → QLTL (τ ∷ [])
nextStepPreserved = present ∧ O present

nextStepDeallocated : ∀ {τ} → QLTL (τ ∷ [])
nextStepDeallocated = present ∧ A notPresent

loop : ∀ {n} {Γ : Ctx n} → QLTL (Edge ∷ Γ)
loop = s $ (v0 , *) ≡ᵗ t $ (v0 , *)

hasLoop : QLTL []
hasLoop = ∃< Edge > loop

nodeHasLoop : QLTL (Node ∷ [])
nodeHasLoop = ∃< Edge > (s $ (v0 , *) ≡ᵗ v1 ∧ loop)

willBecomeLoop : QLTL (Edge ∷ [])
willBecomeLoop = ! loop ∧ ◇ loop

eventuallyNodeHasLoop : QLTL (Node ∷ [])
eventuallyNodeHasLoop = ◇ nodeHasLoop

_⇒ : ∀ {ℓ ℓ′} {A : Set ℓ} {i j : A} {R : Rel A ℓ′} → R i j → Star R i j
a ⇒ = a ◅ ε

pattern step a = a ◅ ε

self : CounterpartTrace M ω₂
self .B = _
self .rel = f₃
self .tail = self

σ : CounterpartTrace M ω₀
σ = f₀ ⇀ (f₁ ⇀ self)
