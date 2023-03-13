{-# OPTIONS --sized-types --guardedness #-}

open import SortedAlgebra

module Example where

open import Data.Nat using (zero; suc; _+_; s≤s; z≤n)
open import Data.Fin using () renaming (zero to fz; suc to fs)

open import Data.Unit.Polymorphic using (⊤)
open import Data.Empty.Polymorphic using (⊥)
open import Data.Empty using (⊥-elim)
open import Data.Product using (∃-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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
  e4e5₂ : F₁-Edges e4 e5
data F₁-Nodes : G₁-Nodes → G₂-Nodes → Set where
  n3n5₂ : F₁-Nodes n3 n5
  n4n5₂ : F₁-Nodes n4 n5

F₁ : Σ-Rel G₁ G₂
F₁ = record { ρ = λ { {Edge} → F₁-Edges
                    ; {Node} → F₁-Nodes
                    }
            ; ρ-homo = λ { s (e4e5₂ , *) → n4n5₂
                          ; t (e4e5₂ , *) → n3n5₂
                          }
            }

data F₂-Edges : G₁-Edges → G₂-Edges → Set where
  e3e5₁ : F₂-Edges e3 e5
data F₂-Nodes : G₁-Nodes → G₂-Nodes → Set where
  n3n5₁ : F₂-Nodes n3 n5
  n4n5₁ : F₂-Nodes n4 n5

F₂ : Σ-Rel G₁ G₂
F₂ = record { ρ = λ { {Edge} → F₂-Edges
                    ; {Node} → F₂-Nodes
                    }
            ; ρ-homo = λ { s (e3e5₁ , *) → n3n5₁
                          ; t (e3e5₁ , *) → n4n5₁
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

v2 : ∀ {n} {Γ : Ctx (3 + n)} → Γ ⊢ _ ⟨ ∞ ⟩
v2 = var (fs (fs fz))

present : ∀ {τ} → QLTL (τ ∷ [])
present {τ} = ∃< τ > v1 ≡ᵗ v0

notPresent : ∀ {τ} → QLTL (τ ∷ [])
notPresent {τ} = ∀< τ > v1 ≢ᵗ v0

nextPreserved : ∀ {τ} → QLTL (τ ∷ [])
nextPreserved = present ∧ O present

nextDealloc : ∀ {τ} → QLTL (τ ∷ [])
nextDealloc = present ∧ A notPresent

loop : ∀ {n} {Γ : Ctx n} → QLTL (Edge ∷ Γ)
loop = s $ (v0 , *) ≡ᵗ t $ (v0 , *)

worldHasLoop : QLTL []
worldHasLoop = ∃< Edge > loop

hasLoop : QLTL (Node ∷ [])
hasLoop = ∃< Edge > (s $ (v0 , *) ≡ᵗ v1 ∧ loop)

adjacent : QLTL (Node ∷ Node ∷ [])
adjacent = ∃< Edge > ((s $ (v0 , *) ≡ᵗ v1 ∧ t $ (v0 , *) ≡ᵗ v2)
                    ∨ (s $ (v0 , *) ≡ᵗ v2 ∧ t $ (v0 , *) ≡ᵗ v1))

composable : QLTL (Edge ∷ Edge ∷ [])
composable = ∃< Node > (s $ (v2 , *) ≡ᵗ v0 ∧ t $ (v1 , *) ≡ᵗ v0)

haveComposition : QLTL (Edge ∷ Edge ∷ [])
haveComposition = composable ∧ ∃< Edge > (s $ (v0 , *) ≡ᵗ s $ (v2 , *)
                                        ∧ t $ (v0 , *) ≡ᵗ t $ (v1 , *))

willMerge : ∀ {τ} → QLTL (τ ∷ τ ∷ [])
willMerge {τ} = v0 ≢ᵗ v1 ∧ ◇ v0 ≡ᵗ v1

alwaysPreserved : ∀ {τ} → QLTL (τ ∷ [])
alwaysPreserved {τ} = □ present {τ}

willBecomeLoop : QLTL (Edge ∷ [])
willBecomeLoop = ! loop ∧ ◇ loop

_⇒ : ∀ {ℓ ℓ′} {A : Set ℓ} {i j : A} {R : Rel A ℓ′} → R i j → Star R i j
a ⇒ = a ◅ ε

pattern step a = a ◅ ε

self : CounterpartTrace M ω₂
self .B = _
self .rel = f₃
self .tail = self

σ : CounterpartTrace M ω₀
σ = f₀ ⇀ (f₁ ⇀ self)

-----------------------------------------------------------------

_ : skip 0 σ , (e0 , *) ⊨ nextPreserved {Edge}
_ = (e0 , refl) , ((e4 , *) , (e0e4 , *) , e4 , refl)

_ : skip 0 σ , (n1 , *) ⊨ nextPreserved {Node}
_ = (n1 , refl) , ((n3 , *) , (n1n3 , *) , n3 , refl)

_ : skip 0 σ , (e2 , *) ⊨ ! nextPreserved {Edge}
_ = λ { ((e2 , refl) , ()) }

_ : skip 1 σ , (n3 , *) ⊨ ! nextDealloc {Node}
_ = λ { ((.n3 , refl) , snd) → snd (n5 , *) (n3n5₂ , *) n5 refl }

_ : skip 1 σ , (e3 , *) ⊨ nextDealloc {Edge}
_ = (e3 , refl) , (λ { (e5 , *) (() , *) e5 refl })

_ : skip 1 σ , (e4 , *) ⊨ ! nextDealloc {Edge}
_ = λ { ((e4 , refl) , snd) → snd (e5 , *) (e4e5₂ , *) e5 refl }

-----------------------------------------------------------------

_ : skip 0 σ , (e0 , *) ⊨ ! loop
_ = λ ()

_ : skip 1 σ , (e3 , *) ⊨ ! loop
_ = λ ()

_ : skip 2 σ , (e5 , *) ⊨ loop
_ = refl


_ : skip 0 σ , (n0 , *) ⊨ ! hasLoop
_ = λ { (e0 , ()) ; (e1 , ()) ; (e2 , ()) }

_ : skip 1 σ , (n3 , *) ⊨ ! hasLoop
_ = λ { (e3 , ()) ; (e4 , ()) }

_ : skip 2 σ , (n5 , *) ⊨ hasLoop
_ = e5 , (refl , refl)


_ : skip 0 σ , * ⊨ ∃< Node > (! hasLoop)
_ = n0 , (λ { (e0 , ()) ; (e1 , ()) ; (e2 , ()) })

_ : skip 1 σ , * ⊨ ∃< Node > (! hasLoop)
_ = n3 , λ { (e3 , ()) ; (e4 , ()) }

_ : skip 2 σ , * ⊨ ∃< Node > hasLoop
_ = n5 , (e5 , (refl , refl))

-----------------------------------------------------------------

_ : skip 0 σ , (n0 , n1 , *) ⊨ adjacent
_ = e0 , inj₁ (refl , refl)

_ : skip 1 σ , (n3 , n4 , *) ⊨ adjacent
_ = e3 , inj₁ (refl , refl)

_ : skip 1 σ , (n3 , n4 , *) ⊨ O adjacent
_ = ((n5 , n5 , *) , (n3n5₂ , n4n5₂ , *) , e5 , inj₁ (refl , refl))

_ : skip 0 σ , (e0 , e1 , *) ⊨ composable
_ = n1 , refl , refl

_ : skip 0 σ , (e0 , e1 , *) ⊨ O composable
_ = (e4 , e3 , *) , (e0e4 , e1e3 , *) , n3 , refl , refl

_ : skip 1 σ , (e3 , e4 , *) ⊨ ! O composable
_ = λ { () }

_ : skip 0 σ , (e0 , e1 , *) ⊨ ! haveComposition
_ = λ { ((n1 , refl , refl) , e2 , ()) }

_ : skip 0 σ , (e0 , e1 , *) ⊨ ! O haveComposition
_ = λ { ((e4 , e3 , *) , (e0e4 , e1e3 , *) , (n3 , refl , refl) , e3 , ())
      ; ((e4 , e3 , *) , (e0e4 , e1e3 , *) , (n3 , refl , refl) , e4 , ()) } --(e4 , e3 , *) , (e0e4 , e1e3 , *) , n3 , refl , refl

_ : skip 2 σ , (e5 , e5 , *) ⊨ O haveComposition
_ = (e5 , (e5 , *)) , ((e5e5 , e5e5 , *) , (n5 , refl , refl) , e5 , refl , refl)

-----------------------------------------------------------------

_ : skip 1 σ , * ⊨ ∃< Node > ∃< Node > willMerge
_ = n3 , (n4 , (λ ()) , 1 , (λ { zero (s≤s z≤n) → (n4 , (n3 , *)) , ((refl , refl , *) , *)
                                ; (suc _) (s≤s ()) })
          , (n5 , (n5 , *)) , (((n5 , (n4n5₂ , refl)) , ((n5 , (n3n5₂ , refl)) , *)) , refl))

_ : skip 0 σ , * ⊨ ∃< Node > ∃< Node > willMerge
_ = n0 , (n1 , (λ ()) , 2 ,
           (λ { zero (s≤s z≤n) → (n1 , (n0 , *)) , ((refl , refl , *) , *)
              ; (suc zero) (s≤s (s≤s z≤n)) → (n3 , n4 , *) ,
                                             (((n3 , n1n3 , refl) , ((n4 , n0n4 , refl) , *)) , *) })
           , (n5 , (n5 , *)) , ((n3 , (n1n3 , (n5 , (n3n5₂ , refl)))
                             ) , ((n4 , (n0n4 , (n5 , (n4n5₂ , refl)))) , *)) , refl)

_` : skip 0 σ , * ⊨ ! ∀< Edge > alwaysPreserved
_` ¬∀ with ¬∀ e2
... | inj₂ always with always 1
... | ()

_ : skip 0 σ , * ⊨ ∃< Edge > willBecomeLoop
_ = e0 , ((λ ()) , 2 , (λ { zero (s≤s z≤n) → (e0 , *) , ((refl , *) , *)
                          ; (suc zero) (s≤s (s≤s z≤n)) →
                                (e4 , *) , ((e4 , e0e4 , refl) , *) , *
                          })
       , ((e5 , *) , (((e4 , (e0e4 , e5 , (e4e5₂ , refl))) , *) , refl)))

_ : skip 0 σ , * ⊨ (∃< Edge > s $ (v0 , *) ≢ᵗ t $ (v0 , *)) U (∃< Node > ∀< Node > v0 ≡ᵗ v1)
_ = 2 , (λ { zero (s≤s z≤n) → * , (* , (e2 , (λ ())))
           ; (suc zero) (s≤s (s≤s z≤n)) → * , (* , (e3 , (λ ())))
           }) , * , * , n5 , (λ { n5 → refl })

p : skip 2 σ , * ⊨ ∃< Edge > (□ loop)
p = e5 , inj₂ a
  where
    a : _
    a zero = (e5 , *) , (refl , *) , refl
    a (suc i) with a i
    ... | (fst , *) , (fst₁ , *) , snd = (fst , *) , ((e5 , e5e5 , fst₁) , *) , snd

_`` : skip 0 σ , * ⊨ ∃< Edge > (◇ □ loop)
_`` = e0 , 2 , (λ { zero (s≤s z≤n) → (e0 , *) , (refl , *) , *
                  ; (suc .zero) (s≤s (s≤s z≤n)) → (e4 , *) , ((e4 , e0e4 , refl) , *) , * })
             , (e5 , *) , ((e4 , (e0e4 , (e5 , (e4e5₂ , refl)))) , *)
             , proj₂ p
