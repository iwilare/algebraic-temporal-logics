{-# OPTIONS --guardedness #-}

{-
  Syntax of the positive normal form for QLTL.
-}
module PNF.PNF where

open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)

-- Syntax of extended PNF
data PNF : ℕ → Set where
    true  : ∀ {n} → PNF n
    false : ∀ {n} → PNF n
    _∧_   : ∀ {n} → PNF n → PNF n → PNF n
    _∨_   : ∀ {n} → PNF n → PNF n → PNF n
    _==_  : ∀ {n} → Fin n → Fin n → PNF n
    _!=_  : ∀ {n} → Fin n → Fin n → PNF n
    ∃<>_  : ∀ {n} → PNF (suc n) → PNF n
    ∀<>_  : ∀ {n} → PNF (suc n) → PNF n
    ◯_    : ∀ {n} → PNF n → PNF n
    A_    : ∀ {n} → PNF n → PNF n
    _U_   : ∀ {n} → PNF n → PNF n → PNF n
    _W_   : ∀ {n} → PNF n → PNF n → PNF n
    _F_   : ∀ {n} → PNF n → PNF n → PNF n
    _T_   : ∀ {n} → PNF n → PNF n → PNF n

infix 25 _∧_ _∨_
infix 30 _U_ _W_ _F_ _T_
infix 35 ∃<>_ ∀<>_
infix 40 ◯_ A_ ♢_ □_ ♢*_ □*_
infix 50 _==_ _!=_

-- Syntactically defined shorthands
♢_ : ∀ {n} → PNF n → PNF n
♢ ϕ = true U ϕ

□_ : ∀ {n} → PNF n → PNF n
□ ϕ = ϕ W false

♢*_ : ∀ {n} → PNF n → PNF n
♢* ϕ = true F ϕ

□*_ : ∀ {n} → PNF n → PNF n
□* ϕ = ϕ T false
