module DVec where

open import Data.Vec as V using ([]; _∷_) renaming (Vec to Vector)

open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Function as F using ()
open import Level using (Level; lift) renaming (suc to sucℓ)
open import Data.Product using (∃-syntax; Σ-syntax; _×_; _,_)
open import Data.Unit.Polymorphic using () renaming (⊤ to Unit)
open import Function using (_∘_; const; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Utils

private
  variable
    n : ℕ
    ℓ ℓ′ : Level
    A B : Set ℓ

map : (A → Set ℓ′) → Vector A n → Set ℓ′
map f [] = Unit
map f (x ∷ v) = f x × map f v

zip : (A → B → Set ℓ′) → Vector A n → Vector B n → Set ℓ′
zip f [] [] = Unit
zip f (x ∷ v) (x′ ∷ v′) = f x x′ × zip f v v′

dmap : ∀ {o : Vector A n} {f g : (A → Set ℓ′)} → (∀ {x} → f x → g x) → map f o → map g o
dmap {o = []} a ⊤ = ⊤
dmap {o = _ ∷ _} a (x , v) = a x , dmap a v

dzip : ∀ {o : Vector A n} {f g : (A → Set ℓ′)} → (∀ {x} → f x → g x → Set ℓ) → map f o → map g o → Set ℓ
dzip {o = []} a ⊤ ⊤ = Unit
dzip {o = _ ∷ _} a (x , v) (x′ , v′) = a x x′ × dzip a v v′

lookup : ∀ {o : Vector A n} {f : (A → Set ℓ)} → (i : Fin n) → map f o → f (V.lookup o i)
lookup {o = _ ∷ _} zero (x , v) = x
lookup {o = _ ∷ _} (suc i) (x , v) = lookup i v

lookup-dzip : ∀ {o : Vector A n} {f g : (A → Set ℓ)} {v : map f o} {v′ : map g o} {ρ : ∀ {x} → f x → g x → Set ℓ}
          → (i : Fin n)
          → dzip ρ v v′
          → ρ (lookup i v) (lookup i v′)
lookup-dzip {o = _ ∷ _} zero (x , v) = x
lookup-dzip {o = _ ∷ _} (suc i) (x , v) = lookup-dzip i v

dzip-imply : ∀ {n ℓ} {A : Set ℓ} {o : Vector A n} {f g : (A → Set ℓ)} {v : map f o} {v′ : map g o} {s t : (∀ {x} → f x → g x → Set ℓ)}
      → (∀ {m} {x y} → s {m} x y → t {m} x y)
      → dzip s v v′
      → dzip t v v′
dzip-imply {o = []} e ⊤ = ⊤
dzip-imply {o = _ ∷ _} e (x , v) = e x , dzip-imply e v

dzip-ext : ∀ {o : Vector A n} {f : (A → Set ℓ)} {v v′ : map f o}
         → dzip _≡_ v v′
         → v ≡ v′
dzip-ext {o = []} {v = ⊤} {v′ = ⊤} ⊤ = refl
dzip-ext {o = _ ∷ _} {v = _ , _} {v′ = _ , _} (refl , v) rewrite dzip-ext v = refl

dzip-id : ∀ {o : Vector A n} {f : (A → Set ℓ)} {v : map f o}
        → dzip _≡_ v v
dzip-id {o = []} {v = ⊤} = ⊤
dzip-id {o = _ ∷ _} {v = _ , v} = refl , dzip-id {v = v}

dmap-cong : ∀ {o : Vector A n} {f g : A → Set ℓ} {v : map f o} {f g : (∀ {x} → f x → g x)}
          → (e : ∀ {x} σ → f {x} σ ≡ g {x} σ)
          → dmap f v ≡ dmap g v
dmap-cong {o = []} e = refl
dmap-cong {o = _ ∷ _} {v = x , v} e rewrite e x | dmap-cong {v = v} e = refl

dmap-comp : ∀ {o : Vector A n} {i j k : A → Set ℓ} {v : map i o} {f : (∀ {x} → j x → k x)} {g : (∀ {x} → i x → j x)}
          → dmap (f ∘ g) v ≡ dmap f (dmap g v)
dmap-comp {o = []} = refl
dmap-comp {o = x ∷ o} {v = _ , v} {f = f} {g = g} rewrite dmap-comp {v = v} {f = f} {g = g} = refl

dmap-id : ∀ {o : Vector A n} {f : A → Set ℓ} {v : map f o}
        → dmap id v ≡ v
dmap-id {o = []} = refl
dmap-id {o = _ ∷ _} {v = _ , v} rewrite dmap-id {v = v}= refl

dzip-rel-decomp : ∀ {o : Vector A n} {f g h : (A → Set ℓ)} {x : map g o} {y : map h o}
        → {s : (∀ {x} → g x → f x → Set ℓ)}
        → {t : (∀ {x} → f x → h x → Set ℓ)}
        → dzip (λ x y → ∃[ a ] (s x a × t a y)) x y
        → Σ[ a ∈ map f o ] (dzip s x a × dzip t a y)
dzip-rel-decomp {o = []} ⊤ = ⊤ , ⊤ , ⊤
dzip-rel-decomp {o = _ ∷ _} (x , v) with dzip-rel-decomp v | x
... | f , g , h | a , x , y = (a , f) , (x , g) , (y , h)

dzip-rel-comp : ∀ {o : Vector A n} {f g h : (A → Set ℓ)} {a : map f o} {x : map g o} {y : map h o}
        → {s : (∀ {x} → g x → f x → Set ℓ)}
        → {t : (∀ {x} → f x → h x → Set ℓ)}
        → dzip s x a → dzip t a y
        → dzip (λ x y → ∃[ a ] (s x a × t a y)) x y
dzip-rel-comp {o = []} ⊤ ⊤ = ⊤
dzip-rel-comp {o = _ ∷ _} (x , v) (x′ , v′) = (_ , x , x′) , dzip-rel-comp v v′

op : ∀ {o : Vector A n} {f g : (A → Set ℓ)} {x : map f o} {y : map g o}
     → {f : (∀ {x} → f x → g x → Set ℓ)}
     → dzip f          x y
     → dzip (F.flip f) y x
op {o = []} ⊤ = ⊤
op {o = _ ∷ _} (x , v) = x , (op v)
