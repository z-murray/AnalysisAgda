{-# OPTIONS --without-K --safe #-}
open import Algebra
open import Data.Bool.Base using (Bool; if_then_else_)
open import Function.Base using (_∘_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; +0; +[1+_]; -[1+_])
import Data.Integer.Properties as ℤP
open import Data.Integer.DivMod as ℤD
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕP using (≤-step)
import Data.Nat.DivMod as ℕD
open import Level using (0ℓ)
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation using (contraposition)
open import Relation.Nullary.Decidable
open import Relation.Unary using (Pred)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong; sym; subst; trans; ≢-sym)
open import Relation.Binary
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; mkℚᵘ; _≢0; _/_; 0ℚᵘ; 1ℚᵘ; ↥_; ↧_; ↧ₙ_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Algebra.Bundles
open import Algebra.Structures
open import Data.Empty
open import Data.Sum
open import Data.Maybe.Base
open import RealsRefactored
open import Data.List
open import Function.Structures {_} {_} {_} {_} {ℕ} _≡_ {ℕ} _≡_

{-
The solvers are used and renamed often enough to warrant them being opened up here
for the sake of consistency and cleanliness.
-}
open ℝ-Solver
open import NonReflectiveZ as ℤ-Solver using ()
  renaming
    ( solve to ℤsolve
    ; _⊕_   to _:+_
    ; _⊗_   to _:*_
    ; _⊖_   to _:-_
    ; ⊝_    to :-_
    ; _⊜_   to _:=_
    ; Κ     to ℤΚ
    )
open import NonReflectiveQ as ℚ-Solver using ()
  renaming
    ( solve to ℚsolve
    ; _⊕_   to _+:_
    ; _⊗_   to _*:_
    ; _⊖_   to _-:_
    ; ⊝_    to -:_
    ; _⊜_   to _=:_
    ; Κ     to ℚΚ
    )

open ℚᵘ
open ℝ

-- We use "Inequality" instead of "a≤x≤b" to avoid mixing up variable names in practice.
-- Intervals of the form (b,a) where a ≤ b will be nonempty of course.
record ⦅_,_⦆ (a b : ℝ) : Set where
  constructor mk⦅⦆
  field
    x          : ℝ
    inequality : a < x < b

record ⦅_,_⟧ (a b : ℝ) : Set where
  constructor mk⦅⟧
  field
    x          : ℝ
    inequality : a < x ≤ b

record ⟦_,_⦆ (a b : ℝ) : Set where
  constructor mk⟦⦆
  field
    x          : ℝ
    inequality : a ≤ x < b

record ⟦_,_⟧ (a b : ℝ) : Set where
  constructor mk⟦⟧
  field
    x          : ℝ
    inequality : a ≤ x ≤ b

record ⦅-∞,_⦆ (a : ℝ) : Set where
  constructor mk⦅-∞⦆
  field
    x          : ℝ
    inequality : x < a

record ⦅-∞,_⟧ (a : ℝ) : Set where
  constructor mk⦅-∞⟧
  field
    x          : ℝ
    inequality : x ≤ a

record ⦅_,∞⦆ (a : ℝ) : Set where
  constructor mk⦅∞⦆
  field
    x          : ℝ
    inequality : a < x

record ⟦_,∞⦆ (a : ℝ) : Set where
  constructor mk⟦∞⦆
  field
    x          : ℝ
    inequality : a ≤ x
    
_isNonvoid : {A : Set} -> (P : A -> Set) -> Set
_isNonvoid {A} P = ∃ λ (x : A) -> P x

Compact⟦_,_⟧ : ℝ -> ℝ -> Set
Compact⟦ a , b ⟧ = ∃ λ (x : ℝ) -> a ≤ x ≤ b

-- Too much bloat?
data _isUpperBoundOf_ (b : ℝ) (P : ℝ -> Set) : Set where
  upBound* : (∀ x -> P x -> x ≤ b) -> b isUpperBoundOf P

_isBoundedAbove : (P : ℝ -> Set) -> Set
P isBoundedAbove = ∃ λ (b : ℝ) -> b isUpperBoundOf P

_isSupremumOf_ : (s : ℝ) -> (P : ℝ -> Set) -> Set
s isSupremumOf P = s isUpperBoundOf P × (∀ ε -> ε > 0ℝ -> ∃ λ x -> P x × x > s - ε)

_hasSupremum : (ℝ -> Set) -> Set
P hasSupremum = ∃ λ s -> s isSupremumOf P

proposition-4-3-if : ∀ {P : ℝ -> Set} -> P isNonvoid -> P isBoundedAbove ->
                     (∀ {x y : ℝ} -> x < y -> y isUpperBoundOf P ⊎ ∃ λ a -> P a × x < a) ->
                     P hasSupremum 
proposition-4-3-if {P} P≠Ø P≤U hyp = {!!}

proposition-4-3-onlyif : ∀ {P : ℝ -> Set} -> P isNonvoid -> P hasSupremum ->
                         ∀ {x y : ℝ} -> x < y -> y isUpperBoundOf P ⊎ ∃ λ a -> P a × x < a
proposition-4-3-onlyif {P} P≠Ø (s , upBound* P≤s , hyp) {x} {y} x<y = [ left , right ]′ (corollary-2-17 s x y x<y)
  where
    open ≤-Reasoning
    left : s < y -> y isUpperBoundOf P ⊎ ∃ λ a -> P a × x < a
    left s<y = inj₁ (upBound* (λ z Pz -> ≤-trans (P≤s z Pz) (<⇒≤ s<y)))

    right : s > x -> y isUpperBoundOf P ⊎ ∃ λ a -> P a × x < a
    right s>x = let aget = hyp (s - x) (x<y⇒0<y-x x s s>x); a = proj₁ aget in
                inj₂ (a , proj₁ (proj₂ aget) , (begin-strict
      x           ≈⟨ solve 2 (λ s x → x ⊜ s ⊖ (s ⊖ x)) ≃-refl s x ⟩
      s - (s - x) <⟨ proj₂ (proj₂ aget) ⟩
      a            ∎))
