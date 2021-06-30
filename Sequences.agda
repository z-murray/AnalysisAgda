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
import Algebra.Solver.Ring as Solver
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
import Data.Rational.Unnormalised.Solver as ℚ-Solver
import Data.Integer.Solver as ℤ-Solver
open import Data.List
open import RealsRefactored

open ℚᵘ
open ℝ

data _ConvergesTo_ : REL (ℕ -> ℝ) ℝ 0ℓ where
  con* : {f : ℕ -> ℝ} -> {x₀ : ℝ} ->
         (∀ k -> {k≢0 : k ≢0} -> ∃ λ Nₖ -> Nₖ ≢0 × (∀ n -> n ℕ.≥ Nₖ -> ∣ f n - x₀ ∣ ≤ ((+ 1 / k) {k≢0}) ⋆)) ->
         f ConvergesTo x₀

_isConvergent : (ℕ -> ℝ) -> Set
f isConvergent = ∃ λ x₀ -> f ConvergesTo x₀

≃-reflexive : ∀ {x y} -> (∀ n -> {n ≢0} -> seq x n ℚ.≃ seq y n) -> x ≃ y
≃-reflexive {x} {y} hyp = *≃* (λ {(suc n-1) -> let n = suc n-1 in begin
  ℚ.∣ seq x n ℚ.- seq y n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (seq x n) (ℚP.-‿cong (ℚP.≃-sym (hyp n)))) ⟩
  ℚ.∣ seq x n ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n)) ⟩
  0ℚᵘ                       ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                    ∎})
  where open ℚP.≤-Reasoning

∣p∣⋆≃∣p⋆∣ : ∀ p -> ℚ.∣ p ∣ ⋆ ≃ ∣ p ⋆ ∣
∣p∣⋆≃∣p⋆∣ p = ≃-reflexive (λ {n -> ℚP.≃-refl})

p≤q+j⁻¹⇒p≤q : ∀ {p q} -> (∀ j -> {j≢0 : j ≢0} -> p ℚ.≤ q ℚ.+ (+ 1 / j) {j≢0}) -> p ℚ.≤ q
p≤q+j⁻¹⇒p≤q {p} {q} hyp = p-q≤j⁻¹⇒p≤q (λ {(suc j-1) -> let j = suc j-1 in begin
  p ℚ.- q             ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- q) (hyp j) ⟩
  q ℚ.+ + 1 / j ℚ.- q ≈⟨ solve 2 (λ q j⁻¹ -> q :+ j⁻¹ :- q := j⁻¹) ℚP.≃-refl q (+ 1 / j) ⟩
  + 1 / j              ∎})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver

{-
Useful for escaping the "metal" of the reals.
-}
∣x-y∣≤k⁻¹⇒x≃y : ∀ x y -> (∀ (k : ℕ) -> {k≢0 : k ≢0} -> ∣ x - y ∣ ≤ ((+ 1 / k) {k≢0}) ⋆) -> x ≃ y
∣x-y∣≤k⁻¹⇒x≃y x y hyp = *≃* λ {(suc n-1) -> p≤q+j⁻¹⇒p≤q (λ {(suc j-1) ->
                        let n = suc n-1; j = suc j-1; xₙ = seq x n; yₙ = seq y n in
                        p⋆≤q⋆⇒p≤q ℚ.∣ xₙ ℚ.- yₙ ∣ (+ 2 / n ℚ.+ + 1 / j) (begin
  ℚ.∣ xₙ ℚ.- yₙ ∣ ⋆                       ≈⟨ ≃-trans (∣p∣⋆≃∣p⋆∣ (xₙ ℚ.- yₙ)) (∣-∣-cong (⋆-distrib-to-p⋆-q⋆ xₙ yₙ)) ⟩
  ∣ xₙ ⋆ - yₙ ⋆ ∣                         ≈⟨ ≃-symm (∣-∣-cong
                                             (≃-trans (+-congˡ (xₙ ⋆ - yₙ ⋆) (+-identityˡ 0ℝ)) (+-identityˡ (xₙ ⋆ - yₙ ⋆)))) ⟩
  ∣ 0ℝ + 0ℝ + (xₙ ⋆ - yₙ ⋆) ∣             ≈⟨ ≃-symm (∣-∣-cong (+-congˡ (xₙ ⋆ - yₙ ⋆) (+-cong (+-inverseʳ x) (+-inverseʳ y)))) ⟩
  ∣ (x - x) + (y - y) + (xₙ ⋆ - yₙ ⋆) ∣   ≈⟨ ∣-∣-cong (ℝsolve 6 (λ x -x y -y xₙ -yₙ ->
                                             (x +: -x) +: (y +: -y) +: (xₙ +: -yₙ) =:
                                             ((xₙ +: -x) +: (y +: -yₙ) +: (x +: -y)) )
                                             ≃-refl x (- x) y (- y) (xₙ ⋆) (- (yₙ ⋆))) ⟩
  ∣ (xₙ ⋆ - x) + (y - yₙ ⋆) + (x - y) ∣   ≤⟨ ≤-trans
                                             (∣x+y∣≤∣x∣+∣y∣ ((xₙ ⋆ - x) + (y - yₙ ⋆)) (x - y))
                                             (+-monoˡ-≤ ∣ x - y ∣ (∣x+y∣≤∣x∣+∣y∣ (xₙ ⋆ - x) (y - yₙ ⋆))) ⟩
  ∣ xₙ ⋆ - x ∣ + ∣ y - yₙ ⋆ ∣ + ∣ x - y ∣  ≤⟨ +-mono-≤
                                              (+-mono-≤ (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ x (xₙ ⋆)) (lemma-2-14 x n))
                                              (lemma-2-14 y n)) (hyp j) ⟩
  (+ 1 / n) ⋆ + (+ 1 / n) ⋆ + (+ 1 / j) ⋆ ≈⟨ ≃-symm (≃-trans (⋆-distrib-+ (+ 1 / n ℚ.+ + 1 / n) (+ 1 / j))
                                                    (+-congˡ ((+ 1 / j) ⋆) (⋆-distrib-+ (+ 1 / n) (+ 1 / n)))) ⟩
  (+ 1 / n ℚ.+ + 1 / n ℚ.+ + 1 / j) ⋆     ≈⟨ ⋆-cong (ℚP.+-congˡ (+ 1 / j) {+ 1 / n ℚ.+ + 1 / n} {+ 2 / n}
                                             (ℚ.*≡* (solve 1 (λ n ->
                                             (con (+ 1) :* n :+ con (+ 1) :* n) :* n := con (+ 2) :* (n :* n)) refl (+ n)))) ⟩
  (+ 2 / n ℚ.+ + 1 / j) ⋆                  ∎)})}
  where
    open ≤-Reasoning
    open ℝ-+-*-Solver using ()
      renaming
        ( solve to ℝsolve
        ; _:+_ to _+:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver

uniqueness-of-limits : ∀ {f : ℕ -> ℝ} -> ∀ {x y : ℝ} -> f ConvergesTo x -> f ConvergesTo y -> x ≃ y
uniqueness-of-limits {f} {x} {y} (con* f→x) (con* f→y) = ∣x-y∣≤k⁻¹⇒x≃y x y (λ {(suc k-1) ->
                                                         let k = suc k-1; N₁ = proj₁ (f→x (2 ℕ.* k)); N₂ = proj₁ (f→y (2 ℕ.* k))
                                                               ; N = N₁ ℕ.⊔ N₂ in begin
  ∣ x - y ∣                                 ≈⟨ ∣-∣-cong (≃-symm (+-congˡ (- y)
                                               (≃-trans (+-congʳ x (+-inverseʳ (f N))) (+-identityʳ x)))) ⟩
  ∣ x + (f N - f N) - y ∣                   ≈⟨ ∣-∣-cong (ℝsolve 4 (λ x -y fN -fN ->
                                               x +: (fN +: -fN) +: -y =: (x +: -fN) +: (fN +: -y))
                                               ≃-refl x (- y) (f N) (- f N)) ⟩
  ∣ (x - f N) + (f N - y) ∣                 ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (x - f N) (f N - y) ⟩
  ∣ x - f N ∣ + ∣ f N - y ∣                 ≤⟨ +-mono-≤
                                              (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (f N) x) (proj₂ (proj₂ (f→x (2 ℕ.* k))) N (ℕP.m≤m⊔n N₁ N₂)))
                                              (proj₂ (proj₂ (f→y (2 ℕ.* k))) N (ℕP.m≤n⊔m N₁ N₂)) ⟩
  (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-trans
                                               (≃-symm (⋆-distrib-+ (+ 1 / (2 ℕ.* k)) (+ 1 / (2 ℕ.* k))))
                                               (⋆-cong (ℚ.*≡* (solve 1 (λ k ->
                                               (con (+ 1) :* (con (+ 2) :* k) :+ con (+ 1) :* (con (+ 2) :* k)) :* k :=
                                               con (+ 1) :* (con (+ 2) :* k :* (con (+ 2) :* k)))
                                               refl (+ k)))) ⟩
  (+ 1 / k) ⋆                                ∎})
  where
    open ≤-Reasoning
    open ℝ-+-*-Solver using ()
      renaming
        ( solve to ℝsolve
        ; _:+_  to _+:_
        ; _:=_  to _=:_
        )
    open ℤ-Solver.+-*-Solver

data _isBounded : (ℕ -> ℝ) -> Set where
  bound* : {f : ℕ -> ℝ} -> (∃ λ r -> Positive r × ∀ n -> {n ≢0} -> ∣ f n ∣ ≤ r) -> f isBounded

{-
Let x₀ = lim f. Then
-}
convergentSeq⇒bounded : ∀ {f : ℕ -> ℝ} -> f isConvergent -> f isBounded
convergentSeq⇒bounded {f} (x₀ , con* f→x₀) = bound* {!!}

data _isCauchy : (ℕ -> ℝ) -> Set where
  cauchy* : {f : ℕ -> ℝ} ->
            (∀ k -> {k≢0 : k ≢0} -> ∃ λ Mₖ -> Mₖ ≢0 × ∀ m n -> m ℕ.≥ Mₖ -> n ℕ.≥ Mₖ ->
                    ∣ f m - f n ∣ ≤ (+ 1 / k) {k≢0} ⋆) -> f isCauchy

convergent⇒cauchy : ∀ {f : ℕ -> ℝ} -> f isConvergent -> f isCauchy
convergent⇒cauchy {f} (x₀ , con* f→x₀) = cauchy* (λ {(suc k-1) ->
                                         let k = suc k-1; N₂ₖ = proj₁ (f→x₀ (2 ℕ.* k)); Mₖ = suc N₂ₖ in
                                         Mₖ , _ , λ {(suc m-1) (suc n-1) m≥Mₖ n≥Mₖ -> let m = suc m-1 ; n = suc n-1 in
                                         begin
  ∣ f m - f n ∣                             ≈⟨ ∣-∣-cong (≃-symm (+-congˡ (- f n) (≃-trans
                                               (+-congʳ (f m) (+-inverseʳ x₀)) (+-identityʳ (f m))))) ⟩
  ∣ f m + (x₀ - x₀) - f n ∣                 ≈⟨ ∣-∣-cong (ℝsolve 4 (λ fm x₀ -x₀ -fn ->
                                               fm +: (x₀ +: -x₀) +: -fn =:
                                               fm +: -x₀ +: (x₀ +: -fn))
                                               ≃-refl (f m) x₀ (- x₀) (- f n)) ⟩
  ∣ f m - x₀ + (x₀ - f n) ∣                 ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (f m - x₀) (x₀ - f n) ⟩
  ∣ f m - x₀ ∣ + ∣ x₀ - f n ∣               ≤⟨ +-mono-≤
                                              (proj₂ (proj₂ (f→x₀ (2 ℕ.* k))) m (ℕP.≤-trans (ℕP.n≤1+n N₂ₖ) m≥Mₖ))
                                              (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (f n) x₀)
                                                         (proj₂ (proj₂ (f→x₀ (2 ℕ.* k))) n (ℕP.≤-trans (ℕP.n≤1+n N₂ₖ) n≥Mₖ))) ⟩
  (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-trans
                                               (≃-symm (⋆-distrib-+ (+ 1 / (2 ℕ.* k)) (+ 1 / (2 ℕ.* k))))
                                               (⋆-cong (ℚ.*≡* (solve 1 (λ k ->
                                               (con (+ 1) :* (con (+ 2) :* k) :+ con (+ 1) :* (con (+ 2) :* k)) :* k :=
                                               con (+ 1) :* (con (+ 2) :* k :* (con (+ 2) :* k))) refl (+ k)))) ⟩
  (+ 1 / k) ⋆                                ∎}})
  where
    open ≤-Reasoning
    open ℝ-+-*-Solver using ()
      renaming
        ( solve to ℝsolve
        ; _:+_  to _+:_
        ; _:=_  to _=:_
        )
    open ℤ-Solver.+-*-Solver

cauchy⇒convergent : ∀ {f : ℕ -> ℝ} -> f isCauchy -> f isConvergent
cauchy⇒convergent {f} (cauchy* fCauchy) = y , f→y
  where
    open ≤-Reasoning
    open ℝ-+-*-Solver using ()
      renaming
        ( solve to ℝsolve
        ; _:+_  to _+:_
        ; _:=_  to _=:_
        )
    open ℤ-Solver.+-*-Solver
    N : ℕ -> ℕ
    N k-1 = let k = suc k-1; M₂ₖ = proj₁ (fCauchy (2 ℕ.* k)) in
                  suc ((3 ℕ.* k) ℕ.⊔ M₂ₖ)

    Nₖ-prop : ∀ k-1 -> ∀ m n -> m ℕ.≥ N k-1 -> n ℕ.≥ N k-1 -> ∣ f m - f n ∣ ≤ (+ 1 / (2 ℕ.* (suc k-1))) ⋆
    Nₖ-prop k-1 = λ {(suc m-1) (suc n-1) m≥N n≥N -> let k = suc k-1; m = suc m-1; n = suc n-1; M₂ₖ = proj₁ (fCauchy (2 ℕ.* k)) in
                  proj₂ (proj₂ (fCauchy (2 ℕ.* k))) m n
                  (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (3 ℕ.* k) M₂ₖ) (ℕP.n≤1+n ((3 ℕ.* k) ℕ.⊔ M₂ₖ))) m≥N)
                  (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (3 ℕ.* k) M₂ₖ) (ℕP.n≤1+n ((3 ℕ.* k) ℕ.⊔ M₂ₖ))) n≥N)}

    ys : (k : ℕ) -> {k ≢0} -> ℚᵘ
    ys (suc k-1) = let k = suc k-1 in
                  seq (f (N k-1)) (2 ℕ.* k)

    helper : ∀ k-1 -> (+ 1 / (2 ℕ.* (suc k-1))) ⋆ + (+ 1 / (2 ℕ.* (suc k-1))) ⋆ ≃ (+ 1 / (suc k-1)) ⋆
    helper k-1 = let k = suc k-1 in begin-equality
      (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-symm (⋆-distrib-+ (+ 1 / (2 ℕ.* k)) (+ 1 / (2 ℕ.* k))) ⟩
      (+ 1 / (2 ℕ.* k) ℚ.+ + 1 / (2 ℕ.* k)) ⋆   ≈⟨ ⋆-cong (ℚ.*≡* (solve 1 (λ k ->
                                                   (con (+ 1) :* (con (+ 2) :* k) :+ (con (+ 1) :* (con (+ 2) :* k))) :* k :=
                                                   con (+ 1) :* (con (+ 2) :* k :* (con (+ 2) :* k))) refl (+ k))) ⟩
      (+ 1 / k) ⋆                                ∎

    helper2 : ∀ m-1 n-1 -> ∣ f (N m-1) - f (N n-1) ∣ ≤ (+ 1 / (2 ℕ.* (suc m-1)) ℚ.+ + 1 / (2 ℕ.* (suc n-1))) ⋆
    helper2 m-1 n-1 = [ left , right ]′ (ℕP.≤-total (N m-1) (N n-1))
      where
        m = suc m-1
        n = suc n-1
        left : N m-1 ℕ.≤ N n-1 -> ∣ f (N m-1) - f (N n-1) ∣ ≤ (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n)) ⋆
        left Nₘ≤Nₙ = begin 
          ∣ f (N m-1) - f (N n-1) ∣               ≤⟨ Nₖ-prop m-1 (N m-1) (N n-1) ℕP.≤-refl Nₘ≤Nₙ ⟩
          (+ 1 / (2 ℕ.* m)) ⋆                     ≤⟨ p≤q⇒p⋆≤q⋆ (+ 1 / (2 ℕ.* m)) (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n))
                                                     (ℚP.≤-respˡ-≃ (ℚP.+-identityʳ (+ 1 / (2 ℕ.* m)))
                                                     (ℚP.+-monoʳ-≤ (+ 1 / (2 ℕ.* m)) {0ℚᵘ} {+ 1 / (2 ℕ.* n)} (ℚP.nonNegative⁻¹ _))) ⟩
          (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n)) ⋆  ∎

        right : N n-1 ℕ.≤ N m-1 -> ∣ f (N m-1) - f (N n-1) ∣ ≤ (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n)) ⋆
        right Nₙ≤Nₘ = begin
          ∣ f (N m-1) - f (N n-1) ∣               ≈⟨ ∣x-y∣≃∣y-x∣ (f (N m-1)) (f (N n-1)) ⟩
          ∣ f (N n-1) - f (N m-1) ∣               ≤⟨ Nₖ-prop n-1 (N n-1) (N m-1) ℕP.≤-refl Nₙ≤Nₘ ⟩
          (+ 1 / (2 ℕ.* n)) ⋆                     ≤⟨ p≤q⇒p⋆≤q⋆ (+ 1 / (2 ℕ.* n)) (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n))
                                                     (ℚP.≤-respˡ-≃ (ℚP.+-identityˡ (+ 1 / (2 ℕ.* n)))
                                                     (ℚP.+-monoˡ-≤ (+ 1 / (2 ℕ.* n)) {0ℚᵘ} {+ 1 / (2 ℕ.* m)} (ℚP.nonNegative⁻¹ _))) ⟩
          (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n)) ⋆  ∎

    y : ℝ
    seq y 0 = 0ℚᵘ
    seq y (suc k-1) = ys (suc k-1)
    reg y = regular-n≤m (seq y) (λ {(suc m-1) (suc n-1) n≤m -> let m = suc m-1; n = suc n-1 in
                                p⋆≤q⋆⇒p≤q ℚ.∣ ys m ℚ.- ys n ∣ (+ 1 / m ℚ.+ + 1 / n) (begin
      ℚ.∣ ys m ℚ.- ys n ∣ ⋆                           ≈⟨ ≃-trans
                                                         (∣p∣⋆≃∣p⋆∣ (ys m ℚ.- ys n))
                                                         (∣-∣-cong (⋆-distrib-to-p⋆-q⋆ (ys m) (ys n))) ⟩
      ∣ ys m ⋆ - ys n ⋆ ∣                             ≈⟨ ∣-∣-cong (≃-symm (≃-trans
                                                         (+-congˡ (ys m ⋆ - ys n ⋆)
                                                           (≃-trans (+-cong (+-inverseʳ (f (N m-1))) (+-inverseʳ (f (N n-1))))
                                                                    (+-identityʳ 0ℝ)))
                                                         (+-identityˡ (ys m ⋆ - ys n ⋆)))) ⟩
      ∣ f (N m-1) - f (N m-1) + (f (N n-1) - f (N n-1))
        + (ys m ⋆ - ys n ⋆) ∣                         ≈⟨ ∣-∣-cong (ℝsolve 6 (λ fm -fm fn -fn ym -yn ->
                                                         fm +: -fm +: (fn +: -fn) +: (ym +: -yn) =:
                                                         (ym +: -fm) +: (fm +: -fn) +: (fn +: -yn))
                                                         ≃-refl (f (N m-1)) (- f (N m-1)) (f (N n-1)) (- f (N n-1)) (ys m ⋆) (- (ys n ⋆))) ⟩
      ∣ (ys m ⋆ - f (N m-1)) + (f (N m-1) - f (N n-1)) 
        + (f (N n-1) - ys n ⋆) ∣                        ≤⟨ ≤-trans
                                                         (∣x+y∣≤∣x∣+∣y∣ ((ys m ⋆ - f (N m-1)) + (f (N m-1) - f (N n-1))) (f (N n-1) - ys n ⋆))
                                                         (+-monoˡ-≤ ∣ f (N n-1) - ys n ⋆ ∣ (∣x+y∣≤∣x∣+∣y∣ (ys m ⋆ - f (N m-1)) (f (N m-1) - f (N n-1)))) ⟩
      ∣ ys m ⋆ - f (N m-1) ∣ + ∣ f (N m-1) - f (N n-1) ∣
        + ∣ f (N n-1) - ys n ⋆ ∣                        ≤⟨ +-mono-≤
                                                         (+-mono-≤ (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (f (N m-1)) (ys m ⋆)) (lemma-2-14 (f (N m-1)) (2 ℕ.* m)))
                                                         (≤-respʳ-≃ (⋆-distrib-+ (+ 1 / (2 ℕ.* m)) (+ 1 / (2 ℕ.* n))) (helper2 m-1 n-1)))
                                                         (lemma-2-14 (f (N n-1)) (2 ℕ.* n)) ⟩
      (+ 1 / (2 ℕ.* m)) ⋆ + ((+ 1 / (2 ℕ.* m)) ⋆
        + (+ 1 / (2 ℕ.* n)) ⋆) + (+ 1 / (2 ℕ.* n)) ⋆  ≈⟨ ℝsolve 2 (λ m n -> m +: (m +: n) +: n =: (m +: m) +: (n +: n))
                                                         ≃-refl ((+ 1 / (2 ℕ.* m)) ⋆) ((+ 1 / (2 ℕ.* n)) ⋆) ⟩
      (+ 1 / (2 ℕ.* m)) ⋆ + (+ 1 / (2 ℕ.* m)) ⋆
        + ((+ 1 / (2 ℕ.* n)) ⋆ + (+ 1 / (2 ℕ.* n)) ⋆) ≈⟨ +-cong (helper m-1) (helper n-1) ⟩
      (+ 1 / m) ⋆ + (+ 1 / n) ⋆                       ≈⟨ ≃-symm (⋆-distrib-+ (+ 1 / m) (+ 1 / n)) ⟩
      (+ 1 / m ℚ.+ + 1 / n) ⋆                          ∎)})

    f→y : f ConvergesTo y
    f→y = con* (λ {(suc k-1) -> N k-1 , _ ,
          λ {(suc n-1) n≥Nₖ -> let k = suc k-1; n = suc n-1
                                     ; n≥3k = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n (3 ℕ.* k) (proj₁ (fCauchy (2 ℕ.* k)))) (ℕP.n≤1+n (ℕ.pred (N k-1)))) n≥Nₖ in begin
      ∣ f n - y ∣                                                         ≈⟨ ∣-∣-cong (≃-symm (≃-trans
                                                                             (+-congˡ (f n - y) (≃-trans (+-cong (+-inverseʳ (f (N n-1))) (+-inverseʳ (ys n ⋆)))
                                                                                                         (+-identityʳ 0ℝ)))
                                                                             (+-identityˡ (f n - y)))) ⟩
      ∣ (f (N n-1) - f (N n-1)) + (ys n ⋆ - ys n ⋆) + (f n - y) ∣         ≈⟨ ∣-∣-cong (ℝsolve 6 (λ fN -fN yn -yn fn -y ->
                                                                             (fN +: -fN) +: (yn +: -yn) +: (fn +: -y) =:
                                                                             ((yn +: -y) +: (fN +: -yn) +: (fn +: -fN)))
                                                                             ≃-refl (f (N n-1)) (- f (N n-1)) (ys n ⋆) (- (ys n ⋆)) (f n) (- y)) ⟩
      ∣ (ys n ⋆ - y) + (f (N n-1) - ys n ⋆) + (f n - f (N n-1)) ∣         ≤⟨ ≤-trans
                                                                             (∣x+y∣≤∣x∣+∣y∣ ((ys n ⋆ - y) + (f (N n-1) - ys n ⋆)) (f n - f (N n-1)))
                                                                             (+-monoˡ-≤ ∣ f n - f (N n-1) ∣ (∣x+y∣≤∣x∣+∣y∣ (ys n ⋆ - y) (f (N n-1) - ys n ⋆))) ⟩
      ∣ ys n ⋆ - y ∣ + ∣ f (N n-1) - ys n ⋆ ∣ + ∣ f n - f (N n-1) ∣        ≤⟨ +-mono-≤ (+-mono-≤
                                                                              (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ y (ys n ⋆)) (lemma-2-14 y n))
                                                                              (lemma-2-14 (f (N n-1)) (2 ℕ.* n)))
                                                                              (Nₖ-prop k-1 n (N n-1) n≥Nₖ
                                                                              (ℕP.≤-trans (ℕP.≤-trans n≥Nₖ (ℕP.m≤n*m n {3} ℕP.0<1+n))
                                                                                          (ℕP.≤-trans (ℕP.m≤m⊔n (3 ℕ.* n) (proj₁ (fCauchy (2 ℕ.* n))))
                                                                                                      (ℕP.n≤1+n (ℕ.pred (N n-1)))))) ⟩
      (+ 1 / n) ⋆ + (+ 1 / (2 ℕ.* n)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆             ≈⟨ ≃-symm (≃-trans
                                                                             (⋆-distrib-+ (+ 1 / n ℚ.+ + 1 / (2 ℕ.* n)) (+ 1 / (2 ℕ.* k)))
                                                                             (+-congˡ ((+ 1 / (2 ℕ.* k)) ⋆) (⋆-distrib-+ (+ 1 / n) (+ 1 / (2 ℕ.* n))))) ⟩
      (+ 1 / n ℚ.+ + 1 / (2 ℕ.* n) ℚ.+ + 1 / (2 ℕ.* k)) ⋆                 ≤⟨ p≤q⇒p⋆≤q⋆ _ _
                                                                             (ℚP.+-monoˡ-≤ (+ 1 / (2 ℕ.* k)) (ℚP.+-mono-≤
                                                                             (q≤r⇒+p/r≤+p/q 1 (3 ℕ.* k) n n≥3k)
                                                                             (q≤r⇒+p/r≤+p/q 1 (2 ℕ.* (3 ℕ.* k)) (2 ℕ.* n) (ℕP.*-monoʳ-≤ 2 n≥3k)))) ⟩
      (+ 1 / (3 ℕ.* k) ℚ.+ + 1 / (2 ℕ.* (3 ℕ.* k)) ℚ.+ + 1 / (2 ℕ.* k)) ⋆ ≈⟨ ⋆-cong (ℚ.*≡* (solve 1 (λ k ->
                                                                             ((con (+ 1) :* (con (+ 2) :* (con (+ 3) :* k)) :+
                                                                             con (+ 1) :* (con (+ 3) :* k)) :* (con (+ 2) :* k) :+
                                                                             (con (+ 1) :* (con (+ 3) :* k :* (con (+ 2) :* (con (+ 3) :* k))))) :* k :=
                                                                             con (+ 1) :* ((con (+ 3) :* k :* (con (+ 2) :* (con (+ 3) :* k))) :* (con (+ 2) :* k)))
                                                                             refl (+ k))) ⟩
      (+ 1 / k) ⋆                                                          ∎}})

