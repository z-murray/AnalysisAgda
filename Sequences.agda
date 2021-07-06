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
         (∀ k -> {k≢0 : k ≢0} -> ∃ λ Nₖ-1 -> (∀ n -> n ℕ.≥ suc (Nₖ-1) -> ∣ f n - x₀ ∣ ≤ ((+ 1 / k) {k≢0}) ⋆)) ->
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
                                                         let k = suc k-1; N₁ = suc (proj₁ (f→x (2 ℕ.* k))); N₂ = suc (proj₁ ((f→y (2 ℕ.* k))))
                                                               ; N = N₁ ℕ.⊔ N₂ in begin
  ∣ x - y ∣                                 ≈⟨ ∣-∣-cong (≃-symm (+-congˡ (- y)
                                               (≃-trans (+-congʳ x (+-inverseʳ (f N))) (+-identityʳ x)))) ⟩
  ∣ x + (f N - f N) - y ∣                   ≈⟨ ∣-∣-cong (ℝsolve 4 (λ x -y fN -fN ->
                                               x +: (fN +: -fN) +: -y =: (x +: -fN) +: (fN +: -y))
                                               ≃-refl x (- y) (f N) (- f N)) ⟩
  ∣ (x - f N) + (f N - y) ∣                 ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (x - f N) (f N - y) ⟩
  ∣ x - f N ∣ + ∣ f N - y ∣                 ≤⟨ +-mono-≤
                                              (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (f N) x) (proj₂ (f→x (2 ℕ.* k)) N (ℕP.m≤m⊔n N₁ N₂)))
                                              (proj₂ (f→y (2 ℕ.* k)) N (ℕP.m≤n⊔m N₁ N₂)) ⟩
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

data _hasBound_ : REL (ℕ -> ℝ) ℝ 0ℓ where
  bound* : {f : ℕ -> ℝ} -> {r : ℝ} -> (∀ n -> {n ≢0} -> ∣ f n ∣ ≤ r) -> f hasBound r 


_isBounded : (ℕ -> ℝ) -> Set
f isBounded = ∃ λ r -> f hasBound r

{-
Taking the max over a sequence instead of over a list for convenience.
It seems to make it easier to take the max over a list of a variable length n, since I don't
think we can write x₁ :: x₂ :: ... :: xₙ :: nil in Agda. 
For an example of this, see the convergent⇒bounded proof, particularly the part where M is defined.
-}
max : (ℕ -> ℝ) -> (n : ℕ) -> {n ≢0} -> ℝ
max f 1 = f 1
max f (suc (suc n-2)) = max f (suc n-2) ⊔ f (suc (suc n-2))

m≤n⇒maxfm≤maxfn : ∀ (f : ℕ -> ℝ) -> ∀ m n -> {m≢0 : m ≢0} -> {n≢0 : n ≢0} -> m ℕ.≤ n -> max f m {m≢0} ≤ max f n {n≢0}
m≤n⇒maxfm≤maxfn f (suc m-1) (suc n-1) m≤n with ≤⇒≡∨< (suc m-1) (suc n-1) m≤n
... | inj₁ refl = ≤-refl
... | inj₂ (ℕ.s≤s m-1<n-1) = ≤-trans (m≤n⇒maxfm≤maxfn f (suc m-1) n-1 {_} {n-1≢0} m-1<n-1) (lem n-1 {n-1≢0})
  where
    n-1≢0 : n-1 ≢0
    n-1≢0 = 0<n⇒n≢0 n-1 (ℕP.<-transˡ (ℕP.0<1+n {m-1}) m-1<n-1)

    lem : ∀ k -> {k≢0 : k ≢0} -> max f k {k≢0} ≤ max f (suc k)
    lem 1 = x≤x⊔y (f 1) (f 2)
    lem (suc (suc k-2)) = let k-1 = suc k-2; k = suc k-1; k+1 = suc k in
                          x≤x⊔y (max f k-1 ⊔ f k) (f k+1)

max-property : ∀ (f : ℕ -> ℝ) -> ∀ m n -> {m ≢0} -> {n≢0 : n ≢0} -> m ℕ.≤ n -> f m ≤ max f n {n≢0}
max-property f (suc m-1) (suc n-1) m≤n = ≤-trans (lem (suc m-1)) (m≤n⇒maxfm≤maxfn f (suc m-1) (suc n-1) m≤n)
  where
    lem : ∀ k -> {k≢0 : k ≢0} -> f k ≤ max f k {k≢0}
    lem 1 = ≤-refl
    lem (suc (suc k-2)) = x≤y⊔x (f (suc (suc k-2))) (max f (suc k-2))

convergent⇒bounded : ∀ {f : ℕ -> ℝ} -> f isConvergent -> f isBounded
convergent⇒bounded {f} (x₀ , con* f→x₀) = M , bound* (λ {(suc n-1) -> let n = suc n-1 in
                                          [ (λ N≤n -> ≤-trans (lem n N≤n) (x≤y⊔x (1ℝ + ∣ x₀ ∣) (max ∣f∣ N))) ,
                                            (λ n≤N -> ≤-trans (max-property ∣f∣ n N n≤N) (x≤x⊔y (max ∣f∣ N) (1ℝ + ∣ x₀ ∣))) ]′
                                          (ℕP.≤-total N n)})
  where
    open ≤-Reasoning
    open ℝ-+-*-Solver
    ∣f∣ = λ n -> ∣ f n ∣
    N = suc (proj₁ (f→x₀ 1))
    M = max ∣f∣ N ⊔ (1ℝ + ∣ x₀ ∣)
    lem : ∀ n -> N ℕ.≤ n -> ∣ f n ∣ ≤ 1ℝ + ∣ x₀ ∣
    lem (suc n-1) N≤n = let n = suc n-1 in begin
      ∣ f n ∣               ≈⟨ ∣-∣-cong (≃-symm (≃-trans (+-congʳ (f n) (+-inverseʳ x₀)) (+-identityʳ (f n)))) ⟩
      ∣ f n + (x₀ - x₀) ∣   ≤⟨ ≤-respˡ-≃ (∣-∣-cong (solve 3 (λ fn x₀ -x₀ ->
                               fn :+ -x₀ :+ x₀ := fn :+ (x₀ :+ -x₀))
                               ≃-refl (f n) x₀ (- x₀)))
                               (∣x+y∣≤∣x∣+∣y∣ (f n - x₀) x₀) ⟩
      ∣ f n - x₀ ∣ + ∣ x₀ ∣ ≤⟨ +-monoˡ-≤ ∣ x₀ ∣ (proj₂ (f→x₀ 1) n N≤n) ⟩
      1ℝ + ∣ x₀ ∣            ∎

data _isCauchy : (ℕ -> ℝ) -> Set where
  cauchy* : {f : ℕ -> ℝ} ->
            (∀ k -> {k≢0 : k ≢0} -> ∃ λ Mₖ -> Mₖ ≢0 × ∀ m n -> m ℕ.≥ Mₖ -> n ℕ.≥ Mₖ ->
                    ∣ f m - f n ∣ ≤ (+ 1 / k) {k≢0} ⋆) -> f isCauchy

convergent⇒cauchy : ∀ {f : ℕ -> ℝ} -> f isConvergent -> f isCauchy
convergent⇒cauchy {f} (x₀ , con* f→x₀) = cauchy* (λ {(suc k-1) ->
                                         let k = suc k-1; N₂ₖ = suc (proj₁ (f→x₀ (2 ℕ.* k))); Mₖ = suc N₂ₖ in
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
                                              (proj₂ (f→x₀ (2 ℕ.* k)) m (ℕP.≤-trans (ℕP.n≤1+n N₂ₖ) m≥Mₖ))
                                              (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (f n) x₀)
                                                         (proj₂ (f→x₀ (2 ℕ.* k)) n (ℕP.≤-trans (ℕP.n≤1+n N₂ₖ) n≥Mₖ))) ⟩
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
    f→y = con* (λ {(suc k-1) -> ℕ.pred (N k-1) ,
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

xₙ+yₙ→x₀+y₀ : ∀ {xs ys : ℕ -> ℝ} -> (xₙ→x₀ : xs isConvergent) -> (yₙ→y₀ : ys isConvergent) ->
              (λ n -> xs n + ys n) ConvergesTo (proj₁ xₙ→x₀ + proj₁ yₙ→y₀)
xₙ+yₙ→x₀+y₀ {xs} {ys} (x₀ , con* xₙ→x₀) (y₀ , con* yₙ→y₀) = con* (λ {(suc k-1) ->
                 let k = suc k-1; N₁ = suc (proj₁ (xₙ→x₀ (2 ℕ.* k))); N₂ = suc (proj₁ (yₙ→y₀ (2 ℕ.* k))); N = N₁ ℕ.⊔ N₂ in
                 ℕ.pred N , λ {(suc n-1) N≤n -> let n = suc n-1; xₙ = xs n; yₙ = ys n in begin
  ∣ xₙ + yₙ - (x₀ + y₀) ∣                   ≈⟨ ∣-∣-cong (+-congʳ (xₙ + yₙ) (neg-distrib-+ x₀ y₀)) ⟩
  ∣ xₙ + yₙ + (- x₀ - y₀) ∣                 ≈⟨ ∣-∣-cong (ℝsolve 4 (λ xₙ yₙ -x₀ -y₀ ->
                                               xₙ +: yₙ +: (-x₀ +: -y₀) =: xₙ +: -x₀ +: (yₙ +: -y₀))
                                               ≃-refl xₙ yₙ (- x₀) (- y₀)) ⟩
  ∣ xₙ - x₀ + (yₙ - y₀) ∣                   ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (xₙ - x₀) (yₙ - y₀) ⟩
  ∣ xₙ - x₀ ∣ + ∣ yₙ - y₀ ∣                 ≤⟨ +-mono-≤
                                               (proj₂ (xₙ→x₀ (2 ℕ.* k)) n (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) N≤n))
                                               (proj₂ (yₙ→y₀ (2 ℕ.* k)) n (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) N≤n)) ⟩
  (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-trans
                                               (≃-symm (⋆-distrib-+ (+ 1 / (2 ℕ.* k)) (+ 1 / (2 ℕ.* k))))
                                               (⋆-cong (ℚ.*≡* (solve 1 (λ k ->
                                               (con (+ 1) :* (con (+ 2) :* k) :+ con (+ 1) :* (con (+ 2) :* k)) :* k :=
                                               con (+ 1) :* (con (+ 2) :* k :* (con (+ 2) :* k)))
                                               refl (+ k)))) ⟩
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

_·_ : (n : ℕ) -> {n ≢0} -> ℝ -> ℝ
1 · x = x
suc (suc n) · x = (suc n) · x + x 

x≤Kx : ∀ x -> x ≤ (+ K x / 1) ⋆
x≤Kx x = nonNeg* (λ {(suc n-1) -> let n = suc n-1 in begin
  ℚ.- (+ 1 / n)                       <⟨ ℚP.negative⁻¹ _ ⟩
  0ℚᵘ                                 <⟨ p<q⇒0<q-p ℚ.∣ seq x (2 ℕ.* n) ∣ (+ K x / 1)
                                         (canonical-strict-upper-bound x (2 ℕ.* n)) ⟩
  + K x / 1 ℚ.- ℚ.∣ seq x (2 ℕ.* n) ∣ ≤⟨ ℚP.+-monoʳ-≤ (+ K x / 1) (
                                         ℚP.neg-mono-≤ (p≤∣p∣ (seq x (2 ℕ.* n)))) ⟩
  + K x / 1 ℚ.- seq x (2 ℕ.* n)        ∎})
  where open ℚP.≤-Reasoning

archimedean-ℝ : ∀ x -> ∃ λ (n-1 : ℕ) -> (+ (suc n-1) / 1) ⋆ > x
archimedean-ℝ x = K x , (begin-strict
  x                     <⟨ <-respˡ-≃ (+-identityˡ x)
                           (+-monoˡ-< x (p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (ℚ.*<* (ℤ.+<+ ℕP.0<1+n)))) ⟩
  1ℝ + x                ≤⟨ +-monoʳ-≤ 1ℝ (x≤Kx x) ⟩
  1ℝ + (+ K x / 1) ⋆    ≈⟨ ≃-trans
                           (≃-symm (⋆-distrib-+ 1ℚᵘ (+ K x / 1)))
                           (⋆-cong (ℚP.≃-reflexive (ℚP./-cong (cong (λ r -> + 1 ℤ.+ r) (ℤP.*-identityʳ (+ K x))) refl _ _))) ⟩
  (+ (suc (K x)) / 1) ⋆  ∎)
  where open ≤-Reasoning

bound⇒boundℕ : ∀ {f : ℕ -> ℝ} -> f isBounded ->
               ∃ λ (M-1 : ℕ) -> ∀ (n : ℕ) -> {n ≢0} -> ∣ f n ∣ < (+ suc (M-1) / 1) ⋆
bound⇒boundℕ {f} (r , (bound* ∣f∣≤r)) = let M = suc (proj₁ (archimedean-ℝ r)) in
                               ℕ.pred M , λ {(suc n-1) -> let n = suc n-1 in begin-strict
  ∣ f n ∣     ≤⟨ ∣f∣≤r n ⟩
  r           <⟨ proj₂ (archimedean-ℝ r) ⟩
  (+ M / 1) ⋆  ∎}
  where open ≤-Reasoning

*-mono-≤ : ∀ {x y z w} -> NonNegative x -> NonNegative z -> x ≤ y -> z ≤ w -> x * z ≤ y * w
*-mono-≤ {x} {y} {z} {w} nonx nonz x≤y z≤w = begin
  x * z ≤⟨ *-monoˡ-≤-nonNeg z≤w nonx ⟩
  x * w ≤⟨ *-monoʳ-≤-nonNeg x≤y (0≤x⇒nonNegx (≤-trans (nonNegx⇒0≤x nonz) z≤w)) ⟩
  y * w  ∎
  where open ≤-Reasoning

⋆-distrib-* : ∀ p q -> (p ℚ.* q) ⋆ ≃ p ⋆ * q ⋆
⋆-distrib-* p q = *≃* (λ {(suc n-1) -> let n = suc n-1 in begin
  ℚ.∣ p ℚ.* q ℚ.- p ℚ.* q ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (p ℚ.* q)) ⟩
  0ℚᵘ                       ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                    ∎})
  where open ℚP.≤-Reasoning

xₙyₙ→x₀y₀ : ∀ {xs ys : ℕ -> ℝ} -> (xₙ→x₀ : xs isConvergent) -> (yₙ→y₀ : ys isConvergent) ->
            (λ n -> (xs n * ys n)) ConvergesTo (proj₁ xₙ→x₀ * proj₁ yₙ→y₀)
xₙyₙ→x₀y₀ {xs} {ys} (x₀ , con* xₙ→x₀) (y₀ , con* yₙ→y₀) = con* (λ {(suc k-1) ->
               let k = suc k-1; archy₀ = archimedean-ℝ ∣ y₀ ∣; N₁ = suc (proj₁ archy₀); boundxₙ = bound⇒boundℕ (convergent⇒bounded (x₀ , con* xₙ→x₀))
                     ; N₂ = suc (proj₁ boundxₙ); m = N₁ ℕ.⊔ N₂; M₁ = suc (proj₁ (xₙ→x₀ (2 ℕ.* m ℕ.* k))); M₂ = suc (proj₁ (yₙ→y₀ (2 ℕ.* m ℕ.* k)))
                     ; Mₖ = M₁ ℕ.⊔ M₂ in ℕ.pred Mₖ , λ {(suc n-1) n≥Mₖ -> let n = suc n-1; xₙ = xs (suc n-1); yₙ = ys (suc n-1) in begin
  ∣ xₙ * yₙ - x₀ * y₀ ∣                               ≈⟨ ∣-∣-cong (≃-symm (+-congˡ (- (x₀ * y₀)) (≃-trans
                                                         (+-congʳ (xₙ * yₙ) (≃-trans
                                                         (≃-trans (≃-symm (*-distribˡ-+ xₙ y₀ (- y₀))) (*-congˡ (+-inverseʳ y₀) ))
                                                         (*-zeroʳ xₙ)))
                                                         (+-identityʳ (xₙ * yₙ))))) ⟩
  ∣ xₙ * yₙ + (xₙ * y₀ + xₙ * (- y₀)) - x₀ * y₀ ∣     ≈⟨ ∣-∣-cong (ℝsolve 4 (λ a b c d -> a +: (b +: c) +: d =: a +: c +: (b +: d))
                                                         ≃-refl (xₙ * yₙ) (xₙ * y₀) (xₙ * (- y₀)) (- (x₀ * y₀))) ⟩ 
  ∣ xₙ * yₙ + xₙ * (- y₀) + (xₙ * y₀ - x₀ * y₀) ∣     ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (xₙ * yₙ + xₙ * (- y₀)) (xₙ * y₀ - x₀ * y₀) ⟩
  ∣ xₙ * yₙ + xₙ * (- y₀) ∣ + ∣ xₙ * y₀ - x₀ * y₀ ∣   ≈⟨ ≃-symm (+-cong
                                                         (∣-∣-cong (*-distribˡ-+ xₙ yₙ (- y₀)))
                                                         (∣-∣-cong (≃-trans (*-distribʳ-+ y₀ xₙ (- x₀))
                                                                            (+-congʳ (xₙ * y₀) (≃-symm (neg-distribˡ-* x₀ y₀)))))) ⟩
  ∣ xₙ * (yₙ - y₀) ∣ + ∣ (xₙ - x₀) * y₀ ∣             ≈⟨ +-cong
                                                         (∣x*y∣≃∣x∣*∣y∣ xₙ (yₙ - y₀))
                                                         (≃-trans (∣x*y∣≃∣x∣*∣y∣ (xₙ - x₀) y₀) (*-comm ∣ xₙ - x₀ ∣ ∣ y₀ ∣)) ⟩
  ∣ xₙ ∣ * ∣ yₙ - y₀ ∣ + ∣ y₀ ∣ * ∣ xₙ - x₀ ∣          ≤⟨ +-mono-≤ {∣ xₙ ∣ * ∣ yₙ - y₀ ∣} {(+ m / 1) ⋆ * (+ 1 / (2 ℕ.* m ℕ.* k)) ⋆}
                                                                  {∣ y₀ ∣ * ∣ xₙ - x₀ ∣} {(+ m / 1) ⋆ * (+ 1 / (2 ℕ.* m ℕ.* k)) ⋆}
                                                         (*-mono-≤ {∣ xₙ ∣} {(+ m / 1) ⋆} {∣ yₙ - y₀ ∣} {(+ 1 / (2 ℕ.* m ℕ.* k)) ⋆}
                                                                   (nonNeg∣x∣ xₙ) (nonNeg∣x∣ (yₙ - y₀))
                                                                   (<⇒≤ (<-≤-trans (proj₂ boundxₙ n) (p≤q⇒p⋆≤q⋆ (+ N₂ / 1) (+ m / 1)
                                                                                   (p≤q⇒p/r≤q/r (+ N₂) (+ m) 1 (ℤ.+≤+ (ℕP.m≤n⊔m N₁ N₂))))))
                                                                   (proj₂ (yₙ→y₀ (2 ℕ.* m ℕ.* k)) n (ℕP.≤-trans (ℕP.m≤n⊔m M₁ M₂) n≥Mₖ)))
                                                         (*-mono-≤ {∣ y₀ ∣} {(+ m / 1) ⋆} {∣ xₙ - x₀ ∣} {(+ 1 / (2 ℕ.* m ℕ.* k)) ⋆}
                                                                   (nonNeg∣x∣ y₀) (nonNeg∣x∣ (xₙ - x₀))
                                                                   (<⇒≤ (<-≤-trans (proj₂ archy₀) (p≤q⇒p⋆≤q⋆ (+ N₁ / 1) (+ m / 1)
                                                                                   (p≤q⇒p/r≤q/r (+ N₁) (+ m) 1 (ℤ.+≤+ (ℕP.m≤m⊔n N₁ N₂))))))
                                                                   (proj₂ (xₙ→x₀ (2 ℕ.* m ℕ.* k)) n (ℕP.≤-trans (ℕP.m≤m⊔n M₁ M₂) n≥Mₖ))) ⟩
  (+ m / 1) ⋆ * (+ 1 / (2 ℕ.* m ℕ.* k)) ⋆ +
  (+ m / 1) ⋆ * (+ 1 / (2 ℕ.* m ℕ.* k)) ⋆             ≈⟨ ≃-symm (≃-trans (≃-trans
                                                         (⋆-distrib-* (+ m / 1) (+ 1 / (2 ℕ.* m ℕ.* k) ℚ.+ + 1 / (2 ℕ.* m ℕ.* k)))
                                                         (*-congˡ (⋆-distrib-+ (+ 1 / (2 ℕ.* m ℕ.* k)) (+ 1 / (2 ℕ.* m ℕ.* k)))))
                                                         (*-distribˡ-+ ((+ m / 1) ⋆) ((+ 1 / (2 ℕ.* m ℕ.* k)) ⋆) ((+ 1 / (2 ℕ.* m ℕ.* k)) ⋆))) ⟩
  (+ m / 1 ℚ.* (+ 1 / (2 ℕ.* m ℕ.* k) ℚ.+
  + 1 / (2 ℕ.* m ℕ.* k))) ⋆                           ≈⟨ ⋆-cong (ℚ.*≡* (solve 2 (λ m k ->
                                                         (m :* (con (+ 1) :* (con (+ 2) :* m :* k) :+ con (+ 1) :* (con (+ 2) :* m :* k))) :* k :=
                                                         con (+ 1) :* (con (+ 1) :* (con (+ 2) :* m :* k :* (con (+ 2) :* m :* k))))
                                                         refl (+ m) (+ k))) ⟩
  (+ 1 / k) ⋆                                           ∎}})
  where
    open ≤-Reasoning
    open ℝ-+-*-Solver using ()
      renaming
        ( solve to ℝsolve
        ; _:+_  to _+:_
        ; _:=_  to _=:_
        )
    open ℤ-Solver.+-*-Solver

{-
-1/k ≤ xₙ⊔yₙ - x₀⊔y₀ ≤ 1/k?

xₙ⊔yₙ - x₀⊔y₀ ≤ ∣x - x₀∣ ⊔ ∣y - y₀∣ ?
xₙ⊔yₙ - x₀⊔y₀ ≤ xₙ⊔yₙ - x₀
              ≤ 

Not sure how to prove this constructively yet. Can't rely on xₙ ⊔ yₙ = xₙ or yₙ since that's not valid.
-}
xₙ⊔yₙ→x₀⊔y₀ : ∀ {xs ys : ℕ -> ℝ} -> (xₙ→x₀ : xs isConvergent) -> (yₙ→y₀ : ys isConvergent) ->
              (λ n -> xs n ⊔ ys n) ConvergesTo (proj₁ xₙ→x₀ ⊔ proj₁ yₙ→y₀)
xₙ⊔yₙ→x₀⊔y₀ {xs} {ys} (x₀ , con* xₙ→x₀) (y₀ , con* yₙ→y₀) = con* (λ {(suc k-1) ->
                      let k = suc k-1; N₁ = suc (proj₁ (xₙ→x₀ k)); N₂ = suc (proj₁ (yₙ→y₀ k)); N = N₁ ℕ.⊔ N₂ in
                      N , λ {(suc n-1) n≥N -> let n = suc n-1 in {!!}}})
  where open ≤-Reasoning

xₙ≃c⇒xₙ→c : ∀ {xs : ℕ -> ℝ} -> ∀ {c : ℝ} -> (∀ n -> {n ≢0} -> xs n ≃ c) -> xs ConvergesTo c
xₙ≃c⇒xₙ→c {xs} {c} hyp = con* (λ {(suc k-1) -> let k = suc k-1 in 0 , λ {(suc n-1) n≥1 -> let n = suc n-1 in begin
  ∣ xs n - c ∣ ≈⟨ ∣-∣-cong (+-congˡ (- c) (hyp n)) ⟩
  ∣ c - c ∣    ≈⟨ ≃-trans (∣-∣-cong (+-inverseʳ c)) (≃-reflexive (λ n -> ℚP.≃-refl)) ⟩
  0ℝ           ≤⟨ p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 1 / k) (ℚP.nonNegative⁻¹ _) ⟩
  (+ 1 / k) ⋆   ∎}})
  where open ≤-Reasoning

xₙ≄0∧x₀≄0⇒xₙ⁻¹→x₀⁻¹ : ∀ {xs : ℕ -> ℝ} -> ∀ {x₀ : ℝ} -> xs ConvergesTo x₀ -> (xₙ≄0 : ∀ n -> xs n ≄0) -> (x₀≄0 : x₀ ≄0) ->
                      (λ n -> (xs n ⁻¹) (xₙ≄0 n)) ConvergesTo (x₀ ⁻¹) x₀≄0
xₙ≄0∧x₀≄0⇒xₙ⁻¹→x₀⁻¹ {xs} {x₀} (con* xₙ→x₀) xₙ≄0 x₀≄0 = con* λ {(suc k-1) -> {!!}}

xₙ≤yₙ⇒x₀≤y₀ : ∀ {xs ys : ℕ -> ℝ} -> ∀ {x₀ y₀ : ℝ} -> xs ConvergesTo x₀ -> ys ConvergesTo y₀ ->
              (∀ n -> {n ≢0} -> xs n ≤ ys n) -> x₀ ≤ y₀
xₙ≤yₙ⇒x₀≤y₀ {xs} {ys} {x₀} {y₀} (con* xₙ→x₀) (con* yₙ→y₀) xₙ≤yₙ = nonNeg-cong {!!} (begin {!!})
  where open ≤-Reasoning
