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
open import Function.Structures {_} {_} {_} {_} {ℕ} _≡_ {ℕ} _≡_

open ℚᵘ
open ℝ
--∀k∈ℕ ∃Nₖ∈ℕ ∀n≥Nₖ ∣ fₙ - x₀ ∣ ≤ k⁻¹
data _ConvergesTo_ : REL (ℕ -> ℝ) ℝ 0ℓ where
  con* : {f : ℕ -> ℝ} -> {x₀ : ℝ} ->
         (∀ k -> {k≢0 : k ≢0} -> ∃ λ Nₖ-1 -> (∀ n -> n ℕ.≥ suc (Nₖ-1) -> ∣ f n - x₀ ∣ ≤ ((+ 1 / k) {k≢0}) ⋆)) ->
         f ConvergesTo x₀

_isConvergent : (ℕ -> ℝ) -> Set
f isConvergent = ∃ λ x₀ -> f ConvergesTo x₀

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

xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ : ∀ {xs ys : ℕ -> ℝ} -> (∀ n -> {n ≢0} -> xs n ≃ ys n) -> (x→x₀ : xs isConvergent) -> ys ConvergesTo proj₁ x→x₀
xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ {xs} {ys} xₙ≃yₙ (x₀ , con* x→x₀) = con* (λ {(suc k-1) -> let k = suc k-1 in
                                                     proj₁ (x→x₀ k) , λ {(suc n-1) n≥N -> let n = suc n-1 in begin
  ∣ ys n - x₀ ∣ ≈⟨ ∣-∣-cong (+-congˡ (- x₀) (≃-symm (xₙ≃yₙ n))) ⟩
  ∣ xs n - x₀ ∣ ≤⟨ proj₂ (x→x₀ k) n n≥N ⟩
  (+ 1 / k) ⋆    ∎}})
  where open ≤-Reasoning

xₙ→x∧x≃y⇒xₙ→y : ∀ {xs : ℕ -> ℝ} -> ∀ {x y : ℝ} -> xs ConvergesTo x -> x ≃ y -> xs ConvergesTo y
xₙ→x∧x≃y⇒xₙ→y {xs} {x} {y} (con* xₙ→x) x≃y = con* (λ {(suc k-1) -> let k = suc k-1; Nₖ = suc (proj₁ (xₙ→x k)) in
                                             ℕ.pred Nₖ , λ n n≥Nₖ -> begin
  ∣ xs n - y ∣ ≈⟨ ∣-∣-cong (+-congʳ (xs n) (-‿cong (≃-symm x≃y))) ⟩
  ∣ xs n - x ∣ ≤⟨ proj₂ (xₙ→x k) n n≥Nₖ ⟩
  (+ 1 / k) ⋆   ∎})
  where open ≤-Reasoning

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
            (∀ k -> {k≢0 : k ≢0} -> ∃ λ Mₖ-1 -> ∀ m n -> m ℕ.≥ suc Mₖ-1 -> n ℕ.≥ suc Mₖ-1 ->
                    ∣ f m - f n ∣ ≤ (+ 1 / k) {k≢0} ⋆) -> f isCauchy

convergent⇒cauchy : ∀ {f : ℕ -> ℝ} -> f isConvergent -> f isCauchy
convergent⇒cauchy {f} (x₀ , con* f→x₀) = cauchy* (λ {(suc k-1) ->
                                         let k = suc k-1; N₂ₖ = suc (proj₁ (f→x₀ (2 ℕ.* k))); Mₖ = suc N₂ₖ in
                                         ℕ.pred Mₖ , λ {(suc m-1) (suc n-1) m≥Mₖ n≥Mₖ -> let m = suc m-1 ; n = suc n-1 in
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
    N k-1 = let k = suc k-1; M₂ₖ = suc (proj₁ (fCauchy (2 ℕ.* k))) in
                  suc ((3 ℕ.* k) ℕ.⊔ M₂ₖ)

    Nₖ-prop : ∀ k-1 -> ∀ m n -> m ℕ.≥ N k-1 -> n ℕ.≥ N k-1 -> ∣ f m - f n ∣ ≤ (+ 1 / (2 ℕ.* (suc k-1))) ⋆
    Nₖ-prop k-1 = λ {(suc m-1) (suc n-1) m≥N n≥N -> let k = suc k-1; m = suc m-1; n = suc n-1; M₂ₖ = suc (proj₁ (fCauchy (2 ℕ.* k))) in
                  proj₂ (fCauchy (2 ℕ.* k)) m n
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
                                     ; n≥3k = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n (3 ℕ.* k) (suc (proj₁ (fCauchy (2 ℕ.* k))))) (ℕP.n≤1+n (ℕ.pred (N k-1)))) n≥Nₖ in begin
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
                                                                                          (ℕP.≤-trans (ℕP.m≤m⊔n (3 ℕ.* n) (suc (proj₁ (fCauchy (2 ℕ.* n)))))
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

{-_·_ : (n : ℕ) -> {n ≢0} -> ℝ -> ℝ
1 · x = x
suc (suc n) · x = (suc n) · x + x -}

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

abstract
  fast-archimedean-ℝ : ∀ x -> ∃ λ (n-1 : ℕ) -> (+ (suc n-1) / 1) ⋆ > x
  fast-archimedean-ℝ = archimedean-ℝ

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

--⋆-distrib-* : ∀ p q -> (p ℚ.* q) ⋆ ≃ p ⋆ * q ⋆
{-⋆-distrib-* p q = *≃* (λ {(suc n-1) -> let n = suc n-1 in begin
  ℚ.∣ p ℚ.* q ℚ.- p ℚ.* q ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (p ℚ.* q)) ⟩
  0ℚᵘ                       ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                    ∎})
  where open ℚP.≤-Reasoning-}

-xₙ→-x₀ : ∀ {xs : ℕ -> ℝ} -> (x→x₀ : xs isConvergent) -> (λ n -> - xs n) ConvergesTo (- (proj₁ x→x₀))
-xₙ→-x₀ {xs} (x₀ , con* x→x₀) = con* (λ {(suc k-1) -> let k = suc k-1 in
                                proj₁ (x→x₀ k) , λ {(suc n-1) n≥N -> let n = suc n-1 in begin
  ∣ - xs n - (- x₀) ∣ ≈⟨ ∣-∣-cong (≃-symm (neg-distrib-+ (xs n) (- x₀))) ⟩
  ∣ - (xs n - x₀) ∣   ≈⟨ ∣-x∣≃∣x∣ ⟩
  ∣ xs n - x₀ ∣       ≤⟨ proj₂ (x→x₀ k) n n≥N ⟩
  (+ 1 / k) ⋆          ∎}})
  where open ≤-Reasoning

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

xₙ≃c⇒xₙ→c : ∀ {xs : ℕ -> ℝ} -> ∀ {c : ℝ} -> (∀ n -> {n ≢0} -> xs n ≃ c) -> xs ConvergesTo c
xₙ≃c⇒xₙ→c {xs} {c} hyp = con* (λ {(suc k-1) -> let k = suc k-1 in 0 , λ {(suc n-1) n≥1 -> let n = suc n-1 in begin
  ∣ xs n - c ∣ ≈⟨ ∣-∣-cong (+-congˡ (- c) (hyp n)) ⟩
  ∣ c - c ∣    ≈⟨ ≃-trans (∣-∣-cong (+-inverseʳ c)) (≃-reflexive (λ n -> ℚP.≃-refl)) ⟩
  0ℝ           ≤⟨ p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 1 / k) (ℚP.nonNegative⁻¹ _) ⟩
  (+ 1 / k) ⋆   ∎}})
  where open ≤-Reasoning

x<y∧posx,y⇒y⁻¹<x⁻¹ : ∀ {x y} -> x < y -> (x≄0 : x ≄0) -> (y≄0 : y ≄0) -> Positive x -> Positive y ->
                     (y ⁻¹) y≄0 < (x ⁻¹) x≄0
x<y∧posx,y⇒y⁻¹<x⁻¹ {x} {y} x<y x≄0 y≄0 posx posy = let x⁻¹ = (x ⁻¹) x≄0; y⁻¹ = (y ⁻¹) y≄0 in
                   begin-strict
  y⁻¹             ≈⟨ ≃-symm (≃-trans (*-congʳ (*-inverseʳ x x≄0)) (*-identityˡ y⁻¹)) ⟩
  x * x⁻¹ * y⁻¹   <⟨ *-monoˡ-<-pos {y⁻¹} (posx⇒posx⁻¹ {y} y≄0 posy)
                     (*-monoˡ-<-pos {x⁻¹} (posx⇒posx⁻¹ {x} x≄0 posx) x<y) ⟩
  y * x⁻¹ * y⁻¹   ≈⟨ ≃-trans (*-congʳ (*-comm y x⁻¹)) (*-assoc x⁻¹ y y⁻¹) ⟩
  x⁻¹ * (y * y⁻¹) ≈⟨ ≃-trans (*-congˡ (*-inverseʳ y y≄0)) (*-identityʳ x⁻¹) ⟩
  x⁻¹              ∎
  where open ≤-Reasoning

<⇒≱ : _<_ ⇒ _≱_
<⇒≱ {x} {y} (pos* (n-1 , x<y)) (nonNeg* x≥y) = let n = suc n-1 in ℚP.<-irrefl-≡ refl (begin-strict
  + 1 / n                                         <⟨ x<y ⟩
  seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)             ≈⟨ ℚP.≃-sym (ℚP.neg-involutive (seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n))) ⟩
  ℚ.- (ℚ.- (seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n))) ≈⟨ solve 2 (λ x y -> :- (:- (y :- x)) := :- (x :- y))
                                                     ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)) ⟩
  ℚ.- (seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n))       ≤⟨ ℚP.neg-mono-≤ (x≥y n) ⟩
  ℚ.- (ℚ.- (+ 1 / n))                             ≈⟨ ℚP.neg-involutive (+ 1 / n) ⟩
  + 1 / n                                          ∎)
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver

<-irrefl : Irreflexive _≃_ _<_
<-irrefl {x} {y} (*≃* x≃y) (pos* (n-1 , x<y)) = let n = suc n-1 in ℚP.<-irrefl ℚP.≃-refl (begin-strict
  + 1 / n                                   <⟨ x<y ⟩
  seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)       ≤⟨ p≤∣p∣ (seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)) ⟩
  ℚ.∣ seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n) ∣ ≈⟨ ∣p-q∣≃∣q-p∣ (seq y (2 ℕ.* n)) (seq x (2 ℕ.* n)) ⟩
  ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ≤⟨ x≃y (2 ℕ.* n) ⟩
  + 2 / (2 ℕ.* n)                           ≈⟨ ℚ.*≡* (sym (ℤP.*-identityˡ (+ 2 ℤ.* + n))) ⟩
  + 1 / n                                    ∎)
  where open ℚP.≤-Reasoning

p⋆≄0⇒∣↥p∣≢0 : ∀ p -> (p ⋆) ≄0 -> ℤ.∣ ↥ p ∣ ≢0
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ (+_ zero) d-1) (inj₁ p⋆<0) = let d = suc d-1 in <-irrefl (≃-reflexive (λ {(suc n-1) -> ℚ.*≡* (sym (ℤP.*-zeroˡ (+ d)))})) p⋆<0
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ +[1+ n ] denominator-2) (inj₁ p⋆<0) = _
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ (-[1+_] n) denominator-2) (inj₁ p⋆<0) = _
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ (+_ zero) d-1) (inj₂ 0<p⋆) = let d = suc d-1 in <-irrefl (≃-reflexive (λ {(suc n-1) -> ℚ.*≡* (ℤP.*-zeroˡ (+ d))})) 0<p⋆
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ +[1+ n ] denominator-2) (inj₂ 0<p⋆) = _
p⋆≄0⇒∣↥p∣≢0 (mkℚᵘ (-[1+_] n) denominator-2) (inj₂ 0<p⋆) = _

∣↥p∣≢0⇒p⋆≄0 : ∀ p -> ℤ.∣ ↥ p ∣ ≢0 -> (p ⋆) ≄0
∣↥p∣≢0⇒p⋆≄0 (mkℚᵘ +[1+ n ] d-1) ∣↥p∣≢0 = inj₂ (p<q⇒p⋆<q⋆ 0ℚᵘ (+[1+ n ] / (suc d-1)) (ℚP.positive⁻¹ _))
∣↥p∣≢0⇒p⋆≄0 (mkℚᵘ (-[1+_] n) d-1) ∣↥p∣≢0 = inj₁ (p<q⇒p⋆<q⋆ (-[1+_] n / (suc d-1)) 0ℚᵘ (ℚP.negative⁻¹ _))

⁻¹-involutive : ∀ {x} -> (x≄0 : x ≄0) -> (x⁻¹≄0 : (x ⁻¹) x≄0 ≄0) ->
                (((x ⁻¹) x≄0) ⁻¹) x⁻¹≄0 ≃ x
⁻¹-involutive {x} x≄0 x⁻¹≄0 = let x⁻¹ = (x ⁻¹) x≄0 in ≃-symm (⁻¹-unique x x⁻¹ x⁻¹≄0 (*-inverseʳ x x≄0))

⁻¹-involutive-default : ∀ {x} -> (x≄0 : x ≄0) ->
                (((x ⁻¹) x≄0) ⁻¹) ([ (λ x<0 -> inj₁ (x<0⇒x⁻¹<0 {x} x≄0 x<0)) , (λ 0<x -> inj₂ (0<x⇒0<x⁻¹ {x} x≄0 0<x))]′ x≄0) ≃ x
⁻¹-involutive-default {x} x≄0 = ⁻¹-involutive {x} x≄0 ([ (λ x<0 -> inj₁ (x<0⇒x⁻¹<0 {x} x≄0 x<0)) , (λ 0<x -> inj₂ (0<x⇒0<x⁻¹ {x} x≄0 0<x))]′ x≄0)

⋆-distrib-⁻¹ : ∀ p -> (p⋆≄0 : (p ⋆) ≄0) -> ((p ⋆) ⁻¹) p⋆≄0 ≃ ((ℚ.1/ p) {p⋆≄0⇒∣↥p∣≢0 p p⋆≄0}) ⋆
⋆-distrib-⁻¹ p p⋆≄0 = let p⁻¹ = (ℚ.1/ p) {p⋆≄0⇒∣↥p∣≢0 p p⋆≄0}; p⋆⁻¹ = ((p ⋆) ⁻¹) p⋆≄0 in
                      ≃-symm (⁻¹-unique (p⁻¹ ⋆) (p ⋆) p⋆≄0 (begin
  p⁻¹ ⋆ * p ⋆   ≈⟨ ≃-symm (⋆-distrib-* p⁻¹ p) ⟩
  (p⁻¹ ℚ.* p) ⋆ ≈⟨ ⋆-cong (ℚP.*-inverseˡ p {p⋆≄0⇒∣↥p∣≢0 p p⋆≄0}) ⟩
  1ℝ             ∎))
  where open ≃-Reasoning

0≤y-x⇒x≤y : ∀ {x y} -> 0ℝ ≤ y - x -> x ≤ y
0≤y-x⇒x≤y {x} {y} 0≤y-x = nonNeg-cong (≃-trans (+-congʳ (y - x) (≃-symm 0≃-0)) (+-identityʳ (y - x))) 0≤y-x

x≤z∧y≤z⇒x⊔y≤z : ∀ {x y z} -> x ≤ z -> y ≤ z -> x ⊔ y ≤ z
x≤z∧y≤z⇒x⊔y≤z {x} {y} {z} x≤z y≤z = lemma-2-8-2-onlyif lem
  where
    open ℚP.≤-Reasoning
    lem : ∀ n -> {n≢0 : n ≢0} -> ∃ λ Nₙ -> Nₙ ≢0 × (∀ m -> m ℕ.≥ Nₙ -> seq (z - (x ⊔ y)) m ℚ.≥ ℚ.- (+ 1 / n) {n≢0})
    lem (suc n-1) = N , _ , λ {(suc m-1) m≥N -> let m = suc m-1 in
                  [ left m m≥N , right m m≥N ]′ (ℚP.≤-total (seq y (2 ℕ.* m)) (seq x (2 ℕ.* m)))}
      where
        n = suc n-1
        fromx≤z = fast-lemma-2-8-2-if x≤z n
        fromy≤z = fast-lemma-2-8-2-if y≤z n
        N₁ = proj₁ fromx≤z
        N₂ = proj₁ fromy≤z
        N = suc (N₁ ℕ.⊔ N₂)

        left : ∀ m -> m ℕ.≥ N -> seq y (2 ℕ.* m) ℚ.≤ seq x (2 ℕ.* m) ->
               seq (z - (x ⊔ y)) m ℚ.≥ ℚ.- (+ 1 / n)
        left (suc m-1) m≥N y₂ₘ≤x₂ₘ = let m = suc m-1 in begin
          ℚ.- (+ 1 / n)                             ≤⟨ proj₂ (proj₂ fromx≤z) m
                                                       (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.n≤1+n (N₁ ℕ.⊔ N₂))) m≥N) ⟩
          seq z (2 ℕ.* m) ℚ.- seq x (2 ℕ.* m)       ≈⟨ ℚP.+-congʳ (seq z (2 ℕ.* m))
                                                       (ℚP.-‿cong (ℚP.≃-sym (ℚP.p≥q⇒p⊔q≃p y₂ₘ≤x₂ₘ))) ⟩
          seq z (2 ℕ.* m) ℚ.- seq (x ⊔ y) (2 ℕ.* m)  ∎

        right : ∀ m -> m ℕ.≥ N -> seq x (2 ℕ.* m) ℚ.≤ seq y (2 ℕ.* m) ->
               seq (z - (x ⊔ y)) m ℚ.≥ ℚ.- (+ 1 / n)
        right (suc m-1) m≥N x₂ₘ≤y₂ₘ = let m = suc m-1 in begin
          ℚ.- (+ 1 / n)                             ≤⟨ proj₂ (proj₂ fromy≤z) m
                                                       (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.n≤1+n (N₁ ℕ.⊔ N₂))) m≥N) ⟩
          seq z (2 ℕ.* m) ℚ.- seq y (2 ℕ.* m)       ≈⟨ ℚP.+-congʳ (seq z (2 ℕ.* m))
                                                       (ℚP.-‿cong (ℚP.≃-sym (ℚP.p≤q⇒p⊔q≃q x₂ₘ≤y₂ₘ))) ⟩
          seq z (2 ℕ.* m) ℚ.- seq (x ⊔ y) (2 ℕ.* m)  ∎

-[x-y]≃y-x : ∀ x y -> - (x - y) ≃ y - x
-[x-y]≃y-x x y = begin-equality
  - (x - y)   ≈⟨ neg-distrib-+ x (- y) ⟩
  - x - (- y) ≈⟨ +-congʳ (- x) (neg-involutive y) ⟩
  - x + y     ≈⟨ +-comm (- x) y ⟩
  y - x        ∎
  where open ≤-Reasoning

∣∣x∣-∣y∣∣≤∣x-y∣ : ∀ x y -> ∣ ∣ x ∣ - ∣ y ∣ ∣ ≤ ∣ x - y ∣
∣∣x∣-∣y∣∣≤∣x-y∣ x y = ≤-respˡ-≃ (≃-symm (∣x∣≃x⊔-x (∣ x ∣ - ∣ y ∣))) (x≤z∧y≤z⇒x⊔y≤z (left x y) right)
  where
    open ≤-Reasoning
    left : ∀ x y -> ∣ x ∣ - ∣ y ∣ ≤ ∣ x - y ∣
    left x y = begin
      ∣ x ∣ - ∣ y ∣             ≈⟨ +-congˡ (- ∣ y ∣) (∣-∣-cong (≃-symm
                                  (≃-trans (+-congʳ x (+-inverseˡ y)) (+-identityʳ x)))) ⟩
      ∣ x + (- y + y) ∣ - ∣ y ∣ ≤⟨ +-monoˡ-≤ (- ∣ y ∣)
                                  (≤-respˡ-≃ (∣-∣-cong (+-assoc x (- y) y)) (∣x+y∣≤∣x∣+∣y∣ (x - y) y)) ⟩
      ∣ x - y ∣ + ∣ y ∣ - ∣ y ∣ ≈⟨ ≃-trans (≃-trans
                                   (+-assoc ∣ x - y ∣ ∣ y ∣ (- ∣ y ∣))
                                   (+-congʳ ∣ x - y ∣ (+-inverseʳ ∣ y ∣)))
                                   (+-identityʳ ∣ x - y ∣) ⟩
      ∣ x - y ∣                  ∎

    right : - (∣ x ∣ - ∣ y ∣) ≤ ∣ x - y ∣
    right = begin
      - (∣ x ∣ - ∣ y ∣) ≈⟨ -[x-y]≃y-x ∣ x ∣ ∣ y ∣ ⟩
      ∣ y ∣ - ∣ x ∣     ≤⟨ left y x ⟩
      ∣ y - x ∣         ≈⟨ ∣x-y∣≃∣y-x∣ y x ⟩
      ∣ x - y ∣          ∎

archimedean-ℝ₂ : ∀ {x} -> Positive x -> ∃ λ n-1 -> (+ 1 / (suc n-1)) ⋆ < x
archimedean-ℝ₂ {x} posx = let x≄0 = inj₂ (posx⇒0<x posx); x⁻¹ = (x ⁻¹) x≄0; arch = archimedean-ℝ x⁻¹
                                  ; x⁻¹≄0 = [ (λ x<0 -> inj₁ (x<0⇒x⁻¹<0 {x} x≄0 x<0)) , (λ 0<x -> inj₂ (0<x⇒0<x⁻¹ {x} x≄0 0<x))]′ x≄0
                                  ; n = suc (proj₁ arch) in
                          ℕ.pred n , <-respˡ-≃ (⋆-distrib-⁻¹ (+ n / 1) (∣↥p∣≢0⇒p⋆≄0 (+ n / 1) _))
                          (<-respʳ-≃ {_} {(x⁻¹ ⁻¹) x⁻¹≄0} {x} (⁻¹-involutive-default {x} x≄0)
                          (x<y∧posx,y⇒y⁻¹<x⁻¹ {x⁻¹} {(+ n / 1) ⋆} (proj₂ arch) x⁻¹≄0 (∣↥p∣≢0⇒p⋆≄0 (+ n / 1) _) (posx⇒posx⁻¹ {x} x≄0 posx)
                          (0<x⇒posx (p<q⇒p⋆<q⋆ 0ℚᵘ (+ n / 1) (ℚP.positive⁻¹ _)))))
  where open ≤-Reasoning

abstract
  fast-archimedean-ℝ₂ : ∀ {x} -> Positive x -> ∃ λ n-1 -> (+ 1 / (suc n-1)) ⋆ < x
  fast-archimedean-ℝ₂ = archimedean-ℝ₂

negx,y⇒posx*y : ∀ {x y} -> Negative x -> Negative y -> Positive (x * y)
negx,y⇒posx*y {x} {y} negx negy = pos-cong (begin
  (- x) * (- y) ≈⟨ ≃-symm (neg-distribˡ-* x (- y)) ⟩
  - (x * (- y)) ≈⟨ ≃-symm (-‿cong (neg-distribʳ-* x y)) ⟩
  - (- (x * y)) ≈⟨ neg-involutive (x * y) ⟩
  x * y          ∎)
  (posx,y⇒posx*y negx negy)
  where open ≃-Reasoning

negx∧posy⇒negx*y : ∀ {x y} -> Negative x -> Positive y -> Negative (x * y)
negx∧posy⇒negx*y {x} {y} negx posy = pos-cong (≃-symm (neg-distribˡ-* x y)) (posx,y⇒posx*y negx posy)

x≄0∧y≄0⇒x*y≄0 : ∀ {x y} -> x ≄0 -> y ≄0 -> (x * y) ≄0
x≄0∧y≄0⇒x*y≄0 {x} {y} x≄0 y≄0 = [ [ y<0∧x<0 , 0<y∧x<0 ]′ y≄0 , [ y<0∧0<x , 0<y∧0<x ]′ y≄0 ]′ x≄0
  where
    y<0∧x<0 : y < 0ℝ -> x < 0ℝ -> (x * y) ≄0
    y<0∧x<0 y<0 x<0 = inj₂ (posx⇒0<x (negx,y⇒posx*y (x<0⇒negx x<0) (x<0⇒negx y<0)))

    0<y∧x<0 : 0ℝ < y -> x < 0ℝ -> (x * y) ≄0
    0<y∧x<0 0<y x<0 = inj₁ (negx⇒x<0 (negx∧posy⇒negx*y (x<0⇒negx x<0) (0<x⇒posx 0<y)))

    y<0∧0<x : y < 0ℝ -> 0ℝ < x -> (x * y) ≄0
    y<0∧0<x y<0 0<x = inj₁ (<-respˡ-≃ (*-comm y x) (negx⇒x<0 (negx∧posy⇒negx*y (x<0⇒negx y<0) (0<x⇒posx 0<x))))

    0<y∧0<x : 0ℝ < y -> 0ℝ < x -> (x * y) ≄0
    0<y∧0<x 0<y 0<x = inj₂ (posx⇒0<x (posx,y⇒posx*y (0<x⇒posx 0<x) (0<x⇒posx 0<y)))

nonNegp⇒nonNegp⋆ : ∀ p -> ℚ.NonNegative p -> NonNegative (p ⋆)
nonNegp⇒nonNegp⋆ p nonp = nonNeg* (λ {(suc n-1) -> ℚP.≤-trans (ℚP.nonPositive⁻¹ _) (ℚP.nonNegative⁻¹ nonp)})

{-
Note: We could obviously get ∣x∣ ≄0 from x≄0 (or vice versa). However, taking in the ∣x∣⁻¹≄0 allows the user to use any
proof that ∣x∣⁻¹ ≄0 instead of just the proof given by x≄0. If we have two distinct proofs of x ≄0,
say A and B, then (x ⁻¹) A ≡ (x ⁻¹) B does not hold by reflexivity, and probably doesn't hold in most
cases anyway. So if the user has a different ∣x∣ ≄0 proof they'd have to apply uniqueness of inverses,
which is more labour than supplying the ∣x∣ ≄0 proof since you have to supply a proof that 
((∣ x ∣ ⁻¹) C) * ∣ x ∣ ≃ 1ℝ along with all of the *-cong's used to swap out ∣ x ∣ ⁻¹ A for ∣ x ∣ ⁻¹ C.
-}
∣x∣⁻¹≃∣x⁻¹∣ : ∀ {x} -> (∣x∣≄0 : ∣ x ∣ ≄0) -> (x≄0 : x ≄0) -> (∣ x ∣ ⁻¹) ∣x∣≄0 ≃ ∣ (x ⁻¹) x≄0 ∣
∣x∣⁻¹≃∣x⁻¹∣ {x} ∣x∣≄0 x≄0 = let ∣x∣⁻¹ = (∣ x ∣ ⁻¹) ∣x∣≄0; x⁻¹ = (x ⁻¹) x≄0 in begin
  ∣x∣⁻¹                     ≈⟨ ≃-symm (*-identityʳ ∣x∣⁻¹) ⟩
  ∣x∣⁻¹ * 1ℝ                ≈⟨ *-congˡ {∣x∣⁻¹} (≃-symm (≃-trans (∣-∣-cong (*-inverseʳ x x≄0)) (nonNegx⇒∣x∣≃x (nonNegp⇒nonNegp⋆ 1ℚᵘ _)))) ⟩
  ∣x∣⁻¹ * ∣ x * x⁻¹ ∣       ≈⟨ *-congˡ {∣x∣⁻¹} (∣x*y∣≃∣x∣*∣y∣ x x⁻¹) ⟩
  ∣x∣⁻¹ * (∣ x ∣ * ∣ x⁻¹ ∣) ≈⟨ ≃-symm (*-assoc ∣x∣⁻¹ ∣ x ∣ ∣ x⁻¹ ∣) ⟩
  ∣x∣⁻¹ * ∣ x ∣ * ∣ x⁻¹ ∣   ≈⟨ *-congʳ {∣ x⁻¹ ∣} (*-inverseˡ ∣ x ∣ ∣x∣≄0) ⟩
  1ℝ * ∣ x⁻¹ ∣             ≈⟨ *-identityˡ ∣ x⁻¹ ∣ ⟩
  ∣ x⁻¹ ∣                   ∎
  where open ≃-Reasoning

x≄0⇒∣x∣≄0 : ∀ {x} -> x ≄0 -> ∣ x ∣ ≄0
x≄0⇒∣x∣≄0 {x} x≄0 = inj₂ (pos-cong (≃-symm (≃-trans (+-congʳ ∣ x ∣ (≃-symm 0≃-0)) (+-identityʳ ∣ x ∣))) (x≄0⇒pos∣x∣ x≄0))

⁻¹-distrib-* : ∀ {x y} -> (x≄0 : x ≄0) -> (y≄0 : y ≄0) -> (xy≄0 : (x * y) ≄0) -> 
               ((x * y) ⁻¹) xy≄0 ≃ ((x ⁻¹) x≄0) * ((y ⁻¹) y≄0)
⁻¹-distrib-* {x} {y} x≄0 y≄0 xy≄0 = let x⁻¹ = (x ⁻¹) x≄0; y⁻¹ = (y ⁻¹) y≄0 in
                                    ≃-symm (⁻¹-unique (x⁻¹ * y⁻¹) (x * y) xy≄0 (begin
  x⁻¹ * y⁻¹ * (x * y)   ≈⟨ *-congˡ {x⁻¹ * y⁻¹} (*-comm x y) ⟩
  x⁻¹ * y⁻¹ * (y * x)   ≈⟨ *-assoc x⁻¹ y⁻¹ (y * x) ⟩
  x⁻¹ * (y⁻¹ * (y * x)) ≈⟨ *-congˡ {x⁻¹} (≃-symm (*-assoc y⁻¹ y x)) ⟩
  x⁻¹ * (y⁻¹ * y * x)   ≈⟨ *-congˡ {x⁻¹} (*-congʳ {x} (*-inverseˡ y y≄0)) ⟩
  x⁻¹ * (1ℝ * x)        ≈⟨ *-congˡ {x⁻¹} (*-identityˡ x) ⟩
  x⁻¹ * x               ≈⟨ *-inverseˡ x x≄0 ⟩
  1ℝ                     ∎))
  where open ≃-Reasoning

abstract
  fast-⁻¹-distrib-* : ∀ {x y} -> (x≄0 : x ≄0) -> (y≄0 : y ≄0) -> (xy≄0 : (x * y) ≄0) -> 
                      ((x * y) ⁻¹) xy≄0 ≃ ((x ⁻¹) x≄0) * ((y ⁻¹) y≄0)
  fast-⁻¹-distrib-* {x} {y} x≄0 y≄0 xy≄0 = ⁻¹-distrib-* {x} {y} x≄0 y≄0 xy≄0

ε-from-convergence : ∀ {xs : ℕ -> ℝ} -> (xₙ→ℓ : xs isConvergent) ->
                ∀ ε -> Positive ε -> ∃ λ (N-1 : ℕ) -> ∀ n -> n ℕ.≥ suc N-1 -> ∣ xs n - proj₁ xₙ→ℓ ∣ < ε
ε-from-convergence {xs} (ℓ , con* xₙ→ℓ) ε posε = let arch = fast-archimedean-ℝ₂ posε; k = suc (proj₁ arch); N = suc (proj₁ (xₙ→ℓ k)) in
                                           ℕ.pred N , λ {(suc n-1) n≥N -> let n = suc n-1 in begin-strict
  ∣ xs n - ℓ ∣ ≤⟨ proj₂ (xₙ→ℓ k) n n≥N ⟩
  (+ 1 / k) ⋆ <⟨ proj₂ arch ⟩
  ε            ∎}
  where open ≤-Reasoning

abstract
  fast-ε-from-convergence : ∀ {xs : ℕ -> ℝ} -> (xₙ→ℓ : xs isConvergent) ->
                       ∀ ε -> Positive ε -> ∃ λ (N-1 : ℕ) -> ∀ n -> n ℕ.≥ suc N-1 -> ∣ xs n - proj₁ xₙ→ℓ ∣ < ε
  fast-ε-from-convergence = ε-from-convergence

¬negx⇒nonNegx : ∀ {x} -> ¬ (Negative x) -> NonNegative x
¬negx⇒nonNegx {x} hyp = 0≤x⇒nonNegx (≮⇒≥ (λ hyp2 -> hyp (pos-cong (+-identityˡ (- x)) hyp2)))

nonNegx⇒¬negx : ∀ {x} -> NonNegative x -> ¬ (Negative x)
nonNegx⇒¬negx {x} (nonNeg* nonx) (pos* (n-1 , negx)) = let n = suc n-1 in ℚP.<-irrefl (ℚP.≃-refl {ℚ.- (+ 1 / n)}) (begin-strict
  ℚ.- (+ 1 / n)     ≤⟨ nonx n ⟩
  seq x n           ≈⟨ ℚP.≃-sym (ℚP.neg-involutive (seq x n)) ⟩
  ℚ.- (ℚ.- seq x n) <⟨ ℚP.neg-mono-< negx ⟩
  ℚ.- (+ 1 / n)      ∎)
  where open ℚP.≤-Reasoning

nonNegx∧x≄0⇒posx : ∀ {x} -> NonNegative x -> x ≄0 -> Positive x
nonNegx∧x≄0⇒posx {x} nonx x≄0 = 0<x⇒posx (begin-strict
  0ℝ    <⟨ x≄0⇒0<∣x∣ x≄0 ⟩
  ∣ x ∣ ≈⟨ nonNegx⇒∣x∣≃x nonx ⟩
  x      ∎)
  where open ≤-Reasoning

nonNegx⇒nonNegx⁻¹ : ∀ {x} -> NonNegative x -> (x≄0 : x ≄0) -> NonNegative ((x ⁻¹) x≄0)
nonNegx⇒nonNegx⁻¹ {x} nonx x≄0 = pos⇒nonNeg (posx⇒posx⁻¹ {x} x≄0 (nonNegx∧x≄0⇒posx {x} nonx x≄0))

{-
Proposition:
  If xₙ ≠ 0 for all n∈ℕ, x₀ ≠ 0, and (xₙ)→x₀, then (xₙ⁻¹)→x₀⁻¹.
Proof:
  We must show that, for all k∈ℕ, there is Nₖ∈ℕ such that
                         ∣xₙ⁻¹ - x₀⁻¹∣ ≤ k⁻¹.
By the Archimedean Property, there is r∈ℕ such that r⁻¹ < 2⁻¹∣x₀∣ since ∣x₀∣ > 0.
Then for some n₀∈ℕ we have
                   ∣xₙ - x₀∣ ≤ r⁻¹ < 2⁻¹∣x₀∣ < ∣x₀∣            (n ≥ n₀),
which implies, for n ≥ n₀,
                       ∣xₙ∣ = ∣x₀ - (x₀ - xₙ)∣
                            ≥ ∣∣x₀∣ - ∣x₀ - xₙ∣∣
                            = ∣x₀∣ - ∣x₀ - xₙ∣   since ∣xₙ - x₀∣ < ∣x₀∣
                            > ∣x₀∣ - 2⁻¹∣x₀∣     since n ≥ n₀
                            = 2⁻¹∣x₀∣.  
Let k∈ℕ. Then there is m₀∈ℕ such that
                      ∣xₙ - x₀∣ < (2k)⁻¹∣x₀∣²                 (n ≥ m₀)
since ∣x₀∣ > 0. Let N = max{m₀, n₀} and let n ≥ N. We have
         ∣xₙ⁻¹ - x₀⁻¹∣ = ∣xₙ∣⁻¹ * ∣x₀∣⁻¹ * ∣xₙ - x₀∣
                       < 2∣x₀∣⁻¹ * ∣x₀∣⁻¹ * ∣xₙ - x₀∣ since n ≥ n₀
                       < 2∣x₀∣⁻² * (2k)⁻¹∣x₀∣²        since n ≥ m₀
                       = k⁻¹.
Hence ∣xₙ⁻¹ - x₀⁻¹∣ ≤ k⁻¹ for all n ≥ N.                                        □

*-mono-≤ {∣ x₀ - xₙ ∣} {(+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣)}
                                                         {∣xₙ∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)} 
                                                         (nonNeg∣x∣ (x₀ - xₙ)) 
                                                         (nonNegx,y⇒nonNegx*y {∣xₙ∣⁻¹} {∣x₀∣⁻¹} 
                                                         (nonNegx⇒nonNegx⁻¹ {∣ xₙ ∣} (nonNeg∣x∣ xₙ) ∣xₙ∣≄0) 
                                                         (nonNegx⇒nonNegx⁻¹ {∣ x₀ ∣} (nonNeg∣x∣ x₀) ∣x₀∣≄0)) 
                                                         (<⇒≤ {∣ x₀ - xₙ ∣} {(+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣)} part4) 
                                                         (≤-respʳ-≃ {∣xₙ∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * ∣x₀∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)}
                                                         (*-assoc (2ℚᵘ ⋆) ∣x₀∣⁻¹ ∣x₀∣⁻¹) 
                                                         (<⇒≤ {∣xₙ∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * ∣x₀∣⁻¹ * ∣x₀∣⁻¹}
                                                         (*-monoˡ-<-pos {∣x₀∣⁻¹} (posx⇒posx⁻¹ {∣ x₀ ∣} ∣x₀∣≄0 (x≄0⇒pos∣x∣ {x₀} x₀≄0)) part3)))
-}
abstract
  xₙ≄0∧x₀≄0⇒xₙ⁻¹→x₀⁻¹ : ∀ {xs : ℕ -> ℝ} -> ∀ {x₀ : ℝ} -> xs ConvergesTo x₀ -> (xₙ≄0 : ∀ n -> xs n ≄0) -> (x₀≄0 : x₀ ≄0) ->
                        (λ n -> (xs n ⁻¹) (xₙ≄0 n)) ConvergesTo (x₀ ⁻¹) x₀≄0
  xₙ≄0∧x₀≄0⇒xₙ⁻¹→x₀⁻¹ {xs} {x₀} (con* xₙ→x₀) xₙ≄0 x₀≄0 = con* main
    where
      open ≤-Reasoning
      open ℤ-Solver.+-*-Solver
      main : ∀ k -> {k≢0 : k ≢0} -> ∃ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 ->
             ∣ (xs n ⁻¹) (xₙ≄0 n) - (x₀ ⁻¹) x₀≄0 ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
      main (suc k-1) = ℕ.pred N , sub
        where
          arch = fast-archimedean-ℝ₂ {(+ 1 / 2) ⋆ * ∣ x₀ ∣} (posx,y⇒posx*y (posp⇒posp⋆ (+ 1 / 2) _) (x≄0⇒pos∣x∣ x₀≄0))
          r = suc (proj₁ arch)
          k = suc k-1
          m₀-getter = fast-ε-from-convergence (x₀ , con* xₙ→x₀) ((+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣))
                      (posx,y⇒posx*y (posp⇒posp⋆ (+ 1 / (2 ℕ.* k)) _)
                      (posx,y⇒posx*y (x≄0⇒pos∣x∣ x₀≄0) (x≄0⇒pos∣x∣ x₀≄0)))
          m₀ = suc (proj₁ m₀-getter)
          n₀ = suc (proj₁ (xₙ→x₀ r))
          N = m₀ ℕ.⊔ n₀

          {-
            [1]
            Incredible optimization note!
            -------------------------------
            If you case split on n here to get n = suc m for some m∈ℕ, the typechecking (seemingly) never completes!
            If you leave it as is, the typechecking completes in reasonable time.
            Agda must be getting stuck on computing lots of extra things when n = suc m. Amazing!
          
            Despite this issue being solved, the addition of all of the implicit arguments below is a notable optimization, and will
            thus be kept.
          -}
          sub : ∀ n -> n ℕ.≥ N -> ∣ (xs n ⁻¹) (xₙ≄0 n) - (x₀ ⁻¹) x₀≄0 ∣ ≤ (+ 1 / k) ⋆
          sub n n≥N = begin
            ∣ xₙ⁻¹ - x₀⁻¹ ∣                          ≈⟨ ≃-trans {∣ xₙ⁻¹ - x₀⁻¹ ∣} {∣xₙ∣⁻¹ * ∣x₀∣⁻¹ * ∣ x₀ - xₙ ∣} {∣ x₀ - xₙ ∣ * (∣xₙ∣⁻¹ * ∣x₀∣⁻¹)}
                                                        part2 (*-comm (∣xₙ∣⁻¹ * ∣x₀∣⁻¹) ∣ x₀ - xₙ ∣) ⟩
            ∣ x₀ - xₙ ∣ * (∣xₙ∣⁻¹ * ∣x₀∣⁻¹)           ≤⟨ *-mono-≤ {∣ x₀ - xₙ ∣} {(+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣)}
                                                         {∣xₙ∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)} 
                                                         (nonNeg∣x∣ (x₀ - xₙ)) 
                                                         (nonNegx,y⇒nonNegx*y {∣xₙ∣⁻¹} {∣x₀∣⁻¹} 
                                                         (nonNegx⇒nonNegx⁻¹ {∣ xₙ ∣} (nonNeg∣x∣ xₙ) ∣xₙ∣≄0) 
                                                         (nonNegx⇒nonNegx⁻¹ {∣ x₀ ∣} (nonNeg∣x∣ x₀) ∣x₀∣≄0)) 
                                                         (<⇒≤ {∣ x₀ - xₙ ∣} {(+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣)} part4) 
                                                         (≤-respʳ-≃ {∣xₙ∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * ∣x₀∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)}
                                                         (*-assoc (2ℚᵘ ⋆) ∣x₀∣⁻¹ ∣x₀∣⁻¹) 
                                                         (<⇒≤ {∣xₙ∣⁻¹ * ∣x₀∣⁻¹} {2ℚᵘ ⋆ * ∣x₀∣⁻¹ * ∣x₀∣⁻¹}
                                                         (*-monoˡ-<-pos {∣x₀∣⁻¹} (posx⇒posx⁻¹ {∣ x₀ ∣} ∣x₀∣≄0 (x≄0⇒pos∣x∣ {x₀} x₀≄0))
                                                         {∣xₙ∣⁻¹} {2ℚᵘ ⋆ * ∣x₀∣⁻¹} part3))) ⟩
            (+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣) *
            (2ℚᵘ ⋆ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹))                 ≈⟨ *-congˡ {(+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣)} {2ℚᵘ ⋆ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)} {∣x₀∣⁻¹ * ∣x₀∣⁻¹ * 2ℚᵘ ⋆}
                                                          (*-comm (2ℚᵘ ⋆) (∣x₀∣⁻¹ * ∣x₀∣⁻¹)) ⟩
            (+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣) *
            (∣x₀∣⁻¹ * ∣x₀∣⁻¹ * 2ℚᵘ ⋆)                   ≈⟨ *-assoc ((+ 1 / (2 ℕ.* k)) ⋆) (∣ x₀ ∣ * ∣ x₀ ∣) (∣x₀∣⁻¹ * ∣x₀∣⁻¹ * 2ℚᵘ ⋆) ⟩
            (+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣ *
            (∣x₀∣⁻¹  * ∣x₀∣⁻¹ * 2ℚᵘ ⋆))                 ≈⟨ *-congˡ {(+ 1 / (2 ℕ.* k)) ⋆} {∣ x₀ ∣ * ∣ x₀ ∣ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹ * 2ℚᵘ ⋆)}
                                                           {∣ x₀ ∣ * ∣ x₀ ∣ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹) * 2ℚᵘ ⋆}
                                                           (≃-symm {∣ x₀ ∣ * ∣ x₀ ∣ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹) * (2ℚᵘ ⋆)}
                                                           {∣ x₀ ∣ * ∣ x₀ ∣ * ((∣x₀∣⁻¹ * ∣x₀∣⁻¹) * (2ℚᵘ ⋆))}
                                                           (*-assoc (∣ x₀ ∣ * ∣ x₀ ∣) (∣x₀∣⁻¹ * ∣x₀∣⁻¹) (2ℚᵘ ⋆))) ⟩
            (+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣ *
            (∣x₀∣⁻¹ * ∣x₀∣⁻¹) * 2ℚᵘ ⋆)                  ≈⟨ *-congˡ {(+ 1 / (2 ℕ.* k)) ⋆} {∣ x₀ ∣ * ∣ x₀ ∣ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹) * 2ℚᵘ ⋆}
                                                          {1ℝ * 2ℚᵘ ⋆} (*-congʳ {2ℚᵘ ⋆} {∣ x₀ ∣ * ∣ x₀ ∣ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)} {1ℝ} part5) ⟩
            (+ 1 / (2 ℕ.* k)) ⋆ * (1ℝ * 2ℚᵘ ⋆)         ≈⟨ ≃-trans {(+ 1 / (2 ℕ.* k)) ⋆ * (1ℝ * 2ℚᵘ ⋆)} {(+ 1 / (2 ℕ.* k)) ⋆ * (2ℚᵘ ⋆)}
                                                          {(+ 1 / (2 ℕ.* k) ℚ.* 2ℚᵘ) ⋆}
                                                          (*-congˡ {(+ 1 / (2 ℕ.* k)) ⋆} {1ℝ * 2ℚᵘ ⋆} {2ℚᵘ ⋆} (*-identityˡ (2ℚᵘ ⋆))) 
                                                          (≃-symm {(+ 1 / (2 ℕ.* k) ℚ.* 2ℚᵘ) ⋆} {(+ 1 / (2 ℕ.* k)) ⋆ * 2ℚᵘ ⋆}
                                                          (⋆-distrib-* (+ 1 / (2 ℕ.* k)) 2ℚᵘ)) ⟩
            (+ 1 / (2 ℕ.* k) ℚ.* 2ℚᵘ) ⋆                ≈⟨ ⋆-cong {+ 1 / (2 ℕ.* k) ℚ.* 2ℚᵘ} {+ 1 / k} (ℚ.*≡* (solve 1 (λ k ->
                                                          con (+ 1) :* con (+ 2) :* k := con (+ 1) :* (con (+ 2) :* k :* con (+ 1)))
                                                          refl (+ k))) ⟩
            (+ 1 / k) ⋆                                 ∎
          
            where
              xₙ = xs n
              xₙ⁻¹ = (xₙ ⁻¹) (xₙ≄0 n)
              x₀⁻¹ = (x₀ ⁻¹) x₀≄0
              ∣xₙ∣≄0 = x≄0⇒∣x∣≄0 (xₙ≄0 n)
              ∣x₀∣≄0 = x≄0⇒∣x∣≄0 x₀≄0
              ∣xₙ∣⁻¹ = (∣ xₙ ∣ ⁻¹) ∣xₙ∣≄0
              ∣x₀∣⁻¹ = (∣ x₀ ∣ ⁻¹) ∣x₀∣≄0

              2⁻¹∣x₀∣<∣xₙ∣ : (+ 1 / 2) ⋆ * ∣ x₀ ∣ < ∣ xₙ ∣
              2⁻¹∣x₀∣<∣xₙ∣ = begin-strict
                (+ 1 / 2) ⋆ * ∣ x₀ ∣            ≈⟨ ≃-refl ⟩
                (1ℚᵘ ℚ.- (+ 1 / 2)) ⋆ * ∣ x₀ ∣  ≈⟨ ≃-trans
                                                   (*-congʳ {∣ x₀ ∣} (⋆-distrib-to-p⋆-q⋆ 1ℚᵘ (+ 1 / 2)))
                                                   (*-distribʳ-+ ∣ x₀ ∣ 1ℝ (- ((+ 1 / 2) ⋆))) ⟩
                1ℝ * ∣ x₀ ∣ +
                (- ((+ 1 / 2) ⋆)) * ∣ x₀ ∣      ≈⟨ +-cong (*-identityˡ ∣ x₀ ∣) (≃-symm (neg-distribˡ-* ((+ 1 / 2) ⋆) ∣ x₀ ∣)) ⟩
                ∣ x₀ ∣ - (+ 1 / 2) ⋆ * ∣ x₀ ∣   <⟨ +-monoʳ-< ∣ x₀ ∣ (neg-mono-< (<-respˡ-≃ (∣x-y∣≃∣y-x∣ xₙ x₀)
                                                   (≤-<-trans (proj₂ (xₙ→x₀ r) n (ℕP.≤-trans (ℕP.m≤n⊔m m₀ n₀) n≥N))
                                                   (proj₂ arch)))) ⟩
                ∣ x₀ ∣ - ∣ x₀ - xₙ ∣            ≤⟨ x≤∣x∣ ⟩
                ∣ ∣ x₀ ∣ - ∣ x₀ - xₙ ∣ ∣        ≤⟨ ∣∣x∣-∣y∣∣≤∣x-y∣ x₀ (x₀ - xₙ) ⟩
                ∣ x₀ - (x₀ - xₙ) ∣             ≈⟨ ∣-∣-cong (≃-trans
                                                  (+-congʳ x₀ (neg-distrib-+ x₀ (- xₙ)))
                                                  (≃-symm (+-assoc x₀ (- x₀) (- (- xₙ))))) ⟩
                ∣ x₀ - x₀ - (- xₙ) ∣           ≈⟨ ∣-∣-cong (≃-trans (+-cong (+-inverseʳ x₀) (neg-involutive xₙ)) (+-identityˡ xₙ)) ⟩
                ∣ xₙ ∣                          ∎

              part1 : xₙ⁻¹ - x₀⁻¹ ≃ xₙ⁻¹ * x₀⁻¹ * (x₀ - xₙ)
              part1 = ≃-symm (begin-equality
                xₙ⁻¹ * x₀⁻¹ * (x₀ - xₙ)                 ≈⟨ *-distribˡ-+ (xₙ⁻¹ * x₀⁻¹) x₀ (- xₙ) ⟩
                xₙ⁻¹ * x₀⁻¹ * x₀ + xₙ⁻¹ * x₀⁻¹ * (- xₙ) ≈⟨ +-cong
                                                           (≃-trans (≃-trans
                                                                    (*-assoc xₙ⁻¹ x₀⁻¹ x₀)
                                                                    (*-congˡ {xₙ⁻¹} (*-inverseˡ x₀ x₀≄0)))
                                                                    (*-identityʳ xₙ⁻¹))
                                                           (≃-symm (neg-distribʳ-* (xₙ⁻¹ * x₀⁻¹) xₙ)) ⟩
                xₙ⁻¹ - xₙ⁻¹ * x₀⁻¹ * xₙ                 ≈⟨ +-congʳ xₙ⁻¹ (-‿cong (≃-trans (≃-trans (≃-trans
                                                           (*-comm (xₙ⁻¹ * x₀⁻¹) xₙ)
                                                           (≃-symm (*-assoc xₙ xₙ⁻¹ x₀⁻¹)))
                                                           (*-congʳ {x₀⁻¹} (*-inverseʳ xₙ (xₙ≄0 n))))
                                                           (*-identityˡ x₀⁻¹))) ⟩
                xₙ⁻¹ - x₀⁻¹                              ∎)

              part2 : ∣ xₙ⁻¹ - x₀⁻¹ ∣ ≃ ∣xₙ∣⁻¹ * ∣x₀∣⁻¹ * ∣ x₀ - xₙ ∣
              part2 = begin-equality
                ∣ xₙ⁻¹ - x₀⁻¹ ∣                   ≈⟨ ∣-∣-cong part1 ⟩
                ∣ xₙ⁻¹ * x₀⁻¹ * (x₀ - xₙ) ∣       ≈⟨ ∣x*y∣≃∣x∣*∣y∣ (xₙ⁻¹ * x₀⁻¹) (x₀ - xₙ) ⟩
                ∣ xₙ⁻¹ * x₀⁻¹ ∣ * ∣ x₀ - xₙ ∣     ≈⟨ *-congʳ {∣ x₀ - xₙ ∣} (∣x*y∣≃∣x∣*∣y∣ xₙ⁻¹ x₀⁻¹) ⟩
                ∣ xₙ⁻¹ ∣ * ∣ x₀⁻¹ ∣ * ∣ x₀ - xₙ ∣ ≈⟨ *-congʳ {∣ x₀ - xₙ ∣} (≃-symm (*-cong
                                                    (∣x∣⁻¹≃∣x⁻¹∣ {xₙ} ∣xₙ∣≄0 (xₙ≄0 n))
                                                    (∣x∣⁻¹≃∣x⁻¹∣ {x₀} ∣x₀∣≄0 x₀≄0))) ⟩
                ∣xₙ∣⁻¹ * ∣x₀∣⁻¹ * ∣ x₀ - xₙ ∣      ∎

              part3 : ∣xₙ∣⁻¹ < 2ℚᵘ ⋆ * ∣x₀∣⁻¹
              part3 = let 2⁻¹≄0 = ∣↥p∣≢0⇒p⋆≄0 (+ 1 / 2) _
                                ; 2⁻¹∣x₀∣≄0 = x≄0∧y≄0⇒x*y≄0 {(+ 1 / 2) ⋆} {∣ x₀ ∣} 2⁻¹≄0 ∣x₀∣≄0 in begin-strict
                    ∣xₙ∣⁻¹                                           <⟨ x<y∧posx,y⇒y⁻¹<x⁻¹ {(+ 1 / 2) ⋆ * ∣ x₀ ∣} {∣ xₙ ∣}
                                                                        2⁻¹∣x₀∣<∣xₙ∣ 2⁻¹∣x₀∣≄0 ∣xₙ∣≄0
                                                                        (posx,y⇒posx*y {(+ 1 / 2) ⋆} {∣ x₀ ∣}
                                                                        (posp⇒posp⋆ (+ 1 / 2) _) (x≄0⇒pos∣x∣ {x₀} x₀≄0))
                                                                        (x≄0⇒pos∣x∣ {xₙ} (xₙ≄0 n)) ⟩
                    (((+ 1 / 2) ⋆ * ∣ x₀ ∣) ⁻¹) 2⁻¹∣x₀∣≄0            ≈⟨ ⁻¹-distrib-* {(+ 1 / 2) ⋆} {∣ x₀ ∣} 2⁻¹≄0 ∣x₀∣≄0 2⁻¹∣x₀∣≄0 ⟩
                    (((+ 1 / 2) ⋆) ⁻¹) 2⁻¹≄0 * ∣x₀∣⁻¹                ≈⟨ *-congʳ {∣x₀∣⁻¹} (⋆-distrib-⁻¹ (+ 1 / 2) 2⁻¹≄0) ⟩
                    2ℚᵘ ⋆ * ∣x₀∣⁻¹                                    ∎

              part4 : ∣ x₀ - xₙ ∣ < (+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣)
              part4 = begin-strict
                ∣ x₀ - xₙ ∣                             ≈⟨ ∣x-y∣≃∣y-x∣ x₀ xₙ ⟩
                ∣ xₙ - x₀ ∣                             <⟨ proj₂ m₀-getter n (ℕP.≤-trans (ℕP.m≤m⊔n m₀ n₀) n≥N) ⟩
                (+ 1 / (2 ℕ.* k)) ⋆ * (∣ x₀ ∣ * ∣ x₀ ∣)   ∎

              part5 : (∣ x₀ ∣ * ∣ x₀ ∣) * (∣x₀∣⁻¹ * ∣x₀∣⁻¹) ≃ 1ℝ
              part5 = begin-equality
                (∣ x₀ ∣ * ∣ x₀ ∣) * (∣x₀∣⁻¹ * ∣x₀∣⁻¹) ≈⟨ *-assoc ∣ x₀ ∣ ∣ x₀ ∣ (∣x₀∣⁻¹ * ∣x₀∣⁻¹) ⟩
                ∣ x₀ ∣ * (∣ x₀ ∣ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)) ≈⟨ *-congˡ {∣ x₀ ∣} {∣ x₀ ∣ * (∣x₀∣⁻¹ * ∣x₀∣⁻¹)} {1ℝ * ∣x₀∣⁻¹}
                                                         (≃-trans (≃-symm (*-assoc ∣ x₀ ∣ ∣x₀∣⁻¹ ∣x₀∣⁻¹))
                                                         (*-congʳ {∣x₀∣⁻¹} {∣ x₀ ∣ * ∣x₀∣⁻¹} {1ℝ}
                                                         (*-inverseʳ ∣ x₀ ∣ ∣x₀∣≄0)))⟩
                ∣ x₀ ∣ * (1ℝ * ∣x₀∣⁻¹)                ≈⟨ *-congˡ {∣ x₀ ∣} {1ℝ * ∣x₀∣⁻¹} {∣x₀∣⁻¹} (*-identityˡ ∣x₀∣⁻¹) ⟩
                ∣ x₀ ∣ * ∣x₀∣⁻¹                       ≈⟨ *-inverseʳ ∣ x₀ ∣ ∣x₀∣≄0 ⟩
                1ℝ                                     ∎

∣xₙ∣→∣x₀∣ : ∀ {xs : ℕ -> ℝ} -> (x→x₀ : xs isConvergent) -> (λ n -> ∣ xs n ∣) ConvergesTo ∣ proj₁ x→x₀ ∣
∣xₙ∣→∣x₀∣ {xs} (x₀ , con* x→x₀) = con* λ {(suc k-1) -> let k = suc k-1 in
                                  proj₁ (x→x₀ k) , λ {(suc n-1) n≥N -> let n = suc n-1 in begin
  ∣ ∣ xs n ∣ - ∣ x₀ ∣ ∣ ≤⟨ ∣∣x∣-∣y∣∣≤∣x-y∣ (xs n) x₀ ⟩
  ∣ xs n - x₀ ∣        ≤⟨ proj₂ (x→x₀ k) n n≥N ⟩
  (+ 1 / k) ⋆           ∎}}
  where open ≤-Reasoning

0≤x⇒∣x∣≃x : ∀ {x} -> 0ℝ ≤ x -> ∣ x ∣ ≃ x
0≤x⇒∣x∣≃x {x} 0≤x = nonNegx⇒∣x∣≃x (nonNeg-cong (≃-trans (+-congʳ x (≃-symm 0≃-0)) (+-identityʳ x)) 0≤x)

x≤y⇒0≤y-x : ∀ {x y} -> x ≤ y -> 0ℝ ≤ y - x
x≤y⇒0≤y-x {x} {y} x≤y = nonNeg-cong (≃-symm (≃-trans (+-congʳ (y - x) (≃-symm 0≃-0)) (+-identityʳ (y - x)))) x≤y

xₙ≤yₙ⇒x₀≤y₀ : ∀ {xs ys : ℕ -> ℝ} -> ∀ {x₀ y₀ : ℝ} -> xs ConvergesTo x₀ -> ys ConvergesTo y₀ ->
              (∀ n -> {n ≢0} -> xs n ≤ ys n) -> x₀ ≤ y₀
xₙ≤yₙ⇒x₀≤y₀ {xs} {ys} {x₀} {y₀} (con* xₙ→x₀) (con* yₙ→y₀) xₙ≤yₙ = 0≤y-x⇒x≤y (begin
  0ℝ          ≤⟨ 0≤∣x∣ (y₀ - x₀) ⟩
  ∣ y₀ - x₀ ∣ ≈⟨ uniqueness-of-limits (∣xₙ∣→∣x₀∣ (y₀ - x₀ , yₙ-xₙ→y₀-x₀))
                 (xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc n-1) -> let n = suc n-1 in
                 ≃-symm (0≤x⇒∣x∣≃x (x≤y⇒0≤y-x (xₙ≤yₙ n)))}) (y₀ - x₀ , yₙ-xₙ→y₀-x₀)) ⟩
  y₀ - x₀      ∎)
  where
    open ≤-Reasoning
    yₙ-xₙ→y₀-x₀ = xₙ+yₙ→x₀+y₀ (y₀ , con* yₙ→y₀) (- x₀ , -xₙ→-x₀ (x₀ , con* xₙ→x₀))

private
  x-y≤z⇒x≤z+y : ∀ {x y z} -> x - y ≤ z -> x ≤ z + y
  x-y≤z⇒x≤z+y {x} {y} {z} x-y≤z = begin
    x         ≈⟨ ≃-symm (≃-trans (≃-trans
                 (+-assoc x (- y) y)
                 (+-congʳ x (+-inverseˡ y)))
                 (+-identityʳ x)) ⟩
    x - y + y ≤⟨ +-monoˡ-≤ y x-y≤z ⟩
    z + y      ∎
    where open ≤-Reasoning

  ∣x⊔y-z⊔w∣≤∣x-z∣⊔∣y-w∣ : ∀ x y z w -> ∣ x ⊔ y - (z ⊔ w) ∣ ≤ ∣ x - z ∣ ⊔ ∣ y - w ∣
  ∣x⊔y-z⊔w∣≤∣x-z∣⊔∣y-w∣ x y z w = ≤-respˡ-≃ (≃-symm (∣x∣≃x⊔-x (x ⊔ y - (z ⊔ w))))
                                (x≤z∧y≤z⇒x⊔y≤z
                                (lem x y (z ⊔ w) (∣ x - z ∣ ⊔ ∣ y - w ∣) part1 part2)
                                (≤-respˡ-≃ (≃-symm (-[x-y]≃y-x (x ⊔ y) (z ⊔ w)))
                                           (lem z w (x ⊔ y) (∣ x - z ∣ ⊔ ∣ y - w ∣) part3 part4)))
    where
      open ≤-Reasoning
      lem : ∀ x y z w -> x - z ≤ w -> y - z ≤ w -> x ⊔ y - z ≤ w
      lem x y z w x-z≤w y-z≤w = begin
        x ⊔ y - z ≤⟨ +-monoˡ-≤ (- z) (x≤z∧y≤z⇒x⊔y≤z
                     (x-y≤z⇒x≤z+y x-z≤w)
                     (x-y≤z⇒x≤z+y y-z≤w)) ⟩
        w + z - z ≈⟨ ≃-trans (≃-trans
                     (+-assoc w z (- z))
                     (+-congʳ w (+-inverseʳ z)))
                     (+-identityʳ w) ⟩
        w          ∎

      part1 : x - (z ⊔ w) ≤ ∣ x - z ∣ ⊔ ∣ y - w ∣
      part1 = begin
        x - (z ⊔ w)           ≤⟨ +-monoʳ-≤ x (neg-mono-≤ (x≤x⊔y z w)) ⟩
        x - z                 ≤⟨ x≤∣x∣ ⟩
        ∣ x - z ∣             ≤⟨ x≤x⊔y ∣ x - z ∣ ∣ y - w ∣ ⟩
        ∣ x - z ∣ ⊔ ∣ y - w ∣   ∎

      part2 : y - (z ⊔ w) ≤ ∣ x - z ∣ ⊔ ∣ y - w ∣ 
      part2 = begin
        y - (z ⊔ w)           ≤⟨ +-monoʳ-≤ y (neg-mono-≤ (x≤y⊔x w z)) ⟩
        y - w                 ≤⟨ x≤∣x∣ ⟩
        ∣ y - w ∣             ≤⟨ x≤y⊔x ∣ y - w ∣ ∣ x - z ∣ ⟩
        ∣ x - z ∣ ⊔ ∣ y - w ∣   ∎

      part3 : z - (x ⊔ y) ≤ ∣ x - z ∣ ⊔ ∣ y - w ∣
      part3 = begin
        z - (x ⊔ y)           ≤⟨ +-monoʳ-≤ z (neg-mono-≤ (x≤x⊔y x y)) ⟩
        z - x                 ≤⟨ x≤∣x∣ ⟩
        ∣ z - x ∣             ≈⟨ ∣x-y∣≃∣y-x∣ z x ⟩
        ∣ x - z ∣             ≤⟨ x≤x⊔y ∣ x - z ∣ ∣ y - w ∣ ⟩
        ∣ x - z ∣ ⊔ ∣ y - w ∣   ∎

      part4 : w - (x ⊔ y) ≤ ∣ x - z ∣ ⊔ ∣ y - w ∣
      part4 = begin
        w - (x ⊔ y)           ≤⟨ +-monoʳ-≤ w (neg-mono-≤ (x≤y⊔x y x)) ⟩
        w - y                 ≤⟨ x≤∣x∣ ⟩
        ∣ w - y ∣             ≈⟨ ∣x-y∣≃∣y-x∣ w y ⟩
        ∣ y - w ∣             ≤⟨ x≤y⊔x ∣ y - w ∣ ∣ x - z ∣ ⟩
        ∣ x - z ∣ ⊔ ∣ y - w ∣   ∎

xₙ⊔yₙ→x₀⊔y₀ : ∀ {xs ys : ℕ -> ℝ} -> (xₙ→x₀ : xs isConvergent) -> (yₙ→y₀ : ys isConvergent) ->
              (λ n -> xs n ⊔ ys n) ConvergesTo (proj₁ xₙ→x₀ ⊔ proj₁ yₙ→y₀)
xₙ⊔yₙ→x₀⊔y₀ {xs} {ys} (x₀ , con* xₙ→x₀) (y₀ , con* yₙ→y₀) = con* (λ {(suc k-1) ->
                      let k = suc k-1; N₁ = suc (proj₁ (xₙ→x₀ k)); N₂ = suc (proj₁ (yₙ→y₀ k)) in
                      ℕ.pred (N₁ ℕ.⊔ N₂) , λ {(suc n-1) n≥N -> let n = suc n-1 in begin
  ∣ xs n ⊔ ys n - (x₀ ⊔ y₀) ∣   ≤⟨ ∣x⊔y-z⊔w∣≤∣x-z∣⊔∣y-w∣ (xs n) (ys n) x₀ y₀ ⟩
  ∣ xs n - x₀ ∣ ⊔ ∣ ys n - y₀ ∣ ≤⟨ x≤z∧y≤z⇒x⊔y≤z
                                  (proj₂ (xₙ→x₀ k) n (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) n≥N))
                                  (proj₂ (yₙ→y₀ k) n (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) n≥N)) ⟩
  (+ 1 / k) ⋆                    ∎}})
  where open ≤-Reasoning

SeriesOf_From_ : (ℕ -> ℝ) -> ℕ -> (ℕ -> ℝ)
(SeriesOf xs From i) n = ∑ xs i n

SeriesOf : (ℕ -> ℝ) -> (ℕ -> ℝ)
SeriesOf xs = SeriesOf xs From 0

limitShifting : ∀ xs -> ∀ k m n -> ∑ xs m k ≃ ∑ xs n k + ∑ xs m n
limitShifting xs k zero zero = ≃-symm (+-identityʳ (∑₀ xs k))
limitShifting xs k zero (suc n) = ≃-symm (begin
  ∑₀ xs k - (∑₀ xs n + xs n) + (∑₀ xs n + xs n)     ≈⟨ +-assoc _ _ _ ⟩
  ∑₀ xs k + (- (∑₀ xs n + xs n) + (∑₀ xs n + xs n)) ≈⟨ +-congʳ (∑₀ xs k) (+-inverseˡ _) ⟩
  ∑₀ xs k + 0ℝ                                      ≈⟨ +-identityʳ _ ⟩
  ∑₀ xs k                                            ∎)
  where open ≃-Reasoning
limitShifting xs k (suc m) zero = +-congʳ (∑₀ xs k) (≃-symm (+-identityˡ _))
limitShifting xs k (suc m) (suc n) = ≃-symm (begin
  ∑₀ xs k - (∑₀ xs n + xs n) + (∑₀ xs n + xs n - (∑₀ xs m + xs m)) ≈⟨ solve 4 (λ a b c d ->
                                                                      a :+ b :+ (c :+ d) := a :+ d :+ (c :+ b))
                                                                      ≃-refl (∑₀ xs k) (- (∑₀ xs n + xs n))
                                                                      (∑₀ xs n + xs n) (- (∑₀ xs m + xs m)) ⟩
  ∑₀ xs k - (∑₀ xs m + xs m) + (∑₀ xs n + xs n - (∑₀ xs n + xs n)) ≈⟨ +-congʳ (∑₀ xs k - (∑₀ xs m + xs m))
                                                                      (+-inverseʳ (∑₀ xs n + xs n)) ⟩
  ∑₀ xs k - (∑₀ xs m + xs m) + 0ℝ                                  ≈⟨ +-identityʳ _ ⟩
  ∑₀ xs k - (∑₀ xs m + xs m)                                        ∎)
  where
    open ≃-Reasoning
    open ℝ-+-*-Solver

lowerLimitShiftPreservesConvergence : ∀ xs -> (∃ λ n -> (SeriesOf xs From n) isConvergent) -> ∀ m -> (SeriesOf xs From m) isConvergent
lowerLimitShiftPreservesConvergence xs (n , (ℓ , con* hyp)) m = ℓ + ∑ xs m n , xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc k-1) -> let k = suc k-1 in
                                 ≃-symm (limitShifting xs k m n)}) (ℓ + ∑ xs m n ,
                                 xₙ+yₙ→x₀+y₀ {SeriesOf xs From n} {λ r -> ∑ xs m n} (ℓ , con* hyp) (∑ xs m n , xₙ≃c⇒xₙ→c (λ {(suc r-1) -> ≃-refl})))

cauchyConvergenceTest-if : ∀ xs -> SeriesOf xs isConvergent ->
                           ∀ k -> {k≢0 : k ≢0} -> ∃ λ Nₖ-1 -> ∀ m n -> m ℕ.≥ suc Nₖ-1 -> n ℕ.≥ suc Nₖ-1 ->
                           ∣ ∑ xs m n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
cauchyConvergenceTest-if xs (ℓ , con* hyp) (suc k-1) = let k = suc k-1; N₂ₖ = suc (proj₁ (hyp (2 ℕ.* k))) in
                                                       ℕ.pred N₂ₖ , λ {(suc m-1) (suc n-1) m≥N₂ₖ n≥N₂ₖ ->
                                                       let m = suc m-1; n = suc n-1 in begin
  ∣ ∑₀ xs n - ∑₀ xs m ∣                     ≈⟨ ∣-∣-cong (≃-symm (≃-trans (+-congʳ (∑₀ xs n - ∑₀ xs m) (+-inverseʳ ℓ)) (+-identityʳ _))) ⟩
  ∣ ∑₀ xs n - ∑₀ xs m + (ℓ - ℓ) ∣            ≈⟨ ∣-∣-cong (ℝsolve 4 (λ a b c d -> a +: b +: (c +: d) =: a +: d +: (c +: b))
                                               ≃-refl (∑₀ xs n) (- ∑₀ xs m) ℓ (- ℓ)) ⟩
  ∣ ∑₀ xs n - ℓ + (ℓ - ∑₀ xs m) ∣            ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (∑₀ xs n - ℓ) (ℓ - ∑₀ xs m) ⟩
  ∣ ∑₀ xs n - ℓ ∣ + ∣ ℓ - ∑₀ xs m ∣          ≤⟨ +-mono-≤
                                               (proj₂ (hyp (2 ℕ.* k)) n n≥N₂ₖ)
                                               (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (∑₀ xs m) ℓ) (proj₂ (hyp (2 ℕ.* k)) m m≥N₂ₖ)) ⟩
  (+ 1 / (2 ℕ.* k)) ⋆ + (+ 1 / (2 ℕ.* k)) ⋆ ≈⟨ ≃-trans
                                               (≃-symm (⋆-distrib-+ (+ 1 / (2 ℕ.* k)) (+ 1 / (2 ℕ.* k))))
                                               (⋆-cong (ℚ.*≡* (solve 1 (λ k ->
                                               (con (+ 1) :* (con (+ 2) :* k) :+ con (+ 1) :* (con (+ 2) :* k)) :* k :=
                                               con (+ 1) :* (con (+ 2) :* k :* (con (+ 2) :* k)))
                                               refl (+ k)))) ⟩
  (+ 1 / k) ⋆                                ∎}
  where
    open ≤-Reasoning
    open ℝ-+-*-Solver using ()
      renaming
        ( solve to ℝsolve
        ; _:+_  to _+:_
        ; _:=_  to _=:_
        )
    open ℤ-Solver.+-*-Solver

cauchyConvergenceTest-onlyif : ∀ xs ->
                               (∀ k -> {k≢0 : k ≢0} -> ∃ λ Nₖ-1 -> ∀ m n -> m ℕ.≥ suc Nₖ-1 -> n ℕ.≥ suc Nₖ-1 ->
                                       ∣ ∑ xs m n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆) ->
                               SeriesOf xs isConvergent
cauchyConvergenceTest-onlyif xs hyp = cauchy⇒convergent (cauchy* (λ {(suc k-1) -> let k = suc k-1; Mₖ = suc (proj₁ (hyp k)) in
                                      ℕ.pred Mₖ , λ {(suc m-1) (suc n-1) m≥Mₖ n≥Mₖ -> let m = suc m-1; n = suc n-1 in begin
  ∣ ∑ xs 0 m - ∑ xs 0 n ∣                   ≈⟨ ≃-refl ⟩
  ∣ ∑ xs n m ∣                              ≤⟨ proj₂ (hyp k) n m n≥Mₖ m≥Mₖ ⟩
  (+ 1 / k) ⋆                                ∎}}))
  where
    open ≤-Reasoning
    open ℤ-Solver.+-*-Solver

∑xₙisConvergent⇒xₙ→0 : ∀ xs -> SeriesOf xs isConvergent -> xs ConvergesTo 0ℝ
∑xₙisConvergent⇒xₙ→0 xs (ℓ , con* ∑xₙ→ℓ) = con* (λ {(suc k-1) -> let k = suc k-1; N₂ₖ = suc (proj₁ (∑xₙ→ℓ (2 ℕ.* k))) in
                                          ℕ.pred N₂ₖ , λ {(suc n-1) n≥N₂ₖ -> let n = suc n-1; n+1 = suc n in begin
  ∣ xs n - 0ℝ ∣                             ≈⟨ ∣-∣-cong (+-congʳ (xs n) (≃-symm (≃-trans (+-inverseʳ ℓ) 0≃-0))) ⟩
  ∣ xs n + (ℓ - ℓ)∣                          ≈⟨ ∣-∣-cong (≃-trans
                                               (+-congˡ (ℓ - ℓ) (≃-symm (≃-trans (+-congˡ (xs n) (+-inverseʳ (∑₀ xs n))) (+-identityˡ (xs n)))))
                                               (ℝsolve 6 (λ a b c d e f ->
                                               a +: b +: c +: d +: (e +: f) =: (a +: b +: d +: f +: (e +: c)))
                                               ≃-refl (∑₀ xs n-1) (xs n-1) (- (∑₀ xs n-1 + xs n-1)) (xs n) ℓ (- ℓ))) ⟩
  ∣ ∑₀ xs n+1 - ℓ + (ℓ - ∑₀ xs n) ∣          ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (∑₀ xs n+1 - ℓ) (ℓ - ∑₀ xs n) ⟩
  ∣ ∑₀ xs n+1 - ℓ ∣ + ∣ ℓ - ∑₀ xs n ∣        ≤⟨ +-mono-≤
                                               (proj₂ (∑xₙ→ℓ (2 ℕ.* k)) n+1 (ℕP.≤-trans n≥N₂ₖ (ℕP.n≤1+n n)))
                                               (≤-respˡ-≃ (∣x-y∣≃∣y-x∣ (∑₀ xs n) ℓ) (proj₂ (∑xₙ→ℓ (2 ℕ.* k)) n n≥N₂ₖ)) ⟩
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

SeriesOf_ConvergesAbsolutely : (ℕ -> ℝ) -> Set
SeriesOf xs ConvergesAbsolutely = SeriesOf (λ k -> ∣ xs k ∣) isConvergent

{-
Changing termination depth doesn't help fix this weird lem recursion problem (tried different depths up to 10).
-}
∑-cong : ∀ {xs ys : ℕ -> ℝ} -> (∀ n -> xs n ≃ ys n) -> ∀ m n -> ∑ xs m n ≃ ∑ ys m n
{-∑-cong {xs} {ys} xₙ≃yₙ zero zero = ≃-refl
∑-cong {xs} {ys} xₙ≃yₙ zero (suc n) = +-cong (∑-cong xₙ≃yₙ 0 n) (xₙ≃yₙ n)-}
∑-cong {xs} {ys} xₙ≃yₙ 0 n = lem n
  where
    lem : ∀ n -> ∑ xs 0 n ≃ ∑ ys 0 n
    lem 0 = ≃-refl
    lem (suc n) = +-cong (lem n) (xₙ≃yₙ n)
∑-cong {xs} {ys} xₙ≃yₙ (suc m) n = +-cong (∑-cong xₙ≃yₙ 0 n) (-‿cong (∑-cong xₙ≃yₙ 0 (suc m)))

{-
∣∑xᵢ∣ ≤ ∑∣xᵢ∣ 


Sometimes it's easier to use ∑ᵀ instead of ∑ that gives
            ∑ᵢ₌ₖⁿ xᵢ = xₖ + ⋯ + xₙ
instead of
            ∑ᵢ₌ₖⁿ xᵢ = ∑ᵢ₌₀ⁿ xᵢ - ∑ᵢ₌₀ᵏ xᵢ
when k ≤ n. 

As an example, consider the triangle inequality proof for ∑ below.

Note that ∑ᵀ requires i≤n, which isn't what we want in general. Moreover, 
∑ᵀ uses a somewhat complex with clause, so it's annoying to prove things about.
Hence the alternative definition.
-}
∑ᵀ : (ℕ -> ℝ) -> (i n : ℕ) -> i ℕ.≤ n -> ℝ
∑ᵀ xs i n i≤n with ≤⇒≡∨< i n i≤n
... | inj₁ refl = 0ℝ
∑ᵀ xs i (suc n-1) i≤n | inj₂ (ℕ.s≤s i<n) = ∑ᵀ xs i n-1 i<n + xs n-1

∑-to-∑ᵀ : ∀ (xs : ℕ -> ℝ) -> ∀ m n -> (m≤n : m ℕ.≤ n) -> ∑ xs m n ≃ ∑ᵀ xs m n m≤n
∑-to-∑ᵀ xs zero n ℕ.z≤n = lem n
  where
    lem : ∀ n -> ∑₀ xs n ≃ ∑ᵀ xs 0 n ℕ.z≤n
    lem 0 = ≃-refl
    lem (suc n) with ≤⇒≡∨< 0 (suc n) ℕ.z≤n
    ... | inj₂ 0<n = +-congˡ (xs n) (lem n)
∑-to-∑ᵀ xs (suc m-1) n m≤n with ≤⇒≡∨< (suc m-1) n m≤n
... | inj₁ refl = +-inverseʳ (∑₀ xs (suc m-1))
∑-to-∑ᵀ xs (suc m-1) (suc n-1) m≤n | inj₂ (ℕ.s≤s m<n) = begin
  ∑₀ xs n-1 + xs n-1 - (∑₀ xs m-1 + xs m-1) ≈⟨ solve 3 (λ a b c -> a :+ b :+ c := a :+ c :+ b)
                                               ≃-refl (∑₀ xs n-1) (xs n-1) (- (∑₀ xs m-1 + xs m-1)) ⟩
  ∑₀ xs n-1 - (∑₀ xs m-1 + xs m-1) + xs n-1 ≈⟨ +-congˡ (xs n-1) (∑-to-∑ᵀ xs (suc m-1) n-1 m<n) ⟩
  ∑ᵀ xs (suc m-1) n-1 m<n + xs n-1           ∎
  where
    open ≃-Reasoning
    open ℝ-+-*-Solver

∑ᵀ-triangle-inequality : ∀ (xs : ℕ -> ℝ) -> ∀ m n -> (m≤n : m ℕ.≤ n) -> ∣ ∑ᵀ xs m n m≤n ∣ ≤ ∑ᵀ (λ k -> ∣ xs k ∣) m n m≤n
∑ᵀ-triangle-inequality xs m n m≤n with ≤⇒≡∨< m n m≤n
... | inj₁ refl = ≤-reflexive (≃-reflexive (λ {(suc k-1) -> ℚP.≃-refl}))
∑ᵀ-triangle-inequality xs m (suc n-1) m≤n | inj₂ (ℕ.s≤s m<n) = let n = suc n-1 in begin
  ∣ ∑ᵀ xs m n-1 m<n + xs n-1 ∣                ≤⟨ ∣x+y∣≤∣x∣+∣y∣ (∑ᵀ xs m n-1 m<n) (xs n-1) ⟩
  ∣ ∑ᵀ xs m n-1 m<n ∣ + ∣ xs n-1 ∣            ≤⟨ +-monoˡ-≤ ∣ xs n-1 ∣ (∑ᵀ-triangle-inequality xs m n-1 m<n) ⟩
  ∑ᵀ (λ k -> ∣ xs k ∣) m n-1 m<n + ∣ xs n-1 ∣  ∎
  where open ≤-Reasoning

{-
Note that m ≤ n is required since, if m > n, then ∑ essentially flips m and n and may return a negative number.
-}
∑-triangle-inequality : ∀ (xs : ℕ -> ℝ) -> ∀ m n -> m ℕ.≤ n -> ∣ ∑ xs m n ∣ ≤ ∑ (λ k -> ∣ xs k ∣) m n
∑-triangle-inequality xs m n m≤n = begin
  ∣ ∑ xs m n ∣                 ≈⟨ ∣-∣-cong (∑-to-∑ᵀ xs m n m≤n) ⟩
  ∣ ∑ᵀ xs m n m≤n ∣            ≤⟨ ∑ᵀ-triangle-inequality xs m n m≤n ⟩
  ∑ᵀ (λ k -> ∣ xs k ∣) m n m≤n ≈⟨ ≃-symm (∑-to-∑ᵀ (λ k -> ∣ xs k ∣) m n m≤n) ⟩
  ∑ (λ k -> ∣ xs k ∣) m n       ∎
  where open ≤-Reasoning

∑₀-mono-≤ : ∀ {xs ys} -> (∀ n -> xs n ≤ ys n) -> ∀ n -> ∑₀ xs n ≤ ∑₀ ys n
∑₀-mono-≤ {xs} {ys} xₙ≤yₙ 0 = ≤-refl
∑₀-mono-≤ {xs} {ys} xₙ≤yₙ (suc n) = +-mono-≤ (∑₀-mono-≤ xₙ≤yₙ n) (xₙ≤yₙ n)

∑ᵀ-mono-≤ : ∀ {xs ys} -> (∀ n -> xs n ≤ ys n) -> ∀ m n -> (m≤n : m ℕ.≤ n) -> ∑ᵀ xs m n m≤n ≤ ∑ᵀ ys m n m≤n
∑ᵀ-mono-≤ {xs} {ys} xₙ≤yₙ m n m≤n with ≤⇒≡∨< m n m≤n
... | inj₁ refl = ≤-refl
∑ᵀ-mono-≤ {xs} {ys} xₙ≤yₙ m (suc n-1) m≤n | inj₂ (ℕ.s≤s m<n) = +-mono-≤ (∑ᵀ-mono-≤ xₙ≤yₙ m n-1 m<n) (xₙ≤yₙ n-1)

∑-mono-≤ : ∀ {xs ys} -> (∀ n -> xs n ≤ ys n) -> ∀ m n -> m ℕ.≤ n -> ∑ xs m n ≤ ∑ ys m n
∑-mono-≤ {xs} {ys} xₙ≤yₙ m n m≤n = begin
  ∑ xs m n      ≈⟨ ∑-to-∑ᵀ xs m n m≤n ⟩
  ∑ᵀ xs m n m≤n ≤⟨ ∑ᵀ-mono-≤ xₙ≤yₙ m n m≤n ⟩
  ∑ᵀ ys m n m≤n ≈⟨ ≃-symm (∑-to-∑ᵀ ys m n m≤n) ⟩
  ∑ ys m n       ∎
  where open ≤-Reasoning

neg-flips-∑ : ∀ (xs : ℕ -> ℝ) -> ∀ m n -> - ∑ xs m n ≃ ∑ xs n m
neg-flips-∑ xs 0 0 = ≃-symm 0≃-0
neg-flips-∑ xs 0 (suc n) = ≃-symm (+-identityˡ _)
neg-flips-∑ xs (suc m) zero = ≃-trans (-‿cong (+-identityˡ _)) (neg-involutive (∑₀ xs (suc m)))
neg-flips-∑ xs (suc m) (suc n) = -[x-y]≃y-x (∑₀ xs (suc n)) (∑₀ xs (suc m))

∑ᵀ-mono-≤-weak : ∀ {xs ys : ℕ -> ℝ} -> ∀ {m n} -> (m≤n : m ℕ.≤ n) -> (∀ k -> m ℕ.≤ k × k ℕ.≤ n -> xs k ≤ ys k) ->
                 ∑ᵀ xs m n m≤n ≤ ∑ᵀ ys m n m≤n
∑ᵀ-mono-≤-weak {xs} {ys} {m} {n} m≤n hyp with ≤⇒≡∨< m n m≤n
... | inj₁ refl = ≤-refl
∑ᵀ-mono-≤-weak {xs} {ys} {m} {suc n-1} m≤n hyp | inj₂ (ℕ.s≤s m<n) = +-mono-≤
                             (∑ᵀ-mono-≤-weak m<n (λ k m≤k≤n-1 -> hyp k (proj₁ m≤k≤n-1 , ℕP.≤-trans (proj₂ m≤k≤n-1) (ℕP.n≤1+n n-1))))
                             (hyp n-1 (m<n , ℕP.n≤1+n n-1))

∑-mono-≤-weak : ∀ {xs ys : ℕ -> ℝ} -> ∀ {m n} -> m ℕ.≤ n -> (∀ k -> m ℕ.≤ k × k ℕ.≤ n -> xs k ≤ ys k) ->
                ∑ xs m n ≤ ∑ ys m n
∑-mono-≤-weak {xs} {ys} {m} {n} m≤n hyp = begin
  ∑ xs m n      ≈⟨ ∑-to-∑ᵀ xs m n m≤n ⟩
  ∑ᵀ xs m n m≤n ≤⟨ ∑ᵀ-mono-≤-weak m≤n hyp ⟩
  ∑ᵀ ys m n m≤n ≈⟨ ≃-symm (∑-to-∑ᵀ ys m n m≤n) ⟩
  ∑ ys m n       ∎
  where open ≤-Reasoning

∑0≃0 : ∀ m n -> ∑ (λ k -> 0ℝ) m n ≃ 0ℝ
∑0≃0 zero n = lem n
  where
    lem : ∀ n -> ∑₀ (λ k -> 0ℝ) n ≃ 0ℝ
    lem zero = ≃-refl
    lem (suc n) = ≃-trans (+-identityʳ (∑₀ (λ k -> 0ℝ) n)) (lem n)
∑0≃0 (suc m) n = begin
  ∑₀ (λ k -> 0ℝ) n - (∑₀ (λ k -> 0ℝ) m + 0ℝ) ≈⟨ +-cong (∑0≃0 0 n) (-‿cong (∑0≃0 0 (suc m))) ⟩
  0ℝ - 0ℝ                                    ≈⟨ +-inverseʳ 0ℝ ⟩
  0ℝ                                          ∎
  where open ≃-Reasoning

0≤xₙ⇒0≤∑xₙ : ∀ {xs : ℕ -> ℝ} -> ∀ {m n} -> m ℕ.≤ n -> (∀ k -> m ℕ.≤ k × k ℕ.≤ n -> 0ℝ ≤ xs k) ->
             0ℝ ≤ ∑ xs m n
0≤xₙ⇒0≤∑xₙ {xs} {m} {n} m≤n hyp = begin
  0ℝ                ≈⟨ ≃-symm (∑0≃0 m n) ⟩
  ∑ (λ k -> 0ℝ) m n ≤⟨ ∑-mono-≤-weak m≤n hyp ⟩
  ∑ xs m n           ∎
  where open ≤-Reasoning

nonNegxₙ⇒nonNeg∑xₙ : ∀ {xs : ℕ -> ℝ} -> ∀ {m n} -> m ℕ.≤ n -> (∀ k -> m ℕ.≤ k × k ℕ.≤ n -> NonNegative (xs k)) ->
                     NonNegative (∑ xs m n)
nonNegxₙ⇒nonNeg∑xₙ {xs} {m} {n} m≤n hyp = nonNeg-cong (lem (∑ xs m n))
                                          (0≤xₙ⇒0≤∑xₙ m≤n (λ k m≤k≤n -> nonNeg-cong (≃-symm (lem (xs k))) (hyp k m≤k≤n)))
  where
    lem : ∀ x -> x - 0ℝ ≃ x
    lem x = ≃-trans (+-congʳ x (≃-symm 0≃-0)) (+-identityʳ x)
      
cauchy-convergence : ∀ {xs : ℕ -> ℝ} ->
                     (∀ k -> {k≢0 : k ≢0} -> ∃ λ Nₖ-1 -> ∀ m n -> m ℕ.> n -> m ℕ.≥ suc Nₖ-1 -> n ℕ.≥ suc Nₖ-1 -> ∣ xs m - xs n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆) ->
                     xs isConvergent
cauchy-convergence {xs} hyp = cauchy⇒convergent (cauchy* main)
  where
    main : ∀ k -> {k≢0 : k ≢0} -> ∃ λ Mₖ-1 -> ∀ m n -> m ℕ.≥ suc Mₖ-1 -> n ℕ.≥ suc Mₖ-1 ->
           ∣ xs m - xs n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
    main (suc k-1) = ℕ.pred Mₖ , sub
      where
        open ≤-Reasoning
        k = suc k-1
        Mₖ = suc (proj₁ (hyp k))
        sub : ∀ m n -> m ℕ.≥ Mₖ -> n ℕ.≥ Mₖ -> ∣ xs m - xs n ∣ ≤ (+ 1 / k) ⋆
        sub m n m≥Mₖ n≥Mₖ with ℕP.<-cmp m n
        ... | tri< m<n ¬b ¬c = begin
          ∣ xs m - xs n ∣ ≈⟨ ∣x-y∣≃∣y-x∣ (xs m) (xs n) ⟩
          ∣ xs n - xs m ∣ ≤⟨ proj₂ (hyp k) n m m<n n≥Mₖ m≥Mₖ ⟩
          (+ 1 / k) ⋆      ∎
        ... | tri≈ ¬a refl ¬c = begin
          ∣ xs m - xs m ∣ ≈⟨ ≃-trans (∣-∣-cong (+-inverseʳ (xs m))) (0≤x⇒∣x∣≃x ≤-refl) ⟩
          0ℝ              ≤⟨ p≤q⇒p⋆≤q⋆ 0ℚᵘ (+ 1 / k) (ℚP.nonNegative⁻¹ _) ⟩
          (+ 1 / k) ⋆      ∎
        ... | tri> ¬a ¬b m>n = proj₂ (hyp k) m n m>n m≥Mₖ n≥Mₖ

{-
This is a generalized version of Bishop's Proposition 3.5.

Proposition:
  If ∑yₙ converges and if there is N∈ℕ such that
                ∣xₙ∣ ≤ yₙ                        (n ≥ N),
then ∑xₙ converges.
Proof:
  Let k∈ℕ. Then there is N₂∈ℕ such that 
                     ∣∑ᵢ₌ₙ₊₁ᵐ yᵢ∣ ≤ k⁻¹          (m > n ≥ N₂).
Let N₂∈ℕ such that ∣xₙ∣ ≤ yₙ for n ≥ N₁. Define N = max{N₁, N₂} and let
m > n ≥ N. Then
               ∣∑ᵢ₌ₙ₊₁ᵐ xᵢ∣ ≤ ∑ᵢ₌ₙ₊₁ᵐ ∣xᵢ∣
                            ≤ ∑ᵢ₌ₙ₊₁ᵐ yᵢ  since m > n ≥ N₁
                            ≤ ∣∑ᵢ₌ₙ₊₁ᵐ yᵢ∣
                            ≤ k⁻¹.
Hence ∑xᵢ is convergent.                                               □
[2]
-}
proposition-3-5 : ∀ {xs ys} -> SeriesOf ys isConvergent -> (∃ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> ∣ xs n ∣ ≤ ys n) ->
                    SeriesOf xs isConvergent
proposition-3-5 {xs} {ys} ∑ysCon (N₁-1 , n≥N₁⇒∣xₙ∣≤yₙ) = cauchy-convergence (λ {(suc k-1) ->
                            let k = suc k-1; ∑ysCauchy = cauchyConvergenceTest-if ys ∑ysCon k
                                  ; N₁ = suc N₁-1; N₂ = suc (proj₁ ∑ysCauchy); N = N₁ ℕ.⊔ N₂ in ℕ.pred N ,
                            λ {(suc m-1) (suc n-1) m>n m≥N n≥N ->
                            let m = suc m-1; n = suc n-1; N₂≤N = ℕP.m≤n⊔m N₁ N₂ in begin
  ∣ ∑ xs n m ∣            ≤⟨ ∑-triangle-inequality xs n m (ℕP.<⇒≤ m>n) ⟩
  ∑ (λ i -> ∣ xs i ∣) n m ≤⟨ ∑-mono-≤-weak (ℕP.<⇒≤ m>n) (λ k n≤k≤m -> n≥N₁⇒∣xₙ∣≤yₙ k
                             (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) n≥N) (proj₁ n≤k≤m))) ⟩
  ∑ ys n m                ≤⟨ x≤∣x∣ ⟩
  ∣ ∑ ys n m ∣            ≤⟨ proj₂ ∑ysCauchy n m
                             (ℕP.≤-trans N₂≤N n≥N) (ℕP.≤-trans N₂≤N m≥N) ⟩
  (+ 1 / k) ⋆              ∎}})
  where
    open ≤-Reasoning

absolute⇒isConvergent : ∀ {xs : ℕ -> ℝ} -> SeriesOf xs ConvergesAbsolutely -> SeriesOf xs isConvergent
absolute⇒isConvergent {xs} hyp = proposition-3-5 hyp (0 , (λ n n≥1 -> ≤-refl))

lim : {xs : ℕ -> ℝ} -> xs isConvergent -> ℝ
lim {xs} (ℓ , hyp) = ℓ

reordering : ∀ {xs : ℕ -> ℝ} -> (hyp : SeriesOf xs ConvergesAbsolutely) ->
             ∀ {f : ℕ -> ℕ} -> IsBijection f -> SeriesOf (λ n -> xs (f n)) ConvergesTo lim (absolute⇒isConvergent hyp)
reordering {xs} hyp {f} fBi = {!!}

{-
(xₙ) diverges 
If ∃ε>0 ∀k∈ℕ ∃m,n≥k ( ∣xₘ - xₙ∣ ≥ ε )
-}
data _DivergesBy_ : REL (ℕ -> ℝ) ℝ 0ℓ where
  div* : {f : ℕ -> ℝ} -> {ε : ℝ} -> Positive ε ->
         (∀ k -> {k≢0 : k ≢0} -> (∃ λ m -> ∃ λ n -> m ℕ.≥ k × n ℕ.≥ k × ∣ f m - f n ∣ ≥ ε)) ->
         f DivergesBy ε

_isDivergent : (ℕ -> ℝ) -> Set
f isDivergent = ∃ λ ε -> f DivergesBy ε

cauchy-getter : ∀ {xs} -> xs isCauchy ->
                ∀ k -> {k≢0 : k ≢0} -> ∃ λ Mₖ-1 -> ∀ m n -> m ℕ.≥ suc Mₖ-1 -> n ℕ.≥ suc Mₖ-1 ->
                ∣ xs m - xs n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
cauchy-getter {xs} (cauchy* hyp) = hyp

¬[isConvergent∧isDivergent] : ∀ xs -> ¬ (xs isConvergent × xs isDivergent)
¬[isConvergent∧isDivergent] xs (hyp1 , ε , div* posε hyp2) = let fromdiv = archimedean-ℝ₂ posε; k = suc (proj₁ fromdiv)
                                                                                    ; fromhyp1 = cauchy-getter (convergent⇒cauchy hyp1) k
                                                                                    ; Nₖ = suc (proj₁ fromhyp1)
                                                                                    ; m = proj₁ (hyp2 Nₖ)
                                                                                    ; n = proj₁ (proj₂ (hyp2 Nₖ)) in
                                                                        <-irrefl ≃-refl (begin-strict
  (+ 1 / k) ⋆     <⟨ proj₂ fromdiv ⟩
  ε               ≤⟨ proj₂ (proj₂ (proj₂ (proj₂ (hyp2 Nₖ)))) ⟩
  ∣ xs m - xs n ∣ ≤⟨ proj₂ fromhyp1 m n
                     (proj₁ (proj₂ (proj₂ (hyp2 Nₖ))))
                     (proj₁ (proj₂ (proj₂ (proj₂ (hyp2 Nₖ))))) ⟩
  (+ 1 / k) ⋆      ∎)
  where open ≤-Reasoning

{-
(xₙ) is a subsequence of (yₙ) if there is h : ℕ -> ℕ such that
                              xₙ = yₕ₍ₙ₎                 (n∈ℕ)
and
                            h(n) < h(n+1)                (n∈ℕ).
[3]
-}
data _SubsequenceOf_ : Rel (ℕ -> ℝ) 0ℓ where
  subseq* : {xs ys : ℕ -> ℝ} -> (∃ λ (f : ℕ -> ℕ) ->
            (∀ n -> xs n ≃ ys (f n)) × (∀ n -> f n ℕ.< f (suc n))) ->
            xs SubsequenceOf ys

{-
Not sure what a more meaningful name for this is yet.
-}
subsequence-helper : ∀ {f : ℕ -> ℕ} -> ∀ (k : ℕ) -> (∀ n -> f n ℕ.< f (suc n)) ->
                     ∃ λ (N : ℕ) -> ∀ n -> n ℕ.> N -> f n ℕ.> k  
subsequence-helper {f} zero hyp = 0 , λ {(suc n-1) n>0 → ℕP.<-transʳ ℕ.z≤n (hyp n-1)}
subsequence-helper {f} (suc k) hyp = let ih = subsequence-helper k hyp; N = suc (proj₁ ih) in
                                     N , λ {(suc n-1) (ℕ.s≤s n>N) → ℕP.<-transʳ (proj₂ ih n-1 n>N) (hyp n-1)}

f[n]<f[n+1]⇒n≤f[n] : ∀ {f : ℕ -> ℕ} -> (∀ n -> f n ℕ.< f (suc n)) -> (∀ n -> n ℕ.≤ f n)
f[n]<f[n+1]⇒n≤f[n] {f} f[n]<f[n+1] 0 = ℕ.z≤n
f[n]<f[n+1]⇒n≤f[n] {f} f[n]<f[n+1] (suc n) = ℕP.<-transʳ (f[n]<f[n+1]⇒n≤f[n] f[n]<f[n+1] n) (f[n]<f[n+1] n)

{-
As per Bishop, the series ∑xᵢ is divergent if there is positive r∈ℝ such that ∣xₙ∣ ≥ r for infinitely many n.
Alternatively, ∑xᵢ is divergent if there is positive r∈ℝ and a subsequence (yₙ) of (xₙ) such that ∣yₙ∣ ≥ r for
all n∈ℕ.

Proposition:
  If there is positive r∈ℝ such that r ≤ ∣xₙ∣ for infinitely many n, then ∑xᵢ diverges.
Proof:
  Let (xₕ₍ₙ₎) be a subsequence of (xₙ) such that r ≤ ∣xₕ₍ₙ₎∣ for all n∈ℕ. Note that h(n) < h(n+1) for all n∈ℕ, 
so n ≤ h(n) for all n∈ℕ. Let k∈ℕ. Then k ≤ f(k), and we have:
  ∣ ∑ xs 0 h(k)+1 - ∑ xs 0 h(k) ∣ = ∣ xₕ₍ₖ₎ ∣ ≥ r.
Thus the sum diverges.                                                                                       □
-}
subsequence-divergence-test : ∀ {xs : ℕ -> ℝ} ->
                              (∃ λ (r : ℝ) -> ∃ λ (ys : ℕ -> ℝ) -> Positive r × ys SubsequenceOf xs × (∀ n -> ∣ ys n ∣ ≥ r)) ->
                              SeriesOf xs isDivergent
subsequence-divergence-test {xs} (r , ys , posr , subseq* (f , yₙ⊂xₙ) , ∣yₙ∣≥r) =
                            r , div* posr (λ k -> let k≤f[k] = f[n]<f[n+1]⇒n≤f[n] (proj₂ yₙ⊂xₙ) k in
                            suc (f k) , f k , ℕP.≤-trans k≤f[k] (ℕP.n≤1+n (f k)) , k≤f[k] , (begin
  r                                          ≤⟨ ∣yₙ∣≥r k ⟩
  ∣ ys k ∣                                   ≈⟨ ∣-∣-cong (proj₁ yₙ⊂xₙ k) ⟩
  ∣ xs (f k) ∣                               ≈⟨ ∣-∣-cong (≃-symm (+-identityʳ (xs (f k)))) ⟩
  ∣ xs (f k) + 0ℝ ∣                          ≈⟨ ∣-∣-cong (+-congʳ (xs (f k)) (≃-symm (+-inverseʳ (∑₀ xs (f k))))) ⟩
  ∣ xs (f k) + (∑₀ xs (f k) - ∑₀ xs (f k)) ∣ ≈⟨ ∣-∣-cong (solve 3 (λ a b c -> a :+ (b :+ c) := b :+ a :+ c)
                                                ≃-refl (xs (f k)) (∑₀ xs (f k)) (- ∑₀ xs (f k))) ⟩
  ∣ ∑₀ xs (suc (f k)) - ∑₀ xs (f k) ∣         ∎))
  where
    open ≤-Reasoning
    open ℝ-+-*-Solver

{-
[4]
Proposition:
  Let (yₙ) be a sequence with a nonnegative tail (i.e. ∃N₁∈ℕ ∀n≥N₁[yₙ ≥ 0]). Suppose that
∃N₂∈ℕ ∀n≥N₂[xₙ ≥ yₙ], and that ∑yᵢ is divergent. Then ∑xᵢ is divergent.
Proof:
  Let ε>0 such that ∑yᵢ diverges by ε. Define N = max{N₁, N₂}. Then there is m,n ≥ N such that
                                     ∑ᵢ₌ₙᵐ yᵢ = ∣∑ᵢ₌ₙᵐ yᵢ∣ ≥ ε.
Suppose, WLOG, that m ≥ n. Then:
                       ∣∑ᵢ₌ₙᵐ xᵢ∣ = ∑ᵢ₌ₙᵐ xᵢ
                                  ≥ ∑ᵢ₌ₙᵐ yᵢ
                                  ≥ ε.
Thus ∑xᵢ diverges by ε.                                                                      □

Bishop assumes that 
  (i)  (xₙ) is a sequence of nonnegative terms, and
  (ii) (yₙ) is a nonnegative sequence.

The first could obviously be removed since xₙ ≥ yₙ eventually, and the second could be modified
so that yₙ ≥ 0 eventually. The distinction doesn't matter informally of course, but we adopt it
since we don't have the benefit of saying "it's a trivial extension of this result" without proof.
-}
comparison-test-divergence : ∀ {xs ys : ℕ -> ℝ} -> (∃ λ N₁ -> ∀ n -> n ℕ.≥ N₁ -> NonNegative (ys n)) ->
                             SeriesOf ys isDivergent -> (∃ λ N₂ -> ∀ n -> n ℕ.≥ N₂ -> xs n ≥ ys n) ->
                             SeriesOf xs isDivergent
comparison-test-divergence {xs} {ys} (N₁ , n≥N₁⇒yₙ≥0) (ε , div* posε div∑yₙ) (N₂ , n≥N₂⇒xₙ≥yₙ) = ε , div* posε main
  where
    main : ∀ k -> {k ≢0} -> ∃ λ m -> ∃ λ n -> m ℕ.≥ k × n ℕ.≥ k × ∣ ∑₀ xs m - ∑₀ xs n ∣ ≥ ε
    main (suc N₃-1) = let m = proj₁ (div∑yₙ N); n = proj₁ (proj₂ (div∑yₙ N))
                            ; N≤m = proj₁ (proj₂ (proj₂ (div∑yₙ N))); N≤n = proj₁ (proj₂ (proj₂ (proj₂ (div∑yₙ N))))
                            ; ∑yₙhyp = proj₂ (proj₂ (proj₂ (proj₂ (div∑yₙ N)))) in
                            m , n , ℕP.≤-trans N₃≤N N≤m , ℕP.≤-trans N₃≤N N≤n ,
                            [ (λ m≥n -> sub m n N≤m N≤n m≥n ∑yₙhyp) ,
                              (λ m≤n -> ≤-respʳ-≃ (∣x-y∣≃∣y-x∣ (∑₀ xs n) (∑₀ xs m)) (sub n m N≤n N≤m m≤n
                                        (≤-respʳ-≃ (∣x-y∣≃∣y-x∣ (∑₀ ys m) (∑₀ ys n)) ∑yₙhyp))) ]′ (ℕP.≤-total n m)
      where
        open ≤-Reasoning
        N₃ = suc N₃-1
        N = suc (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃)
        N₁≤N = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃)) (ℕP.n≤1+n (ℕ.pred N))
        N₂≤N = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃)) (ℕP.n≤1+n (ℕ.pred N))
        N₃≤N = ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂) N₃) (ℕP.n≤1+n (ℕ.pred N))
        sub : ∀ m n -> m ℕ.≥ N -> n ℕ.≥ N -> m ℕ.≥ n -> ∣ ∑₀ ys m - ∑₀ ys n ∣ ≥ ε -> ∣ ∑₀ xs m - ∑₀ xs n ∣ ≥ ε
        sub (suc m-1) (suc n-1) m≥N n≥N m≥n hyp = let m = suc m-1; n = suc n-1 in begin
          ε            ≤⟨ hyp ⟩
          ∣ ∑ ys n m ∣ ≈⟨ nonNegx⇒∣x∣≃x (nonNegxₙ⇒nonNeg∑xₙ m≥n (λ k n≤k≤m -> n≥N₁⇒yₙ≥0 k
                          (ℕP.≤-trans (ℕP.≤-trans N₁≤N n≥N) (proj₁ n≤k≤m)))) ⟩
          ∑ ys n m     ≤⟨ ∑-mono-≤-weak m≥n (λ k n≤k≤m -> n≥N₂⇒xₙ≥yₙ k
                          (ℕP.≤-trans (ℕP.≤-trans N₂≤N n≥N) (proj₁ n≤k≤m))) ⟩
          ∑ xs n m     ≤⟨ x≤∣x∣ ⟩
          ∣ ∑ xs n m ∣   ∎

pow : ℝ -> ℕ -> ℝ
pow x 0 = 1ℝ
pow x (suc n) = pow x n * x

pow-cong : ∀ {x y} -> ∀ n -> x ≃ y -> pow x n ≃ pow y n
pow-cong {x} {y} zero x≃y = ≃-refl
pow-cong {x} {y} (suc n) x≃y = *-cong (pow-cong n x≃y) x≃y

xⁿxᵐ≃xⁿ⁺ᵐ : ∀ x -> ∀ n m -> (pow x n) * (pow x m) ≃ pow x (n ℕ.+ m)
xⁿxᵐ≃xⁿ⁺ᵐ x zero m = *-identityˡ (pow x m)
xⁿxᵐ≃xⁿ⁺ᵐ x (suc n) m = begin
  pow x n * x * pow x m   ≈⟨ ≃-trans (≃-trans
                             (*-assoc (pow x n) x (pow x m))
                             (*-congˡ (*-comm x (pow x m))))
                             (≃-symm (*-assoc (pow x n) (pow x m) x)) ⟩
  pow x n * pow x m * x   ≈⟨ *-congʳ (xⁿxᵐ≃xⁿ⁺ᵐ x n m) ⟩
  pow x (n ℕ.+ m) * x     ≈⟨ ≃-refl ⟩
  pow x (1 ℕ.+ (n ℕ.+ m)) ≡⟨ cong (λ k -> pow x k) (sym (ℕP.+-assoc 1 n m)) ⟩
  pow x ((1 ℕ.+ n) ℕ.+ m)  ∎
  where open ≃-Reasoning

testingCase : ∀ x -> ∀ n m -> (pow x n) * (pow x m) ≃ pow x (n ℕ.+ m)
testingCase x zero m = *-identityˡ (pow x m)
testingCase x (suc n) m = begin
  pow x n * x * pow x m ≈⟨ solve 3 (λ a b c -> a ⊗ b ⊗ c ⊜ a ⊗ c ⊗ b) ≃-refl (pow x n) x (pow x m) ⟩
  pow x n * pow x m * x   ≈⟨ {!!} ⟩
  pow x ((suc n) ℕ.+ m)  ∎
  where
    open ≃-Reasoning
    open import RingSolverB

archimedean-ℝ₃ : ∀ {x} y -> Positive x -> ∃ λ n-1 -> (+ (suc n-1) / 1) ⋆ * x > y
archimedean-ℝ₃ {x} y posx = let x≄0 = inj₂ (posx⇒0<x posx); x⁻¹ = (x ⁻¹) x≄0
                                    ; arch = fast-archimedean-ℝ (y * x⁻¹); n = suc (proj₁ arch) in
                            ℕ.pred n , (begin-strict
  y               ≈⟨ ≃-symm (≃-trans (≃-trans (*-assoc y x⁻¹ x)
                     (*-congˡ {y} {x⁻¹ * x} {1ℝ} (*-inverseˡ x x≄0))) (*-identityʳ y)) ⟩
  y * x⁻¹ * x     <⟨ *-monoˡ-<-pos {x} posx {y * x⁻¹} {(+ n / 1) ⋆} (proj₂ arch) ⟩
  (+ n / 1) ⋆ * x  ∎)
  where open ≤-Reasoning

abstract
  fast-archimedean-ℝ₃ : ∀ {x} y -> Positive x -> ∃ λ n-1 -> (+ (suc n-1) / 1) ⋆ * x > y
  fast-archimedean-ℝ₃ = archimedean-ℝ₃

x≤y∧posx⇒y⁻¹≤x⁻¹ : ∀ {x y} -> x ≤ y -> Positive x -> (x≄0 : x ≄0) -> (y≄0 : y ≄0) ->
                   (y ⁻¹) y≄0 ≤ (x ⁻¹) x≄0
x≤y∧posx⇒y⁻¹≤x⁻¹ {x} {y} x≤y posx x≄0 y≄0 = let x⁻¹ = (x ⁻¹) x≄0; y⁻¹ = (y ⁻¹) y≄0 in begin
  y⁻¹             ≈⟨ ≃-symm (≃-trans (*-congˡ {y⁻¹} {x * x⁻¹} {1ℝ} (*-inverseʳ x x≄0)) (*-identityʳ y⁻¹)) ⟩
  y⁻¹ * (x * x⁻¹) ≤⟨ *-monoˡ-≤-nonNeg {x * x⁻¹} {y⁻¹} {y * x⁻¹}
                     (*-monoʳ-≤-nonNeg {x} {x⁻¹} {y} x≤y (nonNegx⇒nonNegx⁻¹ {x} (pos⇒nonNeg posx) x≄0))
                     (nonNegx⇒nonNegx⁻¹ {y} (pos⇒nonNeg (0<x⇒posx (<-≤-trans (posx⇒0<x posx) x≤y))) y≄0) ⟩
  y⁻¹ * (y * x⁻¹) ≈⟨ ≃-trans (≃-trans (≃-symm (*-assoc y⁻¹ y x⁻¹))
                     (*-congʳ {x⁻¹} {y⁻¹ * y} {1ℝ} (*-inverseˡ y y≄0))) (*-identityˡ x⁻¹) ⟩
  x⁻¹              ∎
  where open ≤-Reasoning

x<y⇒∃ε>0[x<x+ε<y] : ∀ {x y} -> x < y -> ∃ λ ε -> Positive ε × x < (x + ε) < y
x<y⇒∃ε>0[x<x+ε<y] {x} {y} x<y = {!!}

[x+y]*[z+w]≃xz+xw+yz+yw : ∀ x y z w -> (x + y) * (z + w) ≃ x * z + x * w + y * z + y * w
[x+y]*[z+w]≃xz+xw+yz+yw x y z w = {!!}

x²ⁿ≥0 : ∀ x -> ∀ n -> pow x (2 ℕ.* n) ≥ 0ℝ
x²ⁿ≥0 x n = {!!}

{-
(1 + x)ⁿ ≥ 1 + nx
n = 0: Easy
n∈ℕ:
(1 + x)ⁿ⁺¹ = (1 + x) * (1 + x)ⁿ
           ≥ (1 + x) * (1 + nx)
           = 1 + (n + 1)x + nx²
           ≥ 1 + (n + 1)x

(1 + x) * (1 + r-1 * x)
= 1 * 1 + 1 * (r-1 * x) + x * 1 + x * r-1 * x
= 1 + (1 + r-1) * x + r-1 * x²

(a + bx) * (c + dx) = ac + adx + bcx + bdx²
                    = ac + (ad + bc)x + bdx²
(1 + x) * (1 + rx)
= 1 * 1 + 1 * rx + x * 1 + x * rx
= 1 + (r + 1)x + rx²
-}
bernoullis-inequality : ∀ {x} -> x ≥ - 1ℝ -> ∀ (r : ℕ) -> pow (1ℝ + x) r ≥ 1ℝ + (+ r / 1) ⋆ * x
bernoullis-inequality {x} x≥-1 zero = begin
  1ℝ + 0ℝ * x ≈⟨ +-congʳ 1ℝ (*-zeroˡ x) ⟩
  1ℝ + 0ℝ     ≈⟨ +-identityʳ 1ℝ ⟩
  1ℝ           ∎
  where open ≤-Reasoning
bernoullis-inequality {x} x≥-1 (suc r-1) = begin
  1ℝ + ((+ suc r-1) / 1) ⋆ * x                                      ≤⟨ ≤-respˡ-≃ (+-identityʳ _)
                                                                       (+-monoʳ-≤ (1ℝ + (+ suc r-1 / 1) ⋆ * x)
                                                                       (nonNegx⇒0≤x (nonNegx,y⇒nonNegx*y
                                                                       (nonNegp⇒nonNegp⋆ (+ r-1 / 1) _) (0≤x⇒nonNegx (x²ⁿ≥0 x 1))))) ⟩
  1ℝ + ((+ suc r-1) / 1) ⋆ * x + (+ r-1 / 1) ⋆ * pow x 2            ≈⟨ {!!} ⟩
  1ℝ * 1ℝ + (1ℝ + 1ℝ * (+ r-1 / 1) ⋆) * x + (+ r-1 / 1) ⋆ * (x * x) ≈⟨ solve 3 (λ 1ₓ r x ->
                                                                       (((1ₓ ⊗ 1ₓ) ⊕ ((1ₓ ⊕ (1ₓ ⊗ r)) ⊗ x)) ⊕ (r ⊗ (x ⊗ x))) ⊜
                                                                       ((1ₓ ⊕ x) ⊗ (1ₓ ⊕ (r ⊗ x)))) ≃-refl 1ℝ ((+ r-1 / 1) ⋆) x ⟩
  (1ℝ + x) * (1ℝ + (+ r-1 / 1) ⋆ * x)                               ≤⟨ *-monoˡ-≤-nonNeg (bernoullis-inequality x≥-1 r-1)
                                                                       (0≤x⇒nonNegx (≤-respˡ-≃ (+-inverseʳ 1ℝ) (+-monoʳ-≤ 1ℝ x≥-1))) ⟩
  (1ℝ + x) * pow (1ℝ + x) r-1                                       ≈⟨ *-comm (1ℝ + x) (pow (1ℝ + x) r-1) ⟩
  pow (1ℝ + x) (suc r-1)                                             ∎
  where
    open ≤-Reasoning
    open import RingSolverB
{-
(1 + x) * (1 + (r * x)) = 
-}

{-
x≄0⇒xⁿ≄0 : ∀ {x} -> ∀ n -> x ≄0 -> pow x n ≄0
x≄0⇒xⁿ≄0 {x} zero x≄0 = inj₂ (p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _))
x≄0⇒xⁿ≄0 {x} (suc n) x≄0 = x≄0∧y≄0⇒x*y≄0 (x≄0⇒xⁿ≄0 n x≄0) x≄0

[xⁿ]⁻¹≃[x⁻¹]ⁿ : ∀ {x} -> (x≄0 : x ≄0) -> ∀ n -> (xⁿ≄0 : pow x n ≄0) -> ((pow x n) ⁻¹) xⁿ≄0 ≃ pow ((x ⁻¹) x≄0) n
[xⁿ]⁻¹≃[x⁻¹]ⁿ {x} x≄0 zero xⁿ≄0 = ⋆-distrib-⁻¹ 1ℚᵘ xⁿ≄0
[xⁿ]⁻¹≃[x⁻¹]ⁿ {x} x≄0 (suc n) xⁿ⁺¹≄0 = let xⁿ≄0 = x≄0⇒xⁿ≄0 {x} n x≄0 in begin
  ((pow x n * x) ⁻¹) xⁿ⁺¹≄0        ≈⟨ fast-⁻¹-distrib-* {pow x n} {x} xⁿ≄0 x≄0 xⁿ⁺¹≄0 ⟩
  ((pow x n) ⁻¹) xⁿ≄0 * (x ⁻¹) x≄0 ≈⟨ *-congʳ {(x ⁻¹) x≄0} {(pow x n ⁻¹) xⁿ≄0} {pow ((x ⁻¹) x≄0) n}
                                      ([xⁿ]⁻¹≃[x⁻¹]ⁿ {x} x≄0 n xⁿ≄0) ⟩
  pow ((x ⁻¹) x≄0) n * (x ⁻¹) x≄0   ∎
  where open ≃-Reasoning

1≤x∧m≤n⇒xᵐ≤xⁿ : ∀ {x} -> ∀ {m n} -> 1ℝ ≤ x -> m ℕ.≤ n -> pow x m ≤ pow x n
1≤x∧m≤n⇒xᵐ≤xⁿ {x} {zero} {zero} 1≤x m≤n = ≤-refl
1≤x∧m≤n⇒xᵐ≤xⁿ {x} {zero} {suc n} 1≤x m≤n = lem (suc n)
  where
    open ≤-Reasoning
    lem : ∀ n -> 1ℝ ≤ pow x n
    lem zero = ≤-refl
    lem (suc n) = begin
      1ℝ          ≤⟨ 1≤x ⟩
      x           ≈⟨ ≃-symm (*-identityˡ x) ⟩
      1ℝ * x      ≤⟨ *-monoʳ-≤-nonNeg (lem n)
                     (0≤x⇒nonNegx (≤-trans (p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ _)) 1≤x)) ⟩
      pow x n * x  ∎
1≤x∧m≤n⇒xᵐ≤xⁿ {x} {suc m} {suc n} 1≤x (ℕ.s≤s m≤n) = *-monoʳ-≤-nonNeg (1≤x∧m≤n⇒xᵐ≤xⁿ 1≤x m≤n)
                                                    (0≤x⇒nonNegx (≤-trans (p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ _)) 1≤x))

nonNegx⇒nonNegxⁿ : ∀ {x} -> ∀ n -> NonNegative x -> NonNegative (pow x n)
nonNegx⇒nonNegxⁿ {x} zero nonx = nonNegp⇒nonNegp⋆ 1ℚᵘ _
nonNegx⇒nonNegxⁿ {x} (suc n) nonx = nonNegx,y⇒nonNegx*y (nonNegx⇒nonNegxⁿ n nonx) nonx

0<r<1⇒rⁿ→0 : ∀ {r} -> 0ℝ < r < 1ℝ ->
             ∀ j -> {j≢0 : j ≢0} -> ∃ λ Nₖ-1 -> ∀ n -> n ℕ.≥ suc Nₖ-1 -> pow r n ≤ ((+ 1 / j) {j≢0}) ⋆
0<r<1⇒rⁿ→0 {r} (0<r , r<1) (suc j-1) = let j = suc j-1; j⋆≄0 = ∣↥p∣≢0⇒p⋆≄0 (+ j / 1) _; N = suc (proj₁ (lem j)) in
                                       ℕ.pred N , λ n n≥N -> begin
      pow r n                  ≈⟨ pow-cong n (≃-symm (⁻¹-involutive {r} r≄0 t≄0)) ⟩
      pow ((t ⁻¹) t≄0) n       ≈⟨ ≃-symm ([xⁿ]⁻¹≃[x⁻¹]ⁿ {t} t≄0 n (tⁿ≄0 n)) ⟩
      ((pow t n) ⁻¹) (tⁿ≄0 n)  ≤⟨ x≤y∧posx⇒y⁻¹≤x⁻¹ {(+ j / 1) ⋆} {pow t n} (proj₂ (lem j) n n≥N) (posp⇒posp⋆ (+ j / 1) _) j⋆≄0 (tⁿ≄0 n) ⟩
      (((+ j / 1) ⋆) ⁻¹) j⋆≄0  ≈⟨ ⋆-distrib-⁻¹ (+ j / 1) j⋆≄0 ⟩
      (+ 1 / j) ⋆               ∎
  where
    open ≤-Reasoning
    r≄0 = inj₂ 0<r
    t = (r ⁻¹) r≄0
    1<t : 1ℝ < t
    1<t = let 0<1 = p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _); 1≄0 = inj₂ 0<1 in begin-strict
      1ℝ                     ≈⟨ ≃-symm (⋆-distrib-⁻¹ 1ℚᵘ 1≄0) ⟩
      (((+ 1 / 1) ⋆) ⁻¹) 1≄0 <⟨ x<y∧posx,y⇒y⁻¹<x⁻¹ {r} {1ℝ} r<1 r≄0 1≄0 (0<x⇒posx 0<r) (0<x⇒posx 0<1) ⟩
      t                       ∎
    t≄0 = inj₂ (0<x⇒0<x⁻¹ {r} r≄0 0<r)
    tⁿ≄0 : ∀ n -> pow t n ≄0
    tⁿ≄0 0 = inj₂ (p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _))
    tⁿ≄0 (suc n) = x≄0∧y≄0⇒x*y≄0 (tⁿ≄0 n) t≄0
    arch = fast-archimedean-ℝ₃ {t - 1ℝ} 1ℝ 1<t
    k = suc (proj₁ arch)

    -1≤t-1 : - 1ℝ ≤ t - 1ℝ
    -1≤t-1 = begin
      - 1ℝ        ≈⟨ ≃-symm (⋆-distrib-neg 1ℚᵘ) ⟩
      (ℚ.- 1ℚᵘ) ⋆ ≤⟨ p≤q⇒p⋆≤q⋆ (ℚ.- 1ℚᵘ) 0ℚᵘ (ℚP.nonPositive⁻¹ _) ⟩
      0ℝ          ≤⟨ x≤y⇒0≤y-x (<⇒≤ 1<t) ⟩
      t - 1ℝ       ∎

    t≃1+[t-1] : t ≃ 1ℝ + (t - 1ℝ)
    t≃1+[t-1] = begin-equality
      t               ≈⟨ ≃-symm (+-identityˡ t) ⟩
      0ℝ + t          ≈⟨ +-congˡ t (≃-symm (+-inverseʳ 1ℝ)) ⟩
      (1ℝ - 1ℝ) + t   ≈⟨ +-assoc 1ℝ (- 1ℝ) t ⟩
      1ℝ + (- 1ℝ + t) ≈⟨ +-congʳ 1ℝ (+-comm (- 1ℝ) t) ⟩
      1ℝ + (t - 1ℝ)    ∎

    tᵏⁿ≥n : ∀ n -> {n ≢0} -> pow t (k ℕ.* n) ≥ (+ n / 1) ⋆
    tᵏⁿ≥n (suc n-1) = let n = suc n-1 in begin
      (+ n / 1) ⋆                          ≈⟨ ≃-symm (*-identityˡ ((+ n / 1) ⋆)) ⟩
      1ℝ * (+ n / 1) ⋆                     ≤⟨ *-monoʳ-≤-nonNeg {1ℝ} {(+ n / 1) ⋆} {(+ k / 1) ⋆ * (t - 1ℝ)}
                                              (<⇒≤ (proj₂ arch)) (nonNegp⇒nonNegp⋆ (+ n / 1) _) ⟩
      (+ k / 1) ⋆ * (t - 1ℝ) * (+ n / 1) ⋆ ≈⟨ ≃-trans (≃-trans
                                              (*-assoc ((+ k / 1) ⋆) (t - 1ℝ) ((+ n / 1) ⋆))
                                              (*-congˡ {(+ k / 1) ⋆} (*-comm (t - 1ℝ) ((+ n / 1) ⋆))))
                                              (≃-symm (*-assoc ((+ k / 1) ⋆) ((+ n / 1) ⋆) (t - 1ℝ))) ⟩
      (+ k / 1) ⋆ * (+ n / 1) ⋆ * (t - 1ℝ) ≈⟨ *-congʳ {t - 1ℝ} (≃-symm (⋆-distrib-* (+ k / 1) (+ n / 1))) ⟩
      (+ (k ℕ.* n) / 1) ⋆ * (t - 1ℝ)       ≤⟨ ≤-respˡ-≃ (+-identityˡ ((+ (k ℕ.* n) / 1) ⋆ * (t - 1ℝ)))
                                              (+-monoˡ-≤ ((+ (k ℕ.* n) / 1) ⋆ * (t - 1ℝ)) (p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ _))) ⟩
      1ℝ + (+ (k ℕ.* n) / 1) ⋆ * (t - 1ℝ)  ≤⟨ bernoullis-inequality {t - 1ℝ} -1≤t-1 (k ℕ.* n) ⟩
      pow (1ℝ + (t - 1ℝ)) (k ℕ.* n)        ≈⟨ pow-cong (k ℕ.* n) (≃-symm t≃1+[t-1]) ⟩
      pow t (k ℕ.* n)                       ∎

    lem : ∀ j -> {j ≢0} -> ∃ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> pow t n ≥ (+ j / 1) ⋆
    lem (suc j-1) = let j = suc j-1 in ℕ.pred (k ℕ.* j) , λ n n≥kj -> begin
      (+ j / 1) ⋆         ≤⟨ tᵏⁿ≥n j ⟩
      pow t (k ℕ.* j)     ≤⟨ 1≤x∧m≤n⇒xᵐ≤xⁿ {t} {k ℕ.* j} {n} (<⇒≤ 1<t) n≥kj ⟩
      pow t n              ∎

abstract
  fast-0<r<1⇒rⁿ→0 : ∀ {r} -> 0ℝ < r < 1ℝ ->
                    ∀ j -> {j≢0 : j ≢0} -> ∃ λ Nₖ-1 -> ∀ n -> n ℕ.≥ suc Nₖ-1 -> pow r n ≤ ((+ 1 / j) {j≢0}) ⋆
  fast-0<r<1⇒rⁿ→0 = 0<r<1⇒rⁿ→0

x≤y∧nonNegx⇒xⁿ≤yⁿ : ∀ {x y} -> ∀ n -> x ≤ y -> NonNegative x -> pow x n ≤ pow y n
x≤y∧nonNegx⇒xⁿ≤yⁿ {x} {y} zero x≤y nonx = ≤-refl
x≤y∧nonNegx⇒xⁿ≤yⁿ {x} {y} (suc n) x≤y nonx = *-mono-≤ (nonNegx⇒nonNegxⁿ n nonx) nonx (x≤y∧nonNegx⇒xⁿ≤yⁿ n x≤y nonx) x≤y

posx⇒posxⁿ : ∀ {x} -> ∀ n -> Positive x -> Positive (pow x n)
posx⇒posxⁿ {x} zero posx = posp⇒posp⋆ 1ℚᵘ _
posx⇒posxⁿ {x} (suc n) posx = posx,y⇒posx*y (posx⇒posxⁿ n posx) posx

x<y∧nonNegx⇒xⁿ<yⁿ : ∀ {x y} -> ∀ n -> {n ≢0} -> x < y -> NonNegative x -> pow x n < pow y n
x<y∧nonNegx⇒xⁿ<yⁿ {x} {y} 1 x<y nonx = *-monoʳ-<-pos (posp⇒posp⋆ 1ℚᵘ _) x<y
x<y∧nonNegx⇒xⁿ<yⁿ {x} {y} (suc (suc n)) x<y nonx = begin-strict
  pow x (suc n) * x ≤⟨ *-monoˡ-≤-nonNeg (<⇒≤ x<y) (nonNegx⇒nonNegxⁿ (suc n) nonx) ⟩
  pow x (suc n) * y <⟨ *-monoˡ-<-pos (0<x⇒posx (≤-<-trans (nonNegx⇒0≤x nonx) x<y)) (x<y∧nonNegx⇒xⁿ<yⁿ (suc n) x<y nonx) ⟩
  pow y (suc n) * y  ∎
  where open ≤-Reasoning

∣xⁿ∣≃∣x∣ⁿ : ∀ x -> ∀ n -> ∣ pow x n ∣ ≃ pow ∣ x ∣ n
∣xⁿ∣≃∣x∣ⁿ x zero = nonNegx⇒∣x∣≃x (0≤x⇒nonNegx (p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ _)))
∣xⁿ∣≃∣x∣ⁿ x (suc n) = begin
  ∣ pow x n * x ∣     ≈⟨ ∣x*y∣≃∣x∣*∣y∣ (pow x n) x ⟩
  ∣ pow x n ∣ * ∣ x ∣ ≈⟨ *-congʳ (∣xⁿ∣≃∣x∣ⁿ x n) ⟩
  pow ∣ x ∣ n * ∣ x ∣  ∎
  where open ≃-Reasoning

{-
(1 + x)ⁿ ≥ 1 + nx
x ≥ -1

(1+x)⁰ = 1
1 + 0x = 1


(1 + x)ⁿ⁺¹ = (1 + x)ⁿ * (1 + x)
           ≥ (1 + nx) * (1 + x)
           = 1 + (n+1)x + nx²
           ≥ 1 + (n+1)x

[5]
This proof is an altered and further constructivized version of the proof at 
https://math.stackexchange.com/questions/1253129/as-the-limit-of-n-goes-to-infinity-prove-that-xn-0-if-operatornameabs  

Proposition:
  If ∣r∣ < 1, then (rⁿ)→0.
Proof:
  Let ε∈ℝ⁺ such that ∣r∣ < ∣r∣ + ε and 0 < ∣r∣ + ε < 1. If ([∣r∣ + ε]ⁿ)→0, then
(∣r∣ⁿ)→0, and so (rⁿ)→0. Let t = (∣r∣ + ε)⁻¹. Then t = 1 + (t - 1), where t - 1 > 0.
By the Archimedean Property, there is k∈ℕ such that k(t - 1) > 1. We have, for n∈ℕ:
             tᵏⁿ = (1 + (t-1))ᵏⁿ
                 ≥ 1 + k(t-1)n   by Bernoulli's inequality
                 > 1 + n         since k(t-1) > 1
                 > n,
so tᵏⁿ > n for all n∈ℕ (⋆).
  Let j∈ℕ and let N = k * j. Let n ≥ N. Then (∣r∣ + ε)ⁿ ≤ j⁻¹ ⇔ j ≤ tⁿ. We have:
           j < tᵏʲ by ⋆
             ≤ tⁿ  since n ≥ kj and (tⁿ) is an increasing sequence.
Thus ([∣r∣ + ε]ⁿ)→0, and so (rⁿ)→0.                                               □ -}
∣r∣<1⇒rⁿ→0 : ∀ {r} -> ∣ r ∣ < 1ℝ -> (λ n -> pow r n) ConvergesTo 0ℝ
∣r∣<1⇒rⁿ→0 {r} ∣r∣<1 = con* (λ {(suc k-1) -> let k = suc k-1; Nₖ-getter = fast-0<r<1⇒rⁿ→0 {∣ r ∣ + ε} (0<∣r∣+ε , (proj₂ (proj₂ (ε-prop))))
                                                  ; Nₖ = suc (proj₁ (Nₖ-getter k)) in ℕ.pred Nₖ , λ n n≥Nₖ -> begin
  ∣ pow r n - 0ℝ ∣  ≈⟨ ∣-∣-cong (≃-trans (+-congʳ (pow r n) (≃-symm 0≃-0)) (+-identityʳ (pow r n))) ⟩
  ∣ pow r n ∣       ≈⟨ ∣xⁿ∣≃∣x∣ⁿ r n ⟩
  pow ∣ r ∣ n       ≤⟨ x≤y∧nonNegx⇒xⁿ≤yⁿ {∣ r ∣} {∣ r ∣ + ε} n ∣r∣≤∣r∣+ε (nonNeg∣x∣ r) ⟩
  pow (∣ r ∣ + ε) n ≤⟨ proj₂ (Nₖ-getter k) n n≥Nₖ ⟩
  (+ 1 / k) ⋆        ∎})
  where
    open ≤-Reasoning
    ε-prop = proj₂ (x<y⇒∃ε>0[x<x+ε<y] {∣ r ∣} {1ℝ} ∣r∣<1)
    ε = proj₁ (x<y⇒∃ε>0[x<x+ε<y] {∣ r ∣} {1ℝ} ∣r∣<1)

    0<∣r∣+ε : 0ℝ < ∣ r ∣ + ε
    0<∣r∣+ε = begin-strict
      0ℝ        <⟨ posx⇒0<x (proj₁ ε-prop) ⟩
      ε         ≤⟨ ≤-respˡ-≃ (+-identityˡ ε) (+-monoˡ-≤ ε (0≤∣x∣ r)) ⟩
      ∣ r ∣ + ε   ∎

    ∣r∣≤∣r∣+ε : ∣ r ∣ ≤ ∣ r ∣ + ε
    ∣r∣≤∣r∣+ε = begin
      ∣ r ∣      ≈⟨ ≃-symm (+-identityʳ ∣ r ∣) ⟩
      ∣ r ∣ + 0ℝ ≤⟨ +-monoʳ-≤ ∣ r ∣ {0ℝ} {ε} (nonNegx⇒0≤x (pos⇒nonNeg (proj₁ ε-prop))) ⟩
      ∣ r ∣ + ε   ∎

private
  1-r≄0 : ∀ r -> ∣ r ∣ < 1ℝ -> (1ℝ - r) ≄0
  1-r≄0 r ∣r∣<1 = inj₂ (x<y⇒0<y-x r 1ℝ (proj₂ (∣x∣<y⇒-y<x<y r 1ℝ ∣r∣<1)))

{- [6] -}
geometric-sum : ∀ {r} -> ∀ n -> (∣r∣<1 : ∣ r ∣ < 1ℝ) -> ∑ (λ i -> pow r i) 0 n ≃ (1ℝ - pow r n) * ((1ℝ - r) ⁻¹) (1-r≄0 r ∣r∣<1)
geometric-sum {r} zero ∣r∣<1 = let [1-r]⁻¹ = ((1ℝ - r) ⁻¹) (1-r≄0 r ∣r∣<1) in ≃-symm (begin
  (1ℝ - 1ℝ) * [1-r]⁻¹ ≈⟨ *-congʳ {[1-r]⁻¹} {1ℝ - 1ℝ} {0ℝ} (+-inverseʳ 1ℝ) ⟩
  0ℝ * [1-r]⁻¹        ≈⟨ *-zeroˡ [1-r]⁻¹ ⟩
  0ℝ                   ∎)
  where open ≃-Reasoning
geometric-sum {r} (suc n) ∣r∣<1 = let [1-r]⁻¹ = ((1ℝ - r) ⁻¹) (1-r≄0 r ∣r∣<1) in begin
  ∑₀ (pow r) n + pow r n                                  ≈⟨ +-cong {∑₀ (pow r) n} {(1ℝ - pow r n) * [1-r]⁻¹}
                                                             {pow r n} {pow r n * (1ℝ - r) * [1-r]⁻¹}
                                                             (geometric-sum {r} n ∣r∣<1)
                                                             (≃-symm (≃-trans (≃-trans
                                                             (*-assoc (pow r n) (1ℝ - r) [1-r]⁻¹)
                                                             (*-congˡ {pow r n} {(1ℝ - r) * [1-r]⁻¹} {1ℝ} (*-inverseʳ (1ℝ - r) (1-r≄0 r ∣r∣<1))))
                                                             (*-identityʳ (pow r n)))) ⟩
  (1ℝ - pow r n) * [1-r]⁻¹ + pow r n * (1ℝ - r) * [1-r]⁻¹ ≈⟨ ≃-symm (*-distribʳ-+ [1-r]⁻¹ (1ℝ - pow r n) (pow r n * (1ℝ - r))) ⟩
  (1ℝ - pow r n + pow r n * (1ℝ - r)) * [1-r]⁻¹           ≈⟨ *-congʳ {[1-r]⁻¹} {1ℝ - pow r n + pow r n * (1ℝ - r)}
                                                             {1ℝ - pow r n + (pow r n - pow r (suc n))}
                                                             (+-congʳ (1ℝ - pow r n) (≃-trans
                                                             (*-distribˡ-+ (pow r n) 1ℝ (- r))
                                                             (+-cong (*-identityʳ (pow r n)) (≃-symm (neg-distribʳ-* (pow r n) r))))) ⟩
  (1ℝ - pow r n + (pow r n - pow r (suc n))) * [1-r]⁻¹    ≈⟨ *-congʳ {[1-r]⁻¹} {1ℝ - pow r n + (pow r n - pow r (suc n))}
                                                             {1ℝ - pow r (suc n) + (pow r n - pow r n)}
                                                             (solve 4 (λ a b c d -> a :+ b :+ (c :+ d) := a :+ d :+ (c :+ b))
                                                             ≃-refl 1ℝ (- pow r n) (pow r n) (- pow r (suc n))) ⟩
  (1ℝ - pow r (suc n) + (pow r n - pow r n)) * [1-r]⁻¹    ≈⟨ *-congʳ {[1-r]⁻¹} {1ℝ - pow r (suc n) + (pow r n - pow r n)}
                                                             {1ℝ - pow r (suc n)}
                                                             (≃-trans (+-congʳ (1ℝ - pow r (suc n)) (+-inverseʳ (pow r n)))
                                                             (+-identityʳ (1ℝ - pow r (suc n)))) ⟩
  (1ℝ - pow r (suc n)) * [1-r]⁻¹                           ∎
  where
    open ≃-Reasoning
    open ℝ-+-*-Solver

geometric-series-converges : ∀ {r} -> (∣r∣<1 : ∣ r ∣ < 1ℝ) -> SeriesOf (λ i -> pow r i) ConvergesTo ((1ℝ - r) ⁻¹) (1-r≄0 r ∣r∣<1)
geometric-series-converges {r} ∣r∣<1 = xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ {λ n -> (1ℝ - pow r n) * [1-r]⁻¹} {SeriesOf rⁱ}
                             (λ {(suc n-1) -> let n = suc n-1 in ≃-symm (geometric-sum {r} n ∣r∣<1)})
                             ([1-r]⁻¹ , xₙ→x∧x≃y⇒xₙ→y {λ n → (1ℝ - pow r n) * [1-r]⁻¹} {1ℝ * [1-r]⁻¹} {[1-r]⁻¹}
                             (xₙyₙ→x₀y₀ {1-rⁱ} {λ i → [1-r]⁻¹} 1-rⁱ→1 [1-r]⁻¹→[1-r]⁻¹) (*-identityˡ [1-r]⁻¹))
  where
    open ≃-Reasoning
    -1<r<1 = ∣x∣<y⇒-y<x<y r 1ℝ ∣r∣<1
    1-rⁱ = λ i -> 1ℝ - pow r i
    [1-r]⁻¹ = ((1ℝ - r) ⁻¹) (1-r≄0 r ∣r∣<1)
    rⁱ = λ i -> pow r i
    rⁱ→0 = 0ℝ , ∣r∣<1⇒rⁿ→0 ∣r∣<1
    1→1 = 1ℝ , xₙ≃c⇒xₙ→c {λ i -> 1ℝ} {1ℝ} λ {(suc n-1) -> ≃-refl}
    [1-r]⁻¹→[1-r]⁻¹ = [1-r]⁻¹ , xₙ≃c⇒xₙ→c {λ i -> [1-r]⁻¹} {[1-r]⁻¹} λ {(suc n-1) -> ≃-refl}
    1-rⁱ→1 = 1ℝ , xₙ→x∧x≃y⇒xₙ→y (xₙ+yₙ→x₀+y₀ 1→1 (- 0ℝ , -xₙ→-x₀ rⁱ→0)) (≃-trans (+-congʳ 1ℝ (≃-symm 0≃-0)) (+-identityʳ 1ℝ))

abstract
  fast-geometric-series-converges : ∀ {r} -> (∣r∣<1 : ∣ r ∣ < 1ℝ) -> SeriesOf (λ i -> pow r i) ConvergesTo ((1ℝ - r) ⁻¹) (1-r≄0 r ∣r∣<1)
  fast-geometric-series-converges {r} = geometric-series-converges {r}

geometric-series-isConvergent : ∀ {r} -> ∣ r ∣ < 1ℝ -> SeriesOf (λ i -> pow r i) isConvergent
geometric-series-isConvergent {r} ∣r∣<1 = ((1ℝ - r) ⁻¹) (1-r≄0 r ∣r∣<1) , geometric-series-converges {r} ∣r∣<1

abstract
  fast-geometric-series-isConvergent : ∀ {r} -> ∣ r ∣ < 1ℝ -> SeriesOf (λ i -> pow r i) isConvergent
  fast-geometric-series-isConvergent {r} = geometric-series-isConvergent {r}

∑cxₙ≃c∑xₙ : ∀ (xs : ℕ -> ℝ) -> ∀ (c : ℝ) -> ∀ (m n : ℕ) -> ∑ (λ i -> c * xs i) m n ≃ c * ∑ xs m n
∑cxₙ≃c∑xₙ xs c zero n = lem n
  where
    open ≃-Reasoning
    lem : ∀ n -> ∑₀ (λ i -> c * xs i) n ≃ c * ∑₀ xs n
    lem 0 = ≃-symm (*-zeroʳ c)
    lem (suc n) = begin
      ∑₀ (λ i -> c * xs i) n + c * xs n ≈⟨ +-congˡ (c * xs n) (lem n) ⟩
      c * ∑₀ xs n + c * xs n            ≈⟨ ≃-symm (*-distribˡ-+ c (∑₀ xs n) (xs n)) ⟩
      c * (∑₀ xs n + xs n)               ∎
∑cxₙ≃c∑xₙ xs c (suc m) n = begin
  ∑₀ (λ i -> c * xs i) n - (∑₀ (λ i -> c * xs i) m + c * xs m) ≈⟨ +-cong (∑cxₙ≃c∑xₙ xs c 0 n)
                                                                  (-‿cong (≃-trans
                                                                  (+-congˡ (c * xs m) (∑cxₙ≃c∑xₙ xs c 0 m))
                                                                  (≃-symm (*-distribˡ-+ c (∑₀ xs m) (xs m))))) ⟩
  c * ∑₀ xs n - (c * (∑₀ xs m + xs m))                         ≈⟨ ≃-symm (≃-trans
                                                                  (*-distribˡ-+ c (∑₀ xs n) (- (∑₀ xs m + xs m)))
                                                                  (+-congʳ (c * ∑₀ xs n) (≃-symm (neg-distribʳ-* c (∑₀ xs (suc m)))))) ⟩
  c * (∑₀ xs n - (∑₀ xs m + xs m))                              ∎
  where open ≃-Reasoning

{- [7] -}
proposition-3-6-1 : ∀ {xs : ℕ -> ℝ} -> ∀ {c} -> 0ℝ < c < 1ℝ ->
                      (∃ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> ∣ xs (suc n) ∣ ≤ c * ∣ xs n ∣) ->
                      SeriesOf xs isConvergent
proposition-3-6-1 {xs} {c} (0<c , c<1) (N-1 , hyp) = proposition-3-5 {xs} {λ n -> ∣ xs N ∣ * c⁻ᴺ * pow c n} part1
                                                     (ℕ.pred N , λ n n≥N -> part2 n (≤⇒≡∨< N n n≥N))
  where
    open ≤-Reasoning
    N = suc N-1
    posc = 0<x⇒posx {c} 0<c
    cᴺ≄0 = inj₂ (posx⇒0<x {pow c N} (posx⇒posxⁿ {c} N posc))
    c⁻ᴺ = ((pow c N) ⁻¹) cᴺ≄0
    ∣c∣<1 = -y<x<y⇒∣x∣<y c 1ℝ (<-trans (<-respˡ-≃ (⋆-distrib-neg 1ℚᵘ)
            (p<q⇒p⋆<q⋆ (ℚ.- 1ℚᵘ) 0ℚᵘ (ℚP.negative⁻¹ _))) 0<c , c<1)
    con∑cⁿ = fast-geometric-series-isConvergent {c} ∣c∣<1

    part0 : (λ i -> ∣ xs N ∣ * c⁻ᴺ * (SeriesOf (λ n -> pow c n) i)) isConvergent
    part0 = ∣ xs N ∣ * c⁻ᴺ * (proj₁ con∑cⁿ) , xₙyₙ→x₀y₀ {λ i → ∣ xs N ∣ * c⁻ᴺ} {SeriesOf (λ n → pow c n)}
            (∣ xs N ∣ * c⁻ᴺ , xₙ≃c⇒xₙ→c {λ i -> ∣ xs N ∣ * c⁻ᴺ} {∣ xs N ∣ * c⁻ᴺ} (λ {(suc n-1) -> ≃-refl}))
            con∑cⁿ

    part1 : SeriesOf (λ n -> ∣ xs N ∣ * c⁻ᴺ * pow c n) isConvergent
    part1 = ∣ xs N ∣ * c⁻ᴺ * (proj₁ con∑cⁿ) ,
            xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
            {λ i → ∣ xs N ∣ * c⁻ᴺ * SeriesOf (λ n → pow c n) i}
            {SeriesOf (λ n → ∣ xs N ∣ * c⁻ᴺ * pow c n)}
            (λ {n -> ≃-symm (∑cxₙ≃c∑xₙ (λ i -> pow c i) (∣ xs N ∣ * c⁻ᴺ) 0 n)}) part0

    part2 : ∀ n -> N ≡ n ⊎ N ℕ.< n -> ∣ xs n ∣ ≤ ∣ xs N ∣ * c⁻ᴺ * pow c n
    part2 .(suc N-1) (inj₁ refl) = ≤-reflexive (≃-symm (begin-equality
      ∣ xs N ∣ * c⁻ᴺ * pow c N                 ≈⟨ *-assoc ∣ xs N ∣ c⁻ᴺ (pow c N) ⟩
      ∣ xs N ∣ * (c⁻ᴺ * pow c N)               ≈⟨ *-congˡ {∣ xs N ∣} {c⁻ᴺ * pow c N} {1ℝ}
                                                  (*-inverseˡ (pow c N) cᴺ≄0) ⟩
      ∣ xs N ∣ * 1ℝ                            ≈⟨ *-identityʳ ∣ xs N ∣ ⟩
      ∣ xs N ∣                                  ∎))
    part2 (suc n) (inj₂ (ℕ.s≤s N<n)) = begin
      ∣ xs (suc n) ∣                 ≤⟨ hyp n N<n ⟩
      c * ∣ xs n ∣                   ≤⟨ *-monoˡ-≤-nonNeg {∣ xs n ∣} {c} {∣ xs N ∣ * c⁻ᴺ * pow c n}
                                        (part2 n (≤⇒≡∨< N n N<n)) (pos⇒nonNeg posc) ⟩
      c * (∣ xs N ∣ * c⁻ᴺ * pow c n) ≈⟨ *-comm c (∣ xs N ∣ * c⁻ᴺ * pow c n) ⟩
      ∣ xs N ∣ * c⁻ᴺ * pow c n * c   ≈⟨ *-assoc (∣ xs N ∣ * c⁻ᴺ) (pow c n) c ⟩
      ∣ xs N ∣ * c⁻ᴺ * pow c (suc n)  ∎

∣c∣>0⇒∑c-isDivergent : ∀ {c} -> ∣ c ∣ > 0ℝ -> SeriesOf (λ i -> c) isDivergent
∣c∣>0⇒∑c-isDivergent {c} ∣c∣>0 = ∣ c ∣ , div* (0<x⇒posx ∣c∣>0)
                           (λ {k -> suc k , k , ℕP.n≤1+n k , ℕP.≤-refl , ≤-reflexive (∣-∣-cong (≃-symm (begin
  ∑₀ (λ i -> c) k + c - ∑₀ (λ i -> c) k   ≈⟨ solve 3 (λ x y z -> x :+ y :+ z := y :+ (x :+ z))
                                             ≃-refl (∑₀ (λ i -> c) k) c (- ∑₀ (λ i -> c) k) ⟩
  c + (∑₀ (λ i -> c) k - ∑₀ (λ i -> c) k) ≈⟨ +-congʳ c (+-inverseʳ (∑₀ (λ i -> c) k)) ⟩
  c + 0ℝ                                  ≈⟨ +-identityʳ c ⟩
  c                                        ∎)))})
  where
    open ≃-Reasoning
    open ℝ-+-*-Solver

{- [8] -}
proposition-3-6-2 : ∀ {xs : ℕ -> ℝ} -> ∀ {c} -> 1ℝ < c ->
                    (∃ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> ∣ xs (suc n) ∣ > c * ∣ xs n ∣) ->
                    SeriesOf xs isDivergent
proposition-3-6-2 {xs} {c} 1<c (N-1 , hyp) = subsequence-divergence-test {xs} (∣ xs (suc N) ∣ ,
                                             (λ n -> xs (n ℕ.+ suc N)) , 0<x⇒posx {∣ xs (suc N) ∣} part1 ,
                                             subseq* ((λ n -> n ℕ.+ suc N) , (λ n -> ≃-refl) , (λ n -> ℕP.n<1+n (n ℕ.+ suc N))) ,
                                             λ n -> ≤-trans {∣ xs (suc N) ∣} {pow c (n ℕ.+ suc N) * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣} {∣ xs (n ℕ.+ suc N) ∣}
                                                    (part2-1 (n ℕ.+ suc N) (ℕP.m≤n+m (suc N) n))
                                                    (part2-2 (n ℕ.+ suc N) (≤⇒≡∨< (suc N) (n ℕ.+ suc N) (ℕP.m≤n+m (suc N) n))))
  where
    open ≤-Reasoning
    N = suc N-1
    n-N-1 = λ n -> ℤ.∣ + n ℤ.- + (suc N) ∣
    cᴺ⁺¹≄0 = inj₂ (posx⇒0<x {pow c (suc N)} (posx⇒posxⁿ {c} (suc N) (0<x⇒posx {c}
             (<-trans (p<q⇒p⋆<q⋆ 0ℚᵘ 1ℚᵘ (ℚP.positive⁻¹ _)) 1<c))))
    c⁻ᴺ⁻¹ = ((pow c (suc N)) ⁻¹) cᴺ⁺¹≄0
    posc = 0<x⇒posx (≤-<-trans (p≤q⇒p⋆≤q⋆ 0ℚᵘ 1ℚᵘ (ℚP.nonNegative⁻¹ _)) 1<c)

    part1 : ∣ xs (suc N) ∣ > 0ℝ
    part1 = begin-strict
      0ℝ                 ≤⟨ nonNegx⇒0≤x (nonNegx,y⇒nonNegx*y (pos⇒nonNeg posc) (nonNeg∣x∣ (xs N))) ⟩
      c * ∣ xs N ∣       <⟨ hyp N ℕP.≤-refl ⟩
      ∣ xs (suc N) ∣      ∎

    part2-1 : ∀ n -> suc N ℕ.≤ n -> pow c n * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣ ≥ ∣ xs (suc N) ∣
    part2-1 n N+1≤n = begin
      ∣ xs (suc N) ∣                         ≈⟨ ≃-symm (*-identityˡ ∣ xs (suc N) ∣) ⟩
      1ℝ * ∣ xs (suc N) ∣                    ≈⟨ ≃-symm (*-congʳ {∣ xs (suc N) ∣} {pow c (suc N) * c⁻ᴺ⁻¹} {1ℝ}
                                                (*-inverseʳ (pow c (suc N)) cᴺ⁺¹≄0)) ⟩
      pow c (suc N) * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣ ≤⟨ *-monoʳ-≤-nonNeg {pow c (suc N) * c⁻ᴺ⁻¹} {∣ xs (suc N) ∣} {pow c n * c⁻ᴺ⁻¹}
                                                (*-monoʳ-≤-nonNeg {pow c (suc N)} {c⁻ᴺ⁻¹} {pow c n}
                                                (1≤x∧m≤n⇒xᵐ≤xⁿ {c} (<⇒≤ 1<c) N+1≤n)
                                                (nonNegx⇒nonNegx⁻¹ {pow c (suc N)} (nonNegx⇒nonNegxⁿ {c} (suc N)
                                                (pos⇒nonNeg {c} posc)) cᴺ⁺¹≄0))
                                                (nonNeg∣x∣ (xs (suc N))) ⟩
      pow c n * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣        ∎

    part2-2 : ∀ n -> suc N ≡ n ⊎ suc N ℕ.< n -> ∣ xs n ∣ ≥ pow c n * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣
    part2-2 .(suc (suc N-1)) (inj₁ refl) = begin
      pow c (suc N) * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣ ≈⟨ *-congʳ {∣ xs (suc N) ∣} {pow c (suc N) * c⁻ᴺ⁻¹} {1ℝ}
                                                (*-inverseʳ (pow c (suc N)) cᴺ⁺¹≄0) ⟩
      1ℝ * ∣ xs (suc N) ∣                    ≈⟨ *-identityˡ ∣ xs (suc N) ∣ ⟩
      ∣ xs (suc N) ∣                          ∎
    part2-2 (suc n) (inj₂ (ℕ.s≤s N<n)) = begin
      pow c n * c * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣   ≈⟨ *-congʳ {∣ xs (suc N) ∣} {pow c n * c * c⁻ᴺ⁻¹} {c * pow c n * c⁻ᴺ⁻¹}
                                                (*-congʳ {c⁻ᴺ⁻¹} {pow c n * c} {c * pow c n} (*-comm (pow c n) c)) ⟩
      c * pow c n * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣   ≈⟨ *-congʳ {∣ xs (suc N) ∣} {c * pow c n * c⁻ᴺ⁻¹} {c * (pow c n * c⁻ᴺ⁻¹)}
                                                (*-assoc c (pow c n) c⁻ᴺ⁻¹) ⟩
      c * (pow c n * c⁻ᴺ⁻¹) * ∣ xs (suc N) ∣ ≈⟨ *-assoc c (pow c n * c⁻ᴺ⁻¹) ∣ xs (suc N) ∣ ⟩
      c * (pow c n * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣) ≤⟨ *-monoˡ-≤-nonNeg {pow c n * c⁻ᴺ⁻¹ * ∣ xs (suc N) ∣} {c} {∣ xs n ∣}
                                                (part2-2 n (≤⇒≡∨< (suc N) n N<n))
                                                (pos⇒nonNeg {c} posc) ⟩
      c * ∣ xs n ∣                           <⟨ hyp n (ℕP.≤-trans (ℕP.n≤1+n N) N<n) ⟩
      ∣ xs (suc n) ∣                          ∎

ε-cauchy-convergence : ∀ {xs : ℕ -> ℝ} -> (∀ {ε} -> ε > 0ℝ -> ∃ λ N-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc N-1 -> ∣ xs m - xs n ∣ < ε) -> xs isConvergent
ε-cauchy-convergence {xs} hyp = cauchy-convergence ((λ {(suc k-1) ->
                                let k = suc k-1; res = hyp (p<q⇒p⋆<q⋆ 0ℚᵘ (+ 1 / k) (ℚP.positive⁻¹ _)) in
                                proj₁ res , λ m n m>n m≥N n≥N -> <⇒≤ (proj₂ res m n m>n n≥N)}))

ε-cauchy : ∀ {xs : ℕ -> ℝ} -> (∀ {ε} -> ε > 0ℝ -> ∃ λ N-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc N-1 -> ∣ xs m - xs n ∣ < ε) -> xs isCauchy
ε-cauchy {xs} hyp = convergent⇒cauchy (ε-cauchy-convergence hyp)

ε-from-convergence-cauchy : ∀ {xs : ℕ -> ℝ} -> (xₙ→ℓ : xs isConvergent) ->
                            ∀ {ε : ℝ} -> ε > 0ℝ -> ∃ λ N-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc N-1 -> ∣ xs m - xs n ∣ < ε
ε-from-convergence-cauchy {xs} xₙ→ℓ {ε} ε>0 = {!!}

abstract
  fast-ε-from-convergence-cauchy : ∀ {xs : ℕ -> ℝ} -> (xₙ→ℓ : xs isConvergent) ->
                                   ∀ {ε : ℝ} -> ε > 0ℝ -> ∃ λ N-1 -> ∀ m n -> m ℕ.> n -> n ℕ.≥ suc N-1 -> ∣ xs m - xs n ∣ < ε
  fast-ε-from-convergence-cauchy = ε-from-convergence-cauchy

{-
Lemma:
  Let (aₙ) and (xₙ) be positive sequences of real numbers and let c>0. If (aₙxₙ)→0 and there is N₁∈ℕ such that
(1)                                 aₙxₙxₙ₊₁⁻¹ - aₙ₊₁ ≥ c         (n ≥ N₁)
then ∑xₙ converges.
Proof:
  Let ε>0. Since (aₙxₙ)→0, there is N₂∈ℕ such that
(2)                                     ∣aₘxₘ - aₙxₙ∣ < cε        (m ≥ n ≥ N₂).
Moreover, by (1) we have
(3)                                   aₙxₙ - aₙ₊₁xₙ₊₁ ≥ cxₙ₊₁     (n ≥ N₁).
Let N = max{N₁, N₂} and let m ≥ n ≥ N. Then
      ∣∑ᵢ₌₀ᵐ xᵢ - ∑ᵢ₌₀ⁿ xᵢ∣ = ∑ᵢ₌ₙᵐ xᵢ
                            = c⁻¹∑ᵢ₌ₙᵐ cxᵢ
                            < c⁻¹∑ᵢ₌ₙᵐ (aᵢ₋₁xᵢ₋₁ - aᵢxᵢ)          by (3)
                            = c⁻¹(aₘ₋₁xₘ₋₁ - aₙxₙ)                
                            ≤ c⁻¹cε                               by (2)
                            = ε.
Thus ∑xₙ is a Cauchy sequence.                                                                             □
-}
lemma-3-7-1 : ∀ {as xs : ℕ -> ℝ} -> ∀ {c : ℝ} -> 0ℝ < c ->
              (0<aₙ,xₙ : ∀ n -> (0ℝ < as n) × (0ℝ < xs n)) ->
              (λ n -> as n * xs n) ConvergesTo 0ℝ ->
              (∃ λ N-1 -> ∀ n -> n ℕ.≥ suc N-1 -> as n * xs n * (xs (suc n) ⁻¹) (inj₂ (proj₂ (0<aₙ,xₙ (suc n)))) - as (suc n) ≥ c) ->
              SeriesOf xs isConvergent
lemma-3-7-1 {as} {xs} {c} 0<c 0<aₙ,xₙ aₙxₙ→0 (N₁-1 , hyp) = ε-cauchy-convergence (λ {ε} ε>0 ->
                                                        let res = fast-ε-from-convergence-cauchy (0ℝ , aₙxₙ→0)
                                                                  (posx⇒0<x (posx,y⇒posx*y (0<x⇒posx 0<c) (0<x⇒posx ε>0)))
                                                                ; N₁ = suc N₁-1; N₂ = suc (proj₁ res); N = N₁ ℕ.⊔ N₂ in
                                                        ℕ.pred N , λ {(suc m-1) (suc n-1) m>n n≥N →
                                                        let m = suc m-1; n = suc n-1
                                                              ; c≄0 = inj₂ 0<c; c⁻¹ = (c ⁻¹) c≄0
                                                              ; posc⁻¹ = posx⇒posx⁻¹ {c} c≄0 (0<x⇒posx 0<c) in begin-strict
  ∣ ∑ xs n m ∣                  ≈⟨ 0≤x⇒∣x∣≃x (0≤xₙ⇒0≤∑xₙ (ℕP.<⇒≤ m>n) (λ k n≤k≤m -> <⇒≤ (proj₂ (0<aₙ,xₙ k)))) ⟩
  ∑ xs n m                      ≈⟨ ≃-symm (≃-trans (*-congʳ {∑ xs n m} (*-inverseˡ c c≄0)) (*-identityˡ (∑ xs n m))) ⟩
  c⁻¹ * c * ∑ xs n m            ≈⟨ ≃-trans
                                   (*-assoc c⁻¹ c (∑ xs n m))
                                   (*-congˡ {c⁻¹} {c * ∑ xs n m} {∑ (λ i → c * xs i) n m}
                                   (≃-symm (∑cxₙ≃c∑xₙ xs c n m))) ⟩
  c⁻¹ * ∑ (λ i -> c * xs i) n m <⟨ *-monoʳ-<-pos {c⁻¹} posc⁻¹ {∑ (λ i → c * xs i) n m}
                                   {∑ (λ i → as (ℕ.pred i) * xs (ℕ.pred i) - as i * xs i) n m}
                                   {!!} ⟩
  c⁻¹ * ∑ (λ i -> as (ℕ.pred i) * xs (ℕ.pred i) - as i * xs i) n m              ≈⟨ {!!} ⟩
  c⁻¹ * (as m-1 * xs m-1 - as n * xs n)                    ≤⟨ *-monoˡ-≤-nonNeg {as m-1 * xs m-1 - as n * xs n} {c⁻¹} {c * ε}
                                                              {!!}
                                                              (pos⇒nonNeg {c⁻¹} posc⁻¹) ⟩
  c⁻¹ * (c * ε)                 ≈⟨ ≃-trans (≃-trans (≃-symm (*-assoc c⁻¹ c ε)) (*-congʳ {ε} {c⁻¹ * c} {1ℝ} (*-inverseˡ c c≄0))) (*-identityˡ ε) ⟩
  ε                              ∎})
  where
    open ≤-Reasoning
    part1 : ∀ n -> n ℕ.≥ suc N₁-1 -> as n * xs n - as (suc n) * xs (suc n) ≥ c * xs (suc n)
    part1 n n≥N₁ = let n+1 = suc n; xₙ₊₁≄0 = inj₂ (proj₂ (0<aₙ,xₙ n+1)) in begin
      c * xs n+1                                                          ≤⟨ *-monoʳ-≤-nonNeg {c} {xs n+1}
                                                                             {as n * xs n * (xs n+1 ⁻¹) xₙ₊₁≄0 - as n+1}
                                                                             (hyp n n≥N₁)
                                                                             (pos⇒nonNeg (0<x⇒posx (proj₂ (0<aₙ,xₙ n+1)))) ⟩
      (as n * xs n * ((xs n+1) ⁻¹) xₙ₊₁≄0 - as n+1) * xs n+1              ≈⟨ *-distribʳ-+ (xs n+1) (as n * xs n * ((xs n+1) ⁻¹) xₙ₊₁≄0) (- (as n+1)) ⟩
      as n * xs n * ((xs n+1) ⁻¹) xₙ₊₁≄0 * xs n+1 + (- (as n+1)) * xs n+1 ≈⟨ +-cong
                                                                             (≃-trans (≃-trans
                                                                             (*-assoc (as n * xs n) (((xs n+1) ⁻¹) xₙ₊₁≄0) (xs n+1))
                                                                             (*-congˡ (*-inverseˡ (xs n+1) xₙ₊₁≄0)))
                                                                             (*-identityʳ (as n * xs n)))
                                                                             (≃-symm (neg-distribˡ-* (as n+1) (xs n+1))) ⟩
      as n * xs n - as n+1 * xs n+1                                        ∎

    lem : ∀ m n -> {n ≢0} -> (m≥n : m ℕ.≥ n) ->
          ∑ᵀ (λ i -> as (ℕ.pred i) * xs (ℕ.pred i) - as i * xs i) n m m≥n ≃ as (ℕ.pred n) * xs (ℕ.pred n) - as (ℕ.pred m) * xs (ℕ.pred m)  
    lem (suc zero) (suc zero) (ℕ.s≤s ℕ.z≤n) = ≃-symm (+-inverseʳ (as 0 * xs 0))
    lem (suc zero) (suc (suc n)) (ℕ.s≤s ())
    lem (suc (suc m)) (suc zero) m≥n = {!!}
    lem (suc (suc m)) (suc (suc n)) m≥n = {!!}

{-
Need to figure out most efficient way to perform this limit shift.
Hard to do it with natural numbers. 

Ideas:
·Implement subtraction function for ℕ (there is currently no such function on ℕ)
 Then make lemmas for:
   · ∑ᵢ₌ₙᵐ xᵢ₊ₖ = ∑ᵢ₌ₙ₊ₖᵐ⁺ᵏ xᵢ
   · ∑ᵢ₌ₙᵐ xᵢ₋ₖ = ∑ᵢ₌ₙ₋ₖᵐ⁻ᵏ xᵢ. Might need k ≤ n, m.
·Make ∑ᵀ function that takes integer limits instead (this would probably be harder to transfer to ∑ though).
-}
    part2 : ∀ m n -> {n ≢0} -> m ℕ.> n ->
            ∑ (λ i -> as (ℕ.pred i) * xs (ℕ.pred i) - as i * xs i) n m ≃ as (ℕ.pred m) * xs (ℕ.pred m) - as n * xs n
    part2 (suc zero) (suc zero) (ℕ.s≤s ())
    part2 (suc (suc m-1)) (suc zero) m>n = {!limitShifting!}
    part2 (suc zero) (suc (suc n-1)) (ℕ.s≤s ())
    part2 (suc (suc m-1)) (suc (suc n-1)) m>n = {!!}

_·_ : ℕ -> ℝ -> ℝ
n · x = {!!}

{-
It's interesting that this typechecks with the (≃-reflexive (λ n -> ℚP.≃-refl)) proof, but
not with the ≃-refl proof.

The reason seems to be this: Each real number is represented as a sequence (xₙ) of rationals
with a proof of its regularity. By calling ≃-refl to prove x ≃ y, we are also declaring that
the regularity proofs of (xₙ) and (yₙ) are equivalent.

We can't prove 0ℝ ≃ - 0ℝ by ≃-refl because of the regularity proof. We can, however, prove it
simply by proving that their corresponding rational sequences are equal. This is exactly what
is occurring here with ≃-reflexive. It checks only the rational sequences of the normal forms.

This enables us to prove things about negatives and about the basic algebraic properties of 
multiplication using the solver, as shown in test and test3. We cannot, however, use it to
prove that x - x ≃ 0ℝ.
-}
test : ∀ x y -> x + y ≃ - (- x - y)
test x y = solve 2 (λ x y -> x :+ y := :- (:- x :- y)) (≃-reflexive (λ n -> ℚP.≃-refl)) x y
  where open ℝ-+-*-Solver

test2 : ∀ x -> x - x ≃ 0ℝ
test2 x = solve 1 (λ x -> x :- x := (0 :× x)) {!!} {!!}
  where open ℝ-+-*-Solver

{-
This test is very slow! It takes a long time to check that the sequences of each normal form
are actually equivalent. Hence the test is commented out until it's needed.
-}
{-
test3 : ∀ x y -> x * y ≃ y * x
test3 x y = solve 2 (λ x y -> x :* y := y :* x) (≃-reflexive (λ {n -> ℚP.≃-refl})) x y
  where open ℝ-+-*-Solver
-}

≃-reflexive-≡ : ∀ {x y} -> (∀ n -> {n ≢0} -> seq x n ≡ seq y n) -> x ≃ y
≃-reflexive-≡ {x} {y} hyp = {!!}

{-
After 15 minutes, test4 would still not typecheck, despite its apparent simplicity. 

This, along with the long time it takes to typecheck test3, indicates that a real number solver that
is functional with multiplication might not be feasible due to the reals being so computationally intensive.
-}
{-
test4 : ∀ x y z -> x * y * z ≃ x * (y * z)
test4 x y z = solve 3 (λ x y z -> x :* y :* z := x :* (y :* z)) (≃-reflexive (λ n -> ℚP.≃-refl)) {!!} {!!} {!!}
  where open ℝ-+-*-Solver
-}

{-
test4-modified : ∀ x y z -> x * y * z ≃ x * (y * z)
test4-modified x y z = solve 3 (λ x y z -> x :* y :* z := x :* (y :* z)) (≃-reflexive-≡ (λ n -> {!refl!})) x y z
  where open ℝ-+-*-Solver
-}
-}
