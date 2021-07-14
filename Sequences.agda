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

archimedean-ℝ₂ : ∀ {x} -> Positive x -> ∃ λ n-1 -> (+ 1 / (suc n-1)) ⋆ < x
archimedean-ℝ₂ {x} posx = {!!}

{-
Proposition:
  If x and y are nonzero, then so is x * y.
Proof:
  Let x,y∈ℝ such that x ≠ 0 and y ≠ 0. We must show that x * y ≠ 0. We have x < 0 ∨ 0 < x and
y < 0 ∨ 0 < y. 
Case 1: Suppose x > 0 and y > 0. Then x * y > 0.
Case 2: Suppose x > 0 and y < 0. Then x * y < 0.
Case 3: Suppose x < 0 and y < 0. Then -x > 0 and -y > 0, so x * y = -x * -y > 0. 
Case 4: Similar to case 2.                                                                   □
-}

negx,y⇒posx*y : ∀ {x y} -> Negative x -> Negative y -> Positive (x * y)
negx,y⇒posx*y {x} {y} negx negy = {!!}

negx∧posy⇒negx*y : ∀ {x y} -> Negative x -> Positive y -> Negative (x * y)
negx∧posy⇒negx*y {x} {y} negx posy = {!!}

x≄0∧y≄0⇒x*y≄0 : ∀ {x y} -> x ≄0 -> y ≄0 -> (x * y) ≄0
x≄0∧y≄0⇒x*y≄0 {x} {y} x≄0 y≄0 = [ [ y<0∧x<0 , {!!} ]′ y≄0 , [ {!!} , 0<y∧0<x ]′ y≄0 ]′ x≄0
  where
    0<y∧0<x : 0ℝ < y -> 0ℝ < x -> (x * y) ≄0
    0<y∧0<x 0<y 0<x = inj₂ (posx⇒0<x (posx,y⇒posx*y (0<x⇒posx 0<x) (0<x⇒posx 0<y)))

    y<0∧x<0 : y < 0ℝ -> x < 0ℝ -> (x * y) ≄0
    y<0∧x<0 y<0 x<0 = inj₂ (posx⇒0<x (negx,y⇒posx*y {!!} {!!}))

{-
Proposition:
  If xₙ ≠ 0 for all n∈ℕ, x₀ ≠ 0, and (xₙ)→x₀, then (xₙ⁻¹)→x₀⁻¹.
Proof:
  We must show that, for all k∈ℕ, there is Nₖ∈ℕ such that
                         ∣xₙ⁻¹ - x₀⁻¹∣ ≤ k⁻¹.
By the Archimedean Property, there is r∈ℕ such that r⁻¹ < 2⁻¹∣x₀∣ since ∣x₀∣ > 0.
Then for some n₀∈ℕ, we have
                         ∣xₙ - x₀∣ ≤ r⁻¹ < 2⁻¹∣x₀∣            (n ≥ n₀).
Let k∈ℕ. Then there is m₀∈ℕ such that 
                   ∣xₙ - x₀∣ ≤ k⁻¹ < (2k)⁻¹∣x₀∣²              (n ≥ m₀).
Let Nₖ = max{m₀, n₀} and let n ≥ N. We have:
        ∣xₙ⁻¹ - x₀⁻¹∣ = ∣xₙ∣⁻¹ * ∣x₀∣⁻¹ * ∣xₙ - x₀∣
                      < 2∣x₀∣⁻¹ * ∣x₀∣⁻¹ * ∣xₙ - x₀∣ since n ≥ n₀
                      ≤ 2∣x₀∣⁻¹ * ∣x₀∣⁻¹ * (2k)⁻¹∣x₀∣²
                      = k⁻¹.
Hence ∣xₙ⁻¹ - x₀⁻¹∣ ≤ k⁻¹ for all n ≥ N.                                       □
-}
xₙ≄0∧x₀≄0⇒xₙ⁻¹→x₀⁻¹ : ∀ {xs : ℕ -> ℝ} -> ∀ {x₀ : ℝ} -> xs ConvergesTo x₀ -> (xₙ≄0 : ∀ n -> xs n ≄0) -> (x₀≄0 : x₀ ≄0) ->
                      (λ n -> (xs n ⁻¹) (xₙ≄0 n)) ConvergesTo (x₀ ⁻¹) x₀≄0
xₙ≄0∧x₀≄0⇒xₙ⁻¹→x₀⁻¹ {xs} {x₀} (con* xₙ→x₀) xₙ≄0 x₀≄0 = con* main
  where
    open ≤-Reasoning
    main : ∀ k -> {k≢0 : k ≢0} -> ∃ λ Nₖ-1 -> ∀ n -> n ℕ.≥ suc Nₖ-1 ->
           ∣ (xs n ⁻¹) (xₙ≄0 n) - (x₀ ⁻¹) x₀≄0 ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
    main (suc k-1) = ℕ.pred Nₖ , sub
      where
        k = suc k-1
        Nₖ = suc (proj₁ (xₙ→x₀ k))
        arch = archimedean-ℝ₂ {!!}
        sub : ∀ n -> n ℕ.≥ Nₖ ->
              ∣ (xs n ⁻¹) (xₙ≄0 n) - (x₀ ⁻¹) x₀≄0 ∣ ≤ (+ 1 / k) ⋆
        sub (suc n-1) n≥Nₖ = {!!}
          where
            n = suc n-1
            xₙ = xs n
            xₙ⁻¹ = (xₙ ⁻¹) (xₙ≄0 n)
            x₀⁻¹ = (x₀ ⁻¹) x₀≄0
            ∣xₙ∣⁻¹ = {!!}
            ∣x₀∣⁻¹ = {!!}

            2⁻¹∣x₀∣<∣xₙ∣ : (+ 1 / 2) ⋆ * ∣ x₀ ∣ < ∣ xₙ ∣
            2⁻¹∣x₀∣<∣xₙ∣ = begin-strict {!!}
              

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

limitShifting : ∀ xs -> ∀ k m n -> m ℕ.< n -> ∑ xs m k ≃ ∑ xs n k + ∑ xs m n
limitShifting xs k zero (suc n) m<n = ≃-symm (begin
  ∑₀ xs k - (∑₀ xs n + xs n) + (∑₀ xs n + xs n)     ≈⟨ +-assoc (∑₀ xs k) (- (∑₀ xs n + xs n)) (∑₀ xs n + xs n) ⟩
  ∑₀ xs k + (- (∑₀ xs n + xs n) + (∑₀ xs n + xs n)) ≈⟨ +-congʳ (∑₀ xs k) (+-inverseˡ (∑₀ xs n + xs n)) ⟩
  ∑₀ xs k + 0ℝ                                      ≈⟨ +-identityʳ (∑₀ xs k) ⟩
  ∑₀ xs k                                            ∎)
  where open ≃-Reasoning
limitShifting xs k (suc m) (suc n) m<n = begin
  ∑₀ xs k - (∑₀ xs m + xs m)                                       ≈⟨ ≃-symm (≃-trans
                                                                      (+-congˡ (- (∑₀ xs m + xs m)) (+-congʳ (∑₀ xs k) (+-inverseʳ (∑₀ xs n + xs n))))
                                                                      (+-congˡ (- (∑₀ xs m + xs m)) (+-identityʳ (∑₀ xs k)))) ⟩
  ∑₀ xs k + (∑₀ xs n + xs n - (∑₀ xs n + xs n)) - (∑₀ xs m + xs m) ≈⟨ solve 4 (λ a b c d -> a :+ (b :+ c) :+ d := a :+ c :+ (b :+ d))
                                                                      ≃-refl (∑₀ xs k) (∑₀ xs n + xs n) (- (∑₀ xs n + xs n)) (- (∑₀ xs m + xs m)) ⟩
  ∑₀ xs k - (∑₀ xs n + xs n) + (∑₀ xs n + xs n - (∑₀ xs m + xs m))  ∎
  where
    open ≃-Reasoning
    open ℝ-+-*-Solver

{-
∑ₘᵗxₖ
m<n :
∑ₘᵗxₖ =  ∑ₙᵗxₖ + ∑ₘⁿ xₖ

m>n:
∑ₙᵗxₖ = ∑ₘᵗxₖ + ∑ₙᵐxₖ
∑ₘᵗxₖ = ∑ₘᵗxₖ + ∑ₙᵗxₖ - ∑ₙᵗxₖ
      = ∑ₘᵗxₖ + ∑ₙᵗxₖ - (∑ₘᵗxₖ + ∑ₙᵐxₖ)
      = ∑ₙᵗxₖ - ∑ₙᵐxₖ
-}
lowerLimitShiftPreservesConvergence : ∀ xs -> ∀ n -> (SeriesOf xs From n) isConvergent ->
                                 ∀ m -> (SeriesOf xs From m) isConvergent
lowerLimitShiftPreservesConvergence xs n (ℓ , con* hyp) m with ℕP.<-cmp m n
... | tri< m<n ¬m≡n ¬m>n = ℓ + ∑ xs m n , xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc k-1) -> ≃-symm (limitShifting xs (suc k-1) m n m<n)})
                           (ℓ + ∑ xs m n , xₙ+yₙ→x₀+y₀ {SeriesOf xs From n} {λ k -> ∑ xs m n} (ℓ , con* hyp) (∑ xs m n , xₙ≃c⇒xₙ→c (λ {(suc k-1) -> ≃-refl})))
... | tri≈ ¬m<n refl ¬m>n = ℓ , con* hyp
... | tri> ¬m<n ¬m≡n m>n = ℓ - ∑ xs n m , xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc k-1) -> let k = suc k-1 in begin
  ∑ xs n k - ∑ xs n m            ≈⟨ +-congˡ (- ∑ xs n m) (limitShifting xs k n m m>n) ⟩
  ∑ xs m k + ∑ xs n m - ∑ xs n m ≈⟨ ≃-trans
                                    (+-assoc (∑ xs m k) (∑ xs n m) (- ∑ xs n m))
                                    (≃-trans (+-congʳ (∑ xs m k) (+-inverseʳ (∑ xs n m)))
                                    (+-identityʳ (∑ xs m k))) ⟩
  ∑ xs m k                        ∎})
                           (ℓ - ∑ xs n m , xₙ+yₙ→x₀+y₀ {SeriesOf xs From n} {λ k -> - ∑ xs n m}
                           (ℓ , con* hyp) (- ∑ xs n m , xₙ≃c⇒xₙ→c (λ {(suc k-1) -> ≃-refl})))
  where open ≃-Reasoning

--∀ε>0 ∃N∈ℕ ∀n>m≥N (∣xₘ₊₁ + ⋯ + ∣ ≤ ε)
cauchyConvergenceTest-if : ∀ xs -> SeriesOf xs isConvergent ->
                           ∀ k -> {k≢0 : k ≢0} -> ∃ λ Nₖ-1 -> ∀ m n -> m ℕ.≥ suc Nₖ-1 -> n ℕ.≥ suc Nₖ-1 -> n ℕ.> m ->
                           ∣ ∑ xs m n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆
cauchyConvergenceTest-if xs hyp (suc k-1) = {!!}

cauchyConvergenceTest-onlyif : ∀ xs ->
                               (∀ k -> {k≢0 : k ≢0} -> ∃ λ Nₖ-1 -> ∀ m n -> m ℕ.≥ suc Nₖ-1 -> n ℕ.≥ suc Nₖ-1 -> n ℕ.> m ->
                                       ∣ ∑ xs m n ∣ ≤ ((+ 1 / k) {k≢0}) ⋆) ->
                               SeriesOf xs isConvergent
cauchyConvergenceTest-onlyif xs hyp = {!!}
{-
Suppose ∑xₙ→ℓ for some ℓ∈ℝ. Let k∈ℕ. Then there is Nₖ∈ℕ s.t. m ≥ Nₖ implies ∣∑ᵐxₙ - ℓ∣ ≤ (2k)⁻¹. 
Let m > Nₖ. Then:
  ∣xₘ∣ = ∣∑ᵐxₙ - ∑ᵐ⁻¹xₙ - ℓ + ℓ∣
       = ∣∑ᵐxₙ - ℓ∣ + ∣∑ᵐ̂⁻¹xₙ - ℓ∣
       ≤ (2k)⁻¹ + (2k)⁻¹
       = k⁻¹,
so ∣xₘ∣ ≤ k⁻¹. Hence (xₙ) → 0.                                                                □
-}
∑xₙisConvergent⇒xₙ→0 : ∀ xs -> SeriesOf xs isConvergent -> xs ConvergesTo 0ℝ
∑xₙisConvergent⇒xₙ→0 xs (ℓ , con* ∑xₙ→ℓ) = {!!}
