{-
This is a heavily refactored version of the old Reals file.
Some code is cleaner (e.g. using let instead of where clauses for renaming variables), and some definitions have been altered for convenience 
(but are still equivalent to the old definitions).

Most importantly, many of the relations, like equality ≃ on ℝ, are now defined using constructors (thanks to Dr. Peter Selinger for suggesting this). 
Thus Agda can pattern match on (most) implicit real number arguments now. For instance, to prove 0ℝ ≃ 0ℝ, it is no longer necessary to type "≃-refl {0ℝ}"; 
just "≃-refl" works now.

As a result, the ring solver from the standard library is now functional on ℝ. It's very weak, though, since equality on ℝ is not decidable. 
-}

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

open ℚᵘ

record ℝ : Set where
  constructor mkℝ
  field
    -- No n≢0 condition for seq
    seq : ℕ -> ℚᵘ
    reg : ∀ (m n : ℕ) -> {m≢0 : m ≢0} -> {n≢0 : n ≢0} ->
          ℚ.∣ seq m ℚ.- seq n ∣ ℚ.≤ ((+ 1) / m) {m≢0} ℚ.+ ((+ 1) / n) {n≢0}

open ℝ

infix 4 _≃_

data _≃_ : Rel ℝ 0ℓ where
  *≃* : ∀ {x y : ℝ} -> (∀ (n : ℕ) -> {n≢0 : n ≢0} -> ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0}) -> x ≃ y

-- Properties of _≃_
≃-refl : Reflexive _≃_
≃-refl {x} = *≃* λ { (suc k₁) → let n = suc k₁ in begin
  ℚ.∣ seq x n ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n)) ⟩
  0ℚᵘ                       ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                    ∎}
  where open ℚP.≤-Reasoning

∣p-q∣≃∣q-p∣ : ∀ p q -> ℚ.∣ p ℚ.- q ∣ ℚ.≃ ℚ.∣ q ℚ.- p ∣
∣p-q∣≃∣q-p∣ p q = begin-equality
  ℚ.∣ p ℚ.- q ∣       ≈⟨ ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (p ℚ.- q)) ⟩
  ℚ.∣ ℚ.- (p ℚ.- q) ∣ ≈⟨ ℚP.∣-∣-cong (solve 2 (λ p q -> :- (p :- q) := q :- p) ℚP.≃-refl p q) ⟩
  ℚ.∣ q ℚ.- p ∣        ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver

≃-symm : Symmetric _≃_
≃-symm {x} {y} (*≃* x₁) = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ seq y n ℚ.- seq x n ∣ ≈⟨ ∣p-q∣≃∣q-p∣ (seq y n) (seq x n) ⟩
  ℚ.∣ seq x n ℚ.- seq y n ∣ ≤⟨ x₁ n ⟩
  + 2 / n                    ∎})
  where open ℚP.≤-Reasoning

m≤∣m∣ : ∀ m -> m ℤ.≤ + ℤ.∣ m ∣
m≤∣m∣ (+_ n) = ℤP.≤-refl
m≤∣m∣ (-[1+_] n) = ℤ.-≤+

archimedean-ℚ : ∀ p r -> ℚ.Positive p -> ∃ λ (N : ℕ) -> r ℚ.< ((+ N) ℤ.* ↥ p) / (↧ₙ p)
archimedean-ℚ (mkℚᵘ +[1+ g ] q-1) (mkℚᵘ u v-1) posp = let p = suc g; q = suc q-1; v = suc v-1; r = (u ℤ.* + q) modℕ (p ℕ.* v); t = (u ℤ.* + q) divℕ (p ℕ.* v) in suc ℤ.∣ t ∣ , ℚ.*<* (begin-strict
  u ℤ.* + q ≡⟨ a≡a%ℕn+[a/ℕn]*n (u ℤ.* + q) (p ℕ.* v) ⟩
  + r ℤ.+ t ℤ.* (+ p ℤ.* + v) <⟨ ℤP.+-monoˡ-< (t ℤ.* (+ p ℤ.* + v)) (ℤ.+<+ (n%d<d (u ℤ.* + q) (+ p ℤ.* + v))) ⟩
  + p ℤ.* + v ℤ.+ t ℤ.* (+ p ℤ.* + v) ≡⟨ solve 2 (λ pv t ->
                                         pv :+ (t :* pv) := (con (+ 1) :+ t) :* pv)
                                         _≡_.refl (+ p ℤ.* + v) t ⟩
  (+ 1 ℤ.+ t) ℤ.* (+ p ℤ.* + v)       ≤⟨ ℤP.*-monoʳ-≤-nonNeg (p ℕ.* v) (m≤∣m∣ (+ 1 ℤ.+ t)) ⟩
  + ℤ.∣ + 1 ℤ.+ t ∣ ℤ.* (+ p ℤ.* + v)   ≤⟨ ℤP.*-monoʳ-≤-nonNeg (p ℕ.* v) (ℤ.+≤+ (ℤP.∣m+n∣≤∣m∣+∣n∣ (+ 1) t)) ⟩
  + suc ℤ.∣ t ∣ ℤ.* (+ p ℤ.* + v)     ≡⟨ sym (ℤP.*-assoc (+ suc ℤ.∣ t ∣) (+ p) (+ v)) ⟩
  (+ suc ℤ.∣ t ∣ ℤ.* + p) ℤ.* + v ∎)
  where
    open ℤP.≤-Reasoning
    open ℤ-Solver.+-*-Solver

q≤r⇒+p/r≤+p/q : ∀ p q r -> {q≢0 : q ≢0} -> {r≢0 : r ≢0} -> q ℕ.≤ r -> (+ p / r) {r≢0} ℚ.≤ (+ p / q) {q≢0}
q≤r⇒+p/r≤+p/q p (suc k₁) (suc k₂) q≤r = ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg p (ℤ.+≤+ q≤r))

p≤q⇒p/r≤q/r : ∀ (p q : ℤ) -> ∀ (r : ℕ) -> {r≢0 : r ≢0} -> p ℤ.≤ q -> (p / r) {r≢0} ℚ.≤ (q / r) {r≢0}
p≤q⇒p/r≤q/r p q (suc k₁) p≤q = ℚ.*≤* (ℤP.*-monoʳ-≤-nonNeg (suc k₁) p≤q)

archimedean-ℚ₂ : ∀ (p : ℚᵘ) -> ∀ (r : ℤ) -> ℚ.Positive p -> ∃ λ (N-1 : ℕ) -> r / (suc N-1) ℚ.< p
archimedean-ℚ₂ (mkℚᵘ (+_ p) q-1) r posp/q = let q = suc q-1; N-1 = proj₁ (archimedean-ℚ (+ p / q) (r / 1) posp/q); N = suc N-1 in N-1 , (begin-strict
  r / N                             ≈⟨ ℚ.*≡* (sym (ℤP.*-assoc r (+ 1) (+ N))) ⟩
  r / 1 ℚ.* (+ 1 / N)               <⟨ ℚP.*-monoˡ-<-pos _ (proj₂ (archimedean-ℚ (+ p / q) (r / 1) posp/q)) ⟩
  (+ N-1 ℤ.* + p) / q ℚ.* (+ 1 / N) ≤⟨ ℚP.*-monoˡ-≤-nonNeg _ (p≤q⇒p/r≤q/r (+ N-1 ℤ.* + p) (+ N ℤ.* + p) q (ℤP.*-monoʳ-≤-nonNeg p (ℤ.+≤+ (ℕP.n≤1+n N-1)))) ⟩
  (+ N ℤ.* + p) / q ℚ.* (+ 1 / N)   ≈⟨ ℚ.*≡* (solve 3 (λ N p q -> N :* p :* con (+ 1) :* q := p :* (q :* N)) _≡_.refl (+ N) (+ p) (+ q)) ⟩
  + p / q                            ∎)
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver.+-*-Solver

equality-lemma-if : ∀ x y -> x ≃ y -> ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
                  ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
                  ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 1 / j) {j≢0}
equality-lemma-if x y (*≃* x₁) (suc k₁) = let j = suc k₁ in 2 ℕ.* j , let N = 2 ℕ.* j in λ { (suc k₂) n≥N → let n = suc k₂ in begin
  ℚ.∣ seq x n ℚ.- seq y n ∣ ≤⟨ x₁ n ⟩
  + 2 / n                   ≤⟨ ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg 2 (ℤ.+≤+ n≥N)) ⟩
  + 2 / N                   ≈⟨ ℚ.*≡* (sym (ℤP.*-identityˡ (+ 2 ℤ.* + j))) ⟩
  + 1 / j                     ∎}
  where open ℚP.≤-Reasoning

p<q⇒0<q-p : ∀ p q -> p ℚ.< q -> 0ℚᵘ ℚ.< q ℚ.- p
p<q⇒0<q-p p q p<q = begin-strict
  0ℚᵘ     ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ p) ⟩
  p ℚ.- p <⟨ ℚP.+-monoˡ-< (ℚ.- p) p<q ⟩
  q ℚ.- p  ∎
  where open ℚP.≤-Reasoning

equality-lemma-onlyif : ∀ x y ->
                        (∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
                         ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 1 / j) {j≢0}) ->
                        x ≃ y
                        
equality-lemma-onlyif x y hyp1 = *≃* λ { n {n≢0} -> lem n {n≢0} (∣xₙ-yₙ∣≤2/n+3/j n {n≢0})}
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _+:_
        ; _:-_ to _-:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver

    ∣xₙ-yₙ∣≤2/n+3/j : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
                      ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0} ℚ.+ (+ 3 / j) {j≢0}
    ∣xₙ-yₙ∣≤2/n+3/j (suc k₁) (suc k₂) = let n = suc k₁; j = suc k₂; Nⱼ = suc (proj₁ (hyp1 j)); m = j ℕ.⊔ Nⱼ in begin
       ℚ.∣ seq x n ℚ.- seq y n ∣                         ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ xₘ yₘ xₙ yₙ ->
                                                           xₙ -: yₙ =: xₙ -: xₘ +: (xₘ -: yₘ) +: (yₘ -: yₙ))
                                                           ℚP.≃-refl (seq x m) (seq y m) (seq x n) (seq y n)) ⟩
      ℚ.∣ seq x n ℚ.- seq x m  ℚ.+
         (seq x m ℚ.- seq y m) ℚ.+
         (seq y m ℚ.- seq y n) ∣                        ≤⟨ ℚP.≤-trans
                                                           (ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x n ℚ.- seq x m ℚ.+ (seq x m ℚ.- seq y m)) (seq y m ℚ.- seq y n))
                                                           (ℚP.+-monoˡ-≤ ℚ.∣ seq y m ℚ.- seq y n ∣
                                                           (ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x n ℚ.- seq x m) (seq x m ℚ.- seq y m))) ⟩
      ℚ.∣ seq x n ℚ.- seq x m ∣ ℚ.+
      ℚ.∣ seq x m ℚ.- seq y m ∣ ℚ.+
      ℚ.∣ seq y m ℚ.- seq y n ∣                         ≤⟨ ℚP.+-mono-≤
                                                           (ℚP.+-mono-≤ (reg x n m) (proj₂ (hyp1 j) m
                                                                        (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred Nⱼ)) (ℕP.m≤n⊔m j Nⱼ))))
                                                           (reg y m n) ⟩
      (+ 1 / n ℚ.+ + 1 / m) ℚ.+
      + 1 / j               ℚ.+
      (+ 1 / m ℚ.+ + 1 / n)                             ≈⟨ ℚ.*≡* (solve 3 (λ j m n ->
                                                           (((con (+ 1) :* m :+ con (+ 1) :* n) :* j :+ con (+ 1) :* (n :* m)) :* (m :* n) :+
                                                           ((con (+ 1) :* n :+ con (+ 1) :* m) :* (n :* m :* j))) :* (n :* (m :* j)) :=
                                                           (con (+ 2) :* (m :* j) :+ (con (+ 2) :* j :+ con (+ 1) :* m) :* n) :* ((n :* m :* j) :* (m :* n)))
                                                           _≡_.refl (+ j) (+ m) (+ n)) ⟩
      + 2 / n ℚ.+ (+ 2 / m ℚ.+ + 1 / j)                 ≤⟨ ℚP.+-monoʳ-≤ (+ 2 / n) {+ 2 / m ℚ.+ + 1 / j} {+ 3 / j}
                                                           (ℚP.≤-respʳ-≃ {+ 2 / m ℚ.+ + 1 / j} {+ 2 / j ℚ.+ + 1 / j} {+ 3 / j}
                                                           (ℚ.*≡* {+ 2 / j ℚ.+ + 1 / j} {+ 3 / j}
                                                           (solve 1 (λ j -> (con (+ 2) :* j :+ con (+ 1) :* j) :* j := con (+ 3) :* (j :* j)) _≡_.refl (+ j)))
                                                           (ℚP.+-monoˡ-≤ (+ 1 / j) {+ 2 / m} {+ 2 / j} (ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg 2 (ℤP.i≤i⊔j (+ j) (+ Nⱼ)))))) ⟩
      + 2 / n ℚ.+ + 3 / j                                ∎
      

    lem : ∀ (n : ℕ) -> {n≢0 : n ≢0} ->
          (∀ (j : ℕ) -> {j≢0 : j ≢0} ->
          ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0} ℚ.+ (+ 3 / j) {j≢0}) ->
          ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0}
    lem (suc k₂) hyp2 = let n = suc k₂ in
                          ℚP.≮⇒≥ (λ {hyp3 -> let arch = archimedean-ℚ₂ (ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.- + 2 / n) (+ 3)
                                                        (ℚ.positive (p<q⇒0<q-p (+ 2 / n) ℚ.∣ seq x n ℚ.- seq y n ∣ hyp3))
                                                        ; j = suc (proj₁ arch)
                                                        ; Nⱼ = suc (proj₁ (hyp1 j))
                                                        ; m = j ℕ.⊔ Nⱼ in
                          ℚP.<-irrefl ℚP.≃-refl (begin-strict
      + 2 / n ℚ.+ + 3 / j                               ≈⟨ ℚP.+-comm (+ 2 / n) (+ 3 / j) ⟩
      + 3 / j ℚ.+ + 2 / n                               <⟨ ℚP.+-monoˡ-< (+ 2 / n) (proj₂ arch) ⟩
      ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.- + 2 / n ℚ.+ + 2 / n ≈⟨ ℚsolve 2 (λ a b -> a -: b +: b =: a) ℚP.≃-refl ℚ.∣ seq x n ℚ.- seq y n ∣ (+ 2 / n) ⟩
      ℚ.∣ seq x n ℚ.- seq y n ∣                         ≤⟨ ∣xₙ-yₙ∣≤2/n+3/j n j ⟩
      + 2 / n ℚ.+ + 3 / j                                ∎)})

≃-trans : Transitive _≃_
≃-trans {x} {y} {z} x≃y y≃z = equality-lemma-onlyif x z (λ { (suc k₁) ->
                              let j = suc k₁; eqxy = equality-lemma-if x y x≃y; eqyz = equality-lemma-if y z y≃z
                                      ; N₁ = proj₁ (eqxy (2 ℕ.* j)); N₂ = proj₁ (eqyz (2 ℕ.* j)); N = suc (N₁ ℕ.⊔ N₂) in
                                      N , λ { (suc k₂) n≥N → let n = suc k₂
                                                                     ; N₁⊔N₂≤n = ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N)) n≥N in begin
  ℚ.∣ seq x n ℚ.- seq z n ∣                               ≈⟨ ℚP.∣-∣-cong (ℚsolve 3 (λ x y z ->
                                                             x ℚ:- z ℚ:= x ℚ:- y ℚ:+ (y ℚ:- z))
                                                             ℚP.≃-refl (seq x n) (seq y n) (seq z n)) ⟩
  ℚ.∣ seq x n ℚ.- seq y n ℚ.+ (seq y n ℚ.- seq z n) ∣     ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x n ℚ.- seq y n) (seq y n ℚ.- seq z n) ⟩
  ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.+ ℚ.∣ seq y n ℚ.- seq z n ∣ ≤⟨ ℚP.+-mono-≤
                                                             (proj₂ (eqxy (2 ℕ.* j)) n (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) N₁⊔N₂≤n))
                                                             (proj₂ (eqyz (2 ℕ.* j)) n (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) N₁⊔N₂≤n)) ⟩
  + 1 / (2 ℕ.* j) ℚ.+ + 1 / (2 ℕ.* j)                     ≈⟨ ℚ.*≡* (solve 1 (λ j ->
                                                             (con (+ 1) :* (con (+ 2) :* j) :+ con (+ 1) :* (con (+ 2) :* j)) :* j :=
                                                             con (+ 1) :* ((con (+ 2) :* j) :* (con (+ 2) :* j)))
                                                             _≡_.refl (+ j)) ⟩
  + 1 / j                                                  ∎}})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _ℚ:+_
        ; _:=_ to _ℚ:=_
        ; _:*_ to _ℚ:*_
        ; _:-_ to _ℚ:-_
        )
    open ℤ-Solver.+-*-Solver

≃-isEquivalence : IsEquivalence _≃_
≃-isEquivalence = record
  { refl = ≃-refl
  ; sym = ≃-symm
  ; trans = ≃-trans
  }

≃-setoid : Setoid 0ℓ 0ℓ
≃-setoid = record
  { isEquivalence = ≃-isEquivalence
  }

module ≃-Reasoning where
  open import Relation.Binary.Reasoning.Setoid ≃-setoid
    public

antidensity-ℤ : ¬(∃ λ (n : ℤ) -> + 0 ℤ.< n × n ℤ.< + 1)
antidensity-ℤ (.(+[1+ n ]) , ℤ.+<+ {n = suc n} m<n , ℤ.+<+ (ℕ.s≤s ()))

p≤∣p∣ : ∀ p -> p ℚ.≤ ℚ.∣ p ∣
p≤∣p∣ (mkℚᵘ (+_ n) denominator-2) = ℚP.≤-refl
p≤∣p∣ (mkℚᵘ (-[1+_] n) denominator-2) = ℚ.*≤* ℤ.-≤+

infixl 6 _+_ _-_ _⊔_ _⊓_ _⊓₂_
infixl 7 _*_
infix 8 -_ _⋆

_+_ : ℝ -> ℝ -> ℝ
seq (x + y) n = seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)
reg (x + y) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  ℚ.∣ seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m) ℚ.-
     (seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)) ∣    ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ xₘ yₘ xₙ yₙ ->
                                                   xₘ +: yₘ -: (xₙ +: yₙ) =: (xₘ -: xₙ +: (yₘ -: yₙ)))
                                                   ℚP.≃-refl (seq x (2 ℕ.* m)) (seq y (2 ℕ.* m)) (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  ℚ.∣ seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n) ℚ.+
      (seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n)) ∣   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n)) (seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n)) ⟩
  ℚ.∣ seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n) ∣ ℚ.+
  ℚ.∣ seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n) ∣     ≤⟨ ℚP.+-mono-≤ (reg x (2 ℕ.* m) (2 ℕ.* n)) (reg y (2 ℕ.* m) (2 ℕ.* n)) ⟩
  + 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n) ℚ.+
  (+ 1 / (2 ℕ.* m) ℚ.+ + 1 / (2 ℕ.* n))         ≈⟨ ℚ.*≡* (solve 2 (λ m n ->
                                                   (((con (+ 1) :* (con (+ 2) :* n) :+ con (+ 1) :* (con (+ 2) :* m))
                                                   :* ((con (+ 2) :* m) :* (con (+ 2) :* n))) :+
                                                   (con (+ 1) :* (con (+ 2) :* n) :+ con (+ 1) :* (con (+ 2) :* m))
                                                   :* ((con (+ 2) :* m) :* (con (+ 2) :* n))) :* (m :* n) :=
                                                   (con (+ 1) :* n :+ con (+ 1) :* m) :*
                                                   (((con (+ 2) :* m) :* (con (+ 2) :* n)) :*
                                                   (((con (+ 2) :* m) :* (con (+ 2) :* n)))))
                                                   _≡_.refl (+ m) (+ n)) ⟩
  + 1 / m ℚ.+ + 1 / n                            ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _+:_
        ; _:-_ to _-:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver

-_ : ℝ -> ℝ
seq (- x) n = ℚ.- seq x n
reg (- x) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  ℚ.∣ ℚ.- seq x m ℚ.- ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.≃-sym (ℚP.≃-reflexive (ℚP.neg-distrib-+ (seq x m) (ℚ.- seq x n)))) ⟩
  ℚ.∣ ℚ.- (seq x m ℚ.- seq x n) ∣   ≤⟨ ℚP.≤-respˡ-≃ (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (seq x m ℚ.- seq x n))) (reg x m n) ⟩
  + 1 / m ℚ.+ + 1 / n                ∎
  where open ℚP.≤-Reasoning

_-_ : ℝ -> ℝ -> ℝ
x - y = x + (- y)

_⊔_ : ℝ -> ℝ -> ℝ
seq (x ⊔ y) n = (seq x n) ℚ.⊔ (seq y n)
reg (x ⊔ y) (suc k₁) (suc k₂) = [ left , right ]′ (ℚP.≤-total (seq x m ℚ.⊔ seq y m) (seq x n ℚ.⊔ seq y n))
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver
    m = suc k₁
    n = suc k₂

    lem : ∀ (a b c d : ℚᵘ) -> a ℚ.≤ b -> ∀ (r s : ℕ) -> {r≢0 : r ≢0} -> {s≢0 : s ≢0} ->
                               ℚ.∣ b ℚ.- d ∣ ℚ.≤ ((+ 1) / r) {r≢0} ℚ.+ ((+ 1) / s) {s≢0} ->
                               (a ℚ.⊔ b) ℚ.- (c ℚ.⊔ d) ℚ.≤ ((+ 1) / r) {r≢0} ℚ.+ ((+ 1) / s) {s≢0} 
    lem a b c d a≤b r s hyp = begin
      (a ℚ.⊔ b) ℚ.- (c ℚ.⊔ d)     ≤⟨ ℚP.+-monoʳ-≤ (a ℚ.⊔ b) (ℚP.neg-mono-≤ (ℚP.p≤q⊔p c d)) ⟩
      (a ℚ.⊔ b) ℚ.- d             ≈⟨ ℚP.+-congˡ (ℚ.- d) (ℚP.p≤q⇒p⊔q≃q a≤b) ⟩
      b ℚ.- d                     ≤⟨ p≤∣p∣ (b ℚ.- d) ⟩
      ℚ.∣ b ℚ.- d ∣               ≤⟨ hyp ⟩
      ((+ 1) / r) ℚ.+ ((+ 1) / s)  ∎

    left : seq x m ℚ.⊔ seq y m ℚ.≤ seq x n ℚ.⊔ seq y n ->
           ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
    left hyp1 = [ xn≤yn , yn≤xn ]′ (ℚP.≤-total (seq x n) (seq y n))
      where
        xn≤yn : seq x n ℚ.≤ seq y n -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        xn≤yn hyp2 = begin
          ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ ((seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n))))
                                                                  (ℚP.∣-∣-cong (solve 2 (λ a b -> :- (a :- b) := b :- a)
                                                                  (ℚ.*≡* _≡_.refl) (seq x m ℚ.⊔ seq y m) (seq x n ℚ.⊔ seq y n))) ⟩
          ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
          (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m)       ≤⟨ lem (seq x n) (seq y n) (seq x m) (seq y m) hyp2 m n
                                                                   (ℚP.≤-respʳ-≃ (ℚP.+-comm (+ 1 / n) (+ 1 / m)) (reg y n m)) ⟩
          (+ 1 / m) ℚ.+ (+ 1 / n)                                ∎ 

        yn≤xn : seq y n ℚ.≤ seq x n -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        yn≤xn hyp2 = begin
          ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ ((seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n))))
                                                                  (ℚP.∣-∣-cong (solve 2 (λ a b -> :- (a :- b) := b :- a)
                                                                  (ℚ.*≡* _≡_.refl) (seq x m ℚ.⊔ seq y m) (seq x n ℚ.⊔ seq y n))) ⟩
          ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
          (seq x n ℚ.⊔ seq y n) ℚ.- (seq x m ℚ.⊔ seq y m)       ≈⟨ ℚP.≃-trans (ℚP.+-congʳ (seq x n ℚ.⊔ seq y n)
                                                                   (ℚP.-‿cong {seq x m ℚ.⊔ seq y m} {seq y m ℚ.⊔ seq x m} (ℚP.⊔-comm (seq x m) (seq y m))))
                                                                   (ℚP.+-congˡ (ℚ.- (seq y m ℚ.⊔ seq x m)) (ℚP.⊔-comm (seq x n) (seq y n))) ⟩
          (seq y n ℚ.⊔ seq x n) ℚ.- (seq y m ℚ.⊔ seq x m) 
                                                                ≤⟨ lem (seq y n) (seq x n) (seq y m) (seq x m) hyp2 m n
                                                                   (ℚP.≤-respʳ-≃ (ℚP.+-comm (+ 1 / n) (+ 1 / m)) (reg x n m)) ⟩
          (+ 1 / m) ℚ.+ (+ 1 / n)                                ∎

    right : seq x n ℚ.⊔ seq y n ℚ.≤ seq x m ℚ.⊔ seq y m ->
            ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
    right hyp1 = [ xm≤ym , ym≤xm ]′ (ℚP.≤-total (seq x m) (seq y m))
      where
        xm≤ym : seq x m ℚ.≤ seq y m -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        xm≤ym hyp2 = ℚP.≤-respˡ-≃ (ℚP.≃-sym (ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1))) (lem (seq x m) (seq y m) (seq x n) (seq y n) hyp2 m n (reg y m n)) 

        ym≤xm : seq y m ℚ.≤ seq x m -> ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ℚ.≤ ((+ 1) / m) ℚ.+ ((+ 1) / n)
        ym≤xm hyp2 = begin
           ℚ.∣ (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
           (seq x m ℚ.⊔ seq y m) ℚ.- (seq x n ℚ.⊔ seq y n)       ≈⟨ ℚP.≃-trans (ℚP.+-congˡ (ℚ.- (seq x n ℚ.⊔ seq y n)) (ℚP.⊔-comm (seq x m) (seq y m)))
                                                                    (ℚP.+-congʳ (seq y m ℚ.⊔ seq x m)
                                                                    (ℚP.-‿cong {seq x n ℚ.⊔ seq y n} {seq y n ℚ.⊔ seq x n} (ℚP.⊔-comm (seq x n) (seq y n)))) ⟩
           (seq y m ℚ.⊔ seq x m) ℚ.- (seq y n ℚ.⊔ seq x n)       ≤⟨ lem (seq y m) (seq x m) (seq y n) (seq x n) hyp2 m n (reg x m n) ⟩
           (+ 1 / m) ℚ.+ (+ 1 / n)                                                      ∎

-- Alternative definition of minimum for convenience. Equivalent to Bishop's, of course.
_⊓_ : ℝ -> ℝ -> ℝ
seq (x ⊓ y) n = seq x n ℚ.⊓ seq y n
reg (x ⊓ y) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂; xₘ = seq x m; yₘ = seq y m; xₙ = seq x n; yₙ = seq y n in begin
  ℚ.∣ xₘ ℚ.⊓ yₘ ℚ.- xₙ ℚ.⊓ yₙ ∣               ≈⟨ ℚP.∣-∣-cong (ℚP.+-cong
                                                 (ℚP.⊓-cong (ℚP.≃-sym (ℚP.neg-involutive xₘ)) (ℚP.≃-sym (ℚP.neg-involutive yₘ)))
                                                 (ℚP.-‿cong (ℚP.⊓-cong (ℚP.≃-sym (ℚP.neg-involutive xₙ)) (ℚP.≃-sym (ℚP.neg-involutive yₙ))))) ⟩
  ℚ.∣ ((ℚ.- (ℚ.- xₘ)) ℚ.⊓ (ℚ.- (ℚ.- yₘ))) ℚ.-
      ((ℚ.- (ℚ.- xₙ)) ℚ.⊓ (ℚ.- (ℚ.- yₙ))) ∣   ≈⟨ ℚP.∣-∣-cong (ℚP.+-cong
                                                 (ℚP.≃-sym (ℚP.neg-distrib-⊔-⊓ (ℚ.- xₘ) (ℚ.- yₘ)))
                                                 (ℚP.-‿cong (ℚP.≃-sym (ℚP.neg-distrib-⊔-⊓ (ℚ.- xₙ) (ℚ.- yₙ))))) ⟩
  ℚ.∣ ℚ.- ((ℚ.- xₘ) ℚ.⊔ (ℚ.- yₘ)) ℚ.-
     (ℚ.- ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ))) ∣          ≈⟨ ℚP.∣-∣-cong (solve 2 (λ m n -> (:- m) :- (:- n) := n :- m) ℚP.≃-refl ((ℚ.- xₘ) ℚ.⊔ (ℚ.- yₘ)) ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ))) ⟩
  ℚ.∣ ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ)) ℚ.-
      ((ℚ.- xₘ) ℚ.⊔ (ℚ.- yₘ)) ∣               ≤⟨ reg (- x ⊔ - y) n m ⟩
  + 1 / n ℚ.+ + 1 / m                         ≈⟨ ℚP.+-comm (+ 1 / n) (+ 1 / m) ⟩
  + 1 / m ℚ.+ + 1 / n                          ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver

_⊓₂_ : ℝ -> ℝ -> ℝ
x ⊓₂ y = - ((- x) ⊔ (- y))

∣∣p∣-∣q∣∣≤∣p-q∣ : ∀ p q -> ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ℚ.≤ ℚ.∣ p ℚ.- q ∣
∣∣p∣-∣q∣∣≤∣p-q∣ p q = [ left p q , right p q ]′ (ℚP.≤-total ℚ.∣ q ∣ ℚ.∣ p ∣)
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver

    left : ∀ p q -> ℚ.∣ q ∣ ℚ.≤ ℚ.∣ p ∣ -> ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ℚ.≤ ℚ.∣ p ℚ.- q ∣
    left p q hyp = begin
      ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣             ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp) ⟩
      ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣                   ≈⟨ ℚP.+-congˡ (ℚ.- ℚ.∣ q ∣) (ℚP.∣-∣-cong (solve 2 (λ p q ->
                                               p := p :- q :+ q) ℚP.≃-refl p q)) ⟩
      ℚ.∣ p ℚ.- q ℚ.+ q ∣ ℚ.- ℚ.∣ q ∣       ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- ℚ.∣ q ∣) (ℚP.∣p+q∣≤∣p∣+∣q∣ (p ℚ.- q) q) ⟩
      ℚ.∣ p ℚ.- q ∣ ℚ.+ ℚ.∣ q ∣ ℚ.- ℚ.∣ q ∣ ≈⟨ solve 2 (λ x y -> x :+ y :- y := x)
                                              ℚP.≃-refl ℚ.∣ p ℚ.- q ∣ ℚ.∣ q ∣ ⟩
      ℚ.∣ p ℚ.- q ∣ ∎

    right : ∀ p q -> ℚ.∣ p ∣ ℚ.≤ ℚ.∣ q ∣ -> ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ℚ.≤ ℚ.∣ p ℚ.- q ∣
    right p q hyp = begin
      ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣))) (ℚP.∣-∣-cong
                                  (solve 2 (λ p q -> :- (p :- q) := q :- p) ℚP.≃-refl ℚ.∣ p ∣ ℚ.∣ q ∣)) ⟩
      ℚ.∣ ℚ.∣ q ∣ ℚ.- ℚ.∣ p ∣ ∣ ≤⟨ left q p hyp ⟩
      ℚ.∣ q ℚ.- p ∣            ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (q ℚ.- p))) (ℚP.∣-∣-cong
                                  (solve 2 (λ p q -> :- (q :- p) := p :- q) ℚP.≃-refl p q)) ⟩
      ℚ.∣ p ℚ.- q ∣  ∎

least-ℤ>ℚ : ∀ (p : ℚᵘ) -> ∃ λ (K : ℤ) ->
            p ℚ.< K / 1 × ∀ (n : ℤ) -> p ℚ.< n / 1 -> K ℤ.≤ n
least-ℤ>ℚ p/q = let p = ↥ p/q; q = ↧ₙ p/q; r = p modℕ q; t = p divℕ q in + 1 ℤ.+ t , greater , least
  where
    open ℤP.≤-Reasoning
    open ℤ-Solver.+-*-Solver
    greater : p/q ℚ.< (+ 1 ℤ.+ (↥ p/q divℕ ↧ₙ p/q)) / 1
    greater = let p = ↥ p/q; q = ↧ₙ p/q; r = p modℕ q; t = p divℕ q in ℚ.*<* (begin-strict
      p ℤ.* + 1           ≡⟨ trans (ℤP.*-identityʳ p) (a≡a%ℕn+[a/ℕn]*n p q) ⟩
      + r ℤ.+ t ℤ.* + q   <⟨ ℤP.+-monoˡ-< (t ℤ.* (+ q)) (ℤ.+<+ (n%ℕd<d p q)) ⟩
      + q ℤ.+ t ℤ.* + q   ≡⟨ solve 2 (λ q t -> q :+ t :* q := (con (+ 1) :+ t) :* q) _≡_.refl (+ q) t ⟩
      (+ 1 ℤ.+ t) ℤ.* + q  ∎)

    least : ∀ (n : ℤ) -> p/q ℚ.< n / 1 -> + 1 ℤ.+ (↥ p/q divℕ ↧ₙ p/q) ℤ.≤ n
    least n p/q<n = ℤP.≮⇒≥ (λ {hyp -> antidensity-ℤ (n ℤ.- (↥ p/q divℕ ↧ₙ p/q) , 0<n-t hyp , n-t<1 hyp)})
      where
        0<n-t : n ℤ.< + 1 ℤ.+ (↥ p/q divℕ ↧ₙ p/q) -> + 0 ℤ.< n ℤ.- (↥ p/q divℕ ↧ₙ p/q)
        0<n-t hyp = let p = ↥ p/q; q = ↧ₙ p/q; r = p modℕ q; t = p divℕ q in ℤP.*-cancelʳ-<-nonNeg q (begin-strict
          + 0 ℤ.* + q                     ≡⟨ ℤP.*-zeroˡ (+ q) ⟩
          + 0                             ≤⟨ ℤ.+≤+ ℕ.z≤n ⟩
          + r                             ≡⟨ solve 3 (λ r t q -> r := r :+ t :* q :- t :* q) _≡_.refl (+ r) t (+ q) ⟩
          + r ℤ.+ t ℤ.* + q ℤ.- t ℤ.* + q ≡⟨ cong (λ x -> x ℤ.- t ℤ.* + q) (sym (a≡a%ℕn+[a/ℕn]*n p q)) ⟩
          p ℤ.- t ℤ.* + q                 <⟨ ℤP.+-monoˡ-< (ℤ.- (t ℤ.* + q)) (subst (ℤ._< n ℤ.* + q) (ℤP.*-identityʳ p) (ℚP.drop-*<* p/q<n)) ⟩
          n ℤ.* + q ℤ.- t ℤ.* + q         ≡⟨ solve 3 (λ n t q -> n :* q :- t :* q := (n :- t) :* q) _≡_.refl n t (+ q) ⟩
          (n ℤ.- t) ℤ.* + q                ∎)

        n-t<1 : n ℤ.< + 1 ℤ.+ (↥ p/q divℕ ↧ₙ p/q) -> n ℤ.- (↥ p/q divℕ ↧ₙ p/q) ℤ.< + 1
        n-t<1 hyp = let t = ↥ p/q divℕ ↧ₙ p/q in begin-strict
          n ℤ.- t         <⟨ ℤP.+-monoˡ-< (ℤ.- t) hyp ⟩
          + 1 ℤ.+ t ℤ.- t ≡⟨ solve 1 (λ t -> con (+ 1) :+ t :- t := con (+ 1)) _≡_.refl t ⟩
          + 1              ∎

2ℚᵘ : ℚᵘ
2ℚᵘ = + 2 / 1

K : ℝ -> ℕ
K x = let p = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ); q = ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) in suc ℤ.∣ p divℕ q ∣

private
  Kx=1+t : ∀ x -> + K x ≡ + 1 ℤ.+ (↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))
  Kx=1+t x = let t = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) in begin-equality
    + K x             ≡⟨ _≡_.refl ⟩
    + 1 ℤ.+ + ℤ.∣ t ∣ ≡⟨ cong (λ x -> + 1 ℤ.+ x) (ℤP.0≤n⇒+∣n∣≡n (0≤n⇒0≤n/ℕd (↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ)) (↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))
                         (ℚP.≥0⇒↥≥0 (ℚP.≤-trans (ℚP.0≤∣p∣ (seq x 1)) (ℚP.p≤p+q {ℚ.∣ seq x 1 ∣} {2ℚᵘ} _))))) ⟩
    + 1 ℤ.+ t          ∎
    where
      open ℤP.≤-Reasoning

-- We could do a rewrite Kx=1+t here to get a one-line proof, but the performance becomes abysmal
-- (Around 30sec to typecheck rewrite).
canonical-well-defined : ∀ (x : ℝ) -> ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< + K x / 1 ×
                         ∀ (n : ℤ) -> ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< n / 1 -> + K x ℤ.≤ n
canonical-well-defined x = left , right
  where
    left : ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< + K x / 1
    left = let t = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) in begin-strict
      ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ <⟨ proj₁ (proj₂ (least-ℤ>ℚ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))) ⟩
      (+ 1 ℤ.+ t) / 1                     ≈⟨ ℚP.≃-reflexive (ℚP./-cong (sym (Kx=1+t x)) _≡_.refl _ _) ⟩
      + K x / 1              ∎
      where open ℚP.≤-Reasoning

    right : ∀ (n : ℤ) -> ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< n / 1 -> + K x ℤ.≤ n
    right n hyp = let t = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) in begin
      + K x     ≡⟨ Kx=1+t x ⟩
      + 1 ℤ.+ t ≤⟨ proj₂ (proj₂ (least-ℤ>ℚ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))) n hyp ⟩
      n          ∎
      
      where open ℤP.≤-Reasoning

1/n≤1 : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> (+ 1 / n) {n≢0} ℚ.≤ 1ℚᵘ
1/n≤1 (suc k₁) = let n = suc k₁ in ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg 1 {+ 1} {+ n} (ℤ.+≤+ (ℕ.s≤s ℕ.z≤n)))

canonical-strict-upper-bound : ∀ (x : ℝ) -> ∀ (n : ℕ) -> {n ≢0} -> ℚ.∣ seq x n ∣ ℚ.< + K x / 1
canonical-strict-upper-bound x (suc k₁) = let n = suc k₁ in begin-strict
  ℚ.∣ seq x n ∣                               ≈⟨ ℚP.∣-∣-cong (solve 2 (λ xₙ x₁ ->
                                                 xₙ := x₁ :+ (xₙ :- x₁)) ℚP.≃-refl (seq x n) (seq x 1)) ⟩
  ℚ.∣ seq x 1 ℚ.+ (seq x n ℚ.- seq x 1)∣      ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x 1) (seq x n ℚ.- seq x 1) ⟩
  ℚ.∣ seq x 1 ∣ ℚ.+ ℚ.∣ seq x n ℚ.- seq x 1 ∣ ≤⟨ ℚP.+-monoʳ-≤ ℚ.∣ seq x 1 ∣ (reg x n 1) ⟩
  ℚ.∣ seq x 1 ∣ ℚ.+ (+ 1 / n ℚ.+ ℚ.1ℚᵘ)       ≤⟨ ℚP.+-monoʳ-≤ ℚ.∣ seq x 1 ∣ (ℚP.+-monoˡ-≤ ℚ.1ℚᵘ {+ 1 / n} {1ℚᵘ} (1/n≤1 n)) ⟩
  ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ                       <⟨ proj₁ (canonical-well-defined x) ⟩
  + K x / 1                                    ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver

p≤r⇒p/q≤r/q : ∀ (p r : ℤ) -> ∀ (q : ℕ) -> {q≢0 : q ≢0} -> p ℤ.≤ r -> (p / q) {q≢0} ℚ.≤ (r / q) {q≢0}
p≤r⇒p/q≤r/q p r (suc k₁) p≤r = let q = suc k₁ in ℚ.*≤* (ℤP.*-monoʳ-≤-nonNeg q p≤r)

_*_ : ℝ -> ℝ -> ℝ
seq (x * y) n = seq x (2 ℕ.* (K x ℕ.⊔ K y) ℕ.* n) ℚ.* seq y (2 ℕ.* (K x ℕ.⊔ K y) ℕ.* n)
reg (x * y) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂; k = K x ℕ.⊔ K y; 2km = 2 ℕ.* k ℕ.* m; 2kn = 2 ℕ.* k ℕ.* n
                                         ; x₂ₖₘ = seq x 2km; y₂ₖₘ = seq y 2km; x₂ₖₙ = seq x 2kn; y₂ₖₙ = seq y 2kn
                                         ; ∣x₂ₖₘ∣≤k = ℚP.≤-trans (ℚP.<⇒≤ (canonical-strict-upper-bound x 2km)) (p≤r⇒p/q≤r/q (+ K x) (+ k) 1 (ℤP.i≤i⊔j (+ K x) (+ K y)))
                                         ; ∣y₂ₖₙ∣≤k = ℚP.≤-trans (ℚP.<⇒≤ (canonical-strict-upper-bound y 2kn)) (p≤r⇒p/q≤r/q (+ K y) (+ k) 1 (ℤP.i≤j⊔i (+ K x) (+ K y))) in begin
  ℚ.∣ x₂ₖₘ ℚ.* y₂ₖₘ ℚ.- x₂ₖₙ ℚ.* y₂ₖₙ ∣        ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ xm ym xn yn ->
                                                  xm *: ym -: xn *: yn =:
                                                  xm *: (ym -: yn) +: yn *: (xm -: xn))
                                                  (ℚ.*≡* _≡_.refl) x₂ₖₘ y₂ₖₘ x₂ₖₙ y₂ₖₙ) ⟩
  ℚ.∣ x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ) ℚ.+
      y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ) ∣              ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ))
                                                                (y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ)) ⟩
  ℚ.∣ x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ) ∣ ℚ.+
  ℚ.∣ y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ) ∣              ≈⟨ ℚP.+-cong (ℚP.∣p*q∣≃∣p∣*∣q∣ x₂ₖₘ (y₂ₖₘ ℚ.- y₂ₖₙ)) (ℚP.∣p*q∣≃∣p∣*∣q∣ y₂ₖₙ (x₂ₖₘ ℚ.- x₂ₖₙ)) ⟩
  ℚ.∣ x₂ₖₘ ∣ ℚ.* ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣ ℚ.+
  ℚ.∣ y₂ₖₙ ∣ ℚ.* ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣           ≤⟨ ℚP.+-mono-≤
                                                  (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣} _ ∣x₂ₖₘ∣≤k)
                                                  (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣} _ ∣y₂ₖₙ∣≤k) ⟩
  (+ k / 1) ℚ.* ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣ ℚ.+
  (+ k / 1) ℚ.* ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣           ≤⟨ ℚP.+-mono-≤
                                                 (ℚP.*-monoʳ-≤-nonNeg {+ k / 1} _ (reg y 2km 2kn))
                                                 (ℚP.*-monoʳ-≤-nonNeg {+ k / 1} _ (reg x 2km 2kn)) ⟩
  (+ k / 1) ℚ.* ((+ 1 / 2km) ℚ.+
  (+ 1 / 2kn)) ℚ.+
  (+ k / 1) ℚ.* ((+ 1 / 2km) ℚ.+
  (+ 1 / 2kn))                               ≈⟨ ℚP.≃-sym (ℚP.*-distribˡ-+ (+ k / 1) ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn)) ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn))) ⟩

  (+ k / 1) ℚ.* ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn)
  ℚ.+ ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn)))         ≈⟨ ℚ.*≡* (solve 3 (λ k m n ->

  {- Function for the solver -}
  (k :* ((((con (+ 1) :* (con (+ 2) :* k :* n)) :+ (con (+ 1) :* (con (+ 2) :* k :* m))) :* ((con (+ 2) :* k :* m) :* (con (+ 2) :* k :* n))) :+
  (((con (+ 1) :* (con (+ 2) :* k :* n)) :+ (con (+ 1) :* (con (+ 2) :* k :* m))) :* ((con (+ 2) :* k :* m) :* (con (+ 2) :* k :* n)))))
  :* (m :* n) :=
  (con (+ 1) :* n :+ con (+ 1) :* m) :*
  (con (+ 1) :* (((con (+ 2) :* k :* m) :* (con (+ 2) :* k :* n)):* ((con (+ 2) :* k :* m) :* (con (+ 2) :* k :* n)))))
  -- Other solver inputs
  _≡_.refl (+ k) (+ m) (+ n)) ⟩
  
  (+ 1 / m) ℚ.+ (+ 1 / n)                     ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _+:_
        ; _:-_ to _-:_
        ; _:*_ to _*:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver
    
_⋆ : ℚᵘ -> ℝ
seq (p ⋆) n = p
reg (p ⋆) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  ℚ.∣ p ℚ.- p ∣       ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ p) ⟩
  0ℚᵘ                 ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 1 / m ℚ.+ + 1 / n  ∎
  where
    open ℚP.≤-Reasoning

-- Properties of _+_
+-cong : Congruent₂ _≃_ _+_
+-cong {x} {z} {y} {w} (*≃* x₁) (*≃* x₂) = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n) ℚ.-
     (seq z (2 ℕ.* n) ℚ.+ seq w (2 ℕ.* n)) ∣    ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ x y z w ->
                                                   x +: y -: (z +: w) =: ((x -: z) +: (y -: w)))
                                                   ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)) (seq z (2 ℕ.* n)) (seq w (2 ℕ.* n))) ⟩
  ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq z (2 ℕ.* n) ℚ.+
     (seq y (2 ℕ.* n) ℚ.- seq w (2 ℕ.* n)) ∣    ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x (2 ℕ.* n) ℚ.- seq z (2 ℕ.* n)) (seq y (2 ℕ.* n) ℚ.- seq w (2 ℕ.* n)) ⟩
  ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq z (2 ℕ.* n) ∣ ℚ.+
  ℚ.∣ seq y (2 ℕ.* n) ℚ.- seq w (2 ℕ.* n) ∣     ≤⟨ ℚP.+-mono-≤ (x₁ (2 ℕ.* n)) (x₂ (2 ℕ.* n)) ⟩
  + 2 / (2 ℕ.* n) ℚ.+ + 2 / (2 ℕ.* n)           ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                   (con (+ 2) :* (con (+ 2) :* n) :+ con (+ 2) :* (con (+ 2) :* n)) :* n :=
                                                   (con (+ 2) :* ((con (+ 2) :* n) :* (con (+ 2) :* n)))) _≡_.refl (+ n)) ⟩
  + 2 / n                                        ∎})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _+:_
        ; _:-_ to _-:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver

+-congʳ : ∀ x {y z} -> y ≃ z -> x + y ≃ x + z
+-congʳ x y≃z = +-cong ≃-refl y≃z

+-congˡ : ∀ x {y z} -> y ≃ z -> y + x ≃ z + x
+-congˡ x y≃z = +-cong y≃z ≃-refl

+-comm : Commutative _≃_ _+_
+-comm x y = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ (seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)) ℚ.-
      (seq y (2 ℕ.* n) ℚ.+ seq x (2 ℕ.* n)) ∣   ≈⟨ ℚP.∣-∣-cong (solve 2 (λ x y ->
                                                   (x :+ y) :- (y :+ x) := con (0ℚᵘ))
                                                   ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  0ℚᵘ                                           ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  (+ 2) / n                                      ∎})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver

+-assoc : Associative _≃_ _+_
+-assoc x y z = *≃* (λ { (suc k₁) -> let n = suc k₁; 2n = 2 ℕ.* n; 4n = 2 ℕ.* 2n in begin
  ℚ.∣ ((seq x 4n ℚ.+ seq y 4n) ℚ.+ seq z 2n) ℚ.-
      (seq x 2n ℚ.+ (seq y 4n ℚ.+ seq z 4n)) ∣                ≈⟨ ℚP.∣-∣-cong (ℚsolve 5 (λ x4 y4 z2 x2 z4 ->
                                                                                  ((x4 +: y4) +: z2) -: (x2 +: (y4 +: z4)) =:
                                                                                  (x4 -: x2) +: (z2 -: z4))
                                                                                  ℚP.≃-refl (seq x 4n) (seq y 4n) (seq z 2n) (seq x 2n) (seq z 4n)) ⟩
  ℚ.∣ (seq x 4n ℚ.- seq x 2n) ℚ.+ (seq z 2n ℚ.- seq z 4n) ∣   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x 4n ℚ.- seq x 2n) (seq z 2n ℚ.- seq z 4n) ⟩
  ℚ.∣ seq x 4n ℚ.- seq x 2n ∣ ℚ.+ ℚ.∣ seq z 2n ℚ.- seq z 4n ∣ ≤⟨ ℚP.+-mono-≤ (reg x 4n 2n) (reg z 2n 4n) ⟩
  ((+ 1 / 4n) ℚ.+ (+ 1 / 2n)) ℚ.+ ((+ 1 / 2n) ℚ.+ (+ 1 / 4n)) ≈⟨ ℚ.*≡* (solve 1 ((λ 2n ->
                                                                 ((con (+ 1) :* 2n :+ con (+ 1) :* (con (+ 2) :* 2n)) :*
                                                                 (2n :* (con (+ 2) :* 2n)) :+
                                                                 (con (+ 1) :* (con (+ 2) :* 2n) :+ con (+ 1) :* 2n) :*
                                                                 ((con (+ 2) :* 2n) :* 2n)) :* 2n :=
                                                                 con (+ 3) :* (((con (+ 2) :* 2n) :* 2n) :*
                                                                 (2n :* (con (+ 2) :* 2n)))))
                                                                 _≡_.refl (+ 2n)) ⟩
  + 3 / 2n                                                    ≤⟨ ℚ.*≤* (ℤP.*-monoʳ-≤-nonNeg 2n (ℤ.+≤+ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n {1})))))) ⟩
  + 4 / 2n                                                    ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                                            con (+ 4) :* n := con (+ 2) :* (con (+ 2) :* n))
                                                                            _≡_.refl (+ n)) ⟩
  + 2 / n                                                      ∎})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _+:_
        ; _:-_ to _-:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver

0ℝ : ℝ
0ℝ = 0ℚᵘ ⋆

1ℝ : ℝ
1ℝ = 1ℚᵘ ⋆

+-identityˡ : LeftIdentity _≃_ 0ℝ _+_
+-identityˡ x = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ (0ℚᵘ ℚ.+ seq x (2 ℕ.* n)) ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- seq x n) (ℚP.+-identityˡ (seq x (2 ℕ.* n)))) ⟩
  ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq x n ∣           ≤⟨ reg x (2 ℕ.* n) n ⟩
  (+ 1 / (2 ℕ.* n)) ℚ.+ (+ 1 / n)             ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                            (con (+ 1) :* n :+ con (+ 1) :* (con (+ 2) :* n)) :* (con (+ 2) :* n) :=
                                                            con (+ 3) :* ((con (+ 2) :* n) :* n))
                                                            _≡_.refl (+ n)) ⟩
  + 3 / (2 ℕ.* n)                             ≤⟨ ℚ.*≤* (ℤP.*-monoʳ-≤-nonNeg (2 ℕ.* n) (ℤ.+≤+ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n {1})))))) ⟩
  + 4 / (2 ℕ.* n)                             ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                            con (+ 4) :* n := con (+ 2) :* (con (+ 2) :* n))
                                                            _≡_.refl (+ n)) ⟩
  + 2 / n                                      ∎})
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver.+-*-Solver

+-identityʳ : RightIdentity _≃_ 0ℝ _+_
+-identityʳ x = ≃-trans (+-comm x 0ℝ) (+-identityˡ x)

+-identity : Identity _≃_ 0ℝ _+_
+-identity = +-identityˡ , +-identityʳ

+-inverseʳ : RightInverse _≃_ 0ℝ -_ _+_
+-inverseʳ x = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ (seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)) ℚ.+ 0ℚᵘ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ 0ℚᵘ (ℚP.+-inverseʳ (seq x (2 ℕ.* n)))) ⟩
  0ℚᵘ                                                 ≤⟨ ℚ.*≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ n))) (ℤ.+≤+ ℕ.z≤n)) ⟩
  + 2 / n                                              ∎})
  where open ℚP.≤-Reasoning

+-inverseˡ : LeftInverse _≃_ 0ℝ -_ _+_
+-inverseˡ x = ≃-trans (+-comm (- x) x) (+-inverseʳ x)

+-inverse : Inverse _≃_ 0ℝ -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

-- Properties of _⋆
⋆-distrib-+ : ∀ (p r : ℚᵘ) -> (p ℚ.+ r) ⋆ ≃ p ⋆ + r ⋆
⋆-distrib-+ x y = *≃* (λ { (suc k₁) -> let n = suc k₁; p = ↥ x; q = ↧ₙ x; u = ↥ y; v = ↧ₙ y in begin
  ℚ.∣ ((p / q) ℚ.+ (u / v)) ℚ.- ((p / q) ℚ.+ (u / v)) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ ((p / q) ℚ.+ (u / v))) ⟩
  0ℚᵘ                                                   ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  (+ 2) / n                                              ∎})
  where open ℚP.≤-Reasoning

⋆-distrib-neg : ∀ (p : ℚᵘ) -> (ℚ.- p) ⋆ ≃ - (p ⋆)
⋆-distrib-neg p = *≃* λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.- p ℚ.- (ℚ.- p) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (ℚ.- p)) ⟩
  0ℚᵘ                     ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  (+ 2) / n                ∎}
  where open ℚP.≤-Reasoning

-- Properties of _*_
abstract
  regular⇒cauchy : ∀ (x : ℝ) -> ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (m n : ℕ) ->
                   m ℕ.≥ N -> n ℕ.≥ N -> ℚ.∣ seq x m ℚ.- seq x n ∣ ℚ.≤ (+ 1 / j) {j≢0}
  regular⇒cauchy x (suc k₁) = let j = suc k₁ in 2 ℕ.* j , λ { (suc k₂) (suc k₃) m≥N n≥N → let m = suc k₂; n = suc k₃ in begin 
        ℚ.∣ seq x m ℚ.- seq x n ∣ ≤⟨ reg x m n ⟩
        (+ 1 / m) ℚ.+ (+ 1 / n)   ≤⟨ ℚP.+-mono-≤ (q≤r⇒+p/r≤+p/q 1 (2 ℕ.* j) m m≥N) (q≤r⇒+p/r≤+p/q 1 (2 ℕ.* j) n n≥N) ⟩
        (+ 1 / (2 ℕ.* j)) ℚ.+ (+ 1 / (2 ℕ.* j)) ≈⟨ ℚ.*≡* (solve 1 (λ j ->
                                                   (con (+ 1) :* (con (+ 2) :* j) :+ con (+ 1) :* (con (+ 2) :* j)) :* j :=
                                                   (con (+ 1) :* ((con (+ 2) :* j) :* (con (+ 2) :* j)))) _≡_.refl (+ j)) ⟩
        + 1 / j                    ∎}
    where
      open ℚP.≤-Reasoning
      open ℚ-Solver.+-*-Solver using ()
        renaming
          ( solve to ℚsolve
          ; _:+_ to _+:_
          ; _:-_ to _-:_
          ; _:*_ to _*:_
          ; _:=_ to _=:_
          )
      open ℤ-Solver.+-*-Solver

  equals-to-cauchy : ∀ x y -> x ≃ y -> ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
                     ∃ λ (N : ℕ) -> ∀ (m n : ℕ) -> m ℕ.≥ N -> n ℕ.≥ N ->
                     ℚ.∣ seq x m ℚ.- seq y n ∣ ℚ.≤ (+ 1 / j) {j≢0}
  equals-to-cauchy x y x≃y (suc k₁) = let j = suc k₁; N₁ = suc (proj₁ (equality-lemma-if x y x≃y (2 ℕ.* j))); N₂ = proj₁ (regular⇒cauchy x (2 ℕ.* j)); N = N₁ ℕ.⊔ N₂ in
                                      N , λ { (suc k₂) (suc k₃) m≥N n≥N -> let m = suc k₂; n = suc k₃ in begin
        ℚ.∣ seq x m ℚ.- seq y n ∣     ≈⟨ ℚP.∣-∣-cong (ℚsolve 3 (λ xm yn xn ->
                                         xm -: yn =: (xm -: xn) +: (xn -: yn))
                                         ℚP.≃-refl (seq x m) (seq y n) (seq x n)) ⟩
        ℚ.∣ (seq x m ℚ.- seq x n) ℚ.+
            (seq x n ℚ.- seq y n) ∣   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x m ℚ.- seq x n)
                                                         (seq x n ℚ.- seq y n) ⟩
        ℚ.∣ seq x m ℚ.- seq x n ∣ ℚ.+
        ℚ.∣ seq x n ℚ.- seq y n ∣     ≤⟨ ℚP.+-mono-≤
                                         (proj₂ (regular⇒cauchy x (2 ℕ.* j)) m n (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) m≥N) (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) n≥N))
                                         (proj₂ (equality-lemma-if x y x≃y (2 ℕ.* j)) n (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N₁)) (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) n≥N))) ⟩
        (+ 1 / (2 ℕ.* j)) ℚ.+
        (+ 1 / (2 ℕ.* j))             ≈⟨ ℚ.*≡* (solve 1 (λ j ->
                                         (con (+ 1) :* (con (+ 2) :* j) :+ (con (+ 1) :* (con (+ 2) :* j))) :* j :=
                                         (con (+ 1) :* ((con (+ 2) :* j) :* (con (+ 2) :* j))))
                                         _≡_.refl (+ j)) ⟩
        + 1 / j                        ∎}
    where
      open ℚP.≤-Reasoning
      open ℚ-Solver.+-*-Solver using ()
        renaming
          ( solve to ℚsolve
          ; _:+_ to _+:_
          ; _:-_ to _-:_
          ; _:*_ to _*:_
          ; _:=_ to _=:_
          )
      open ℤ-Solver.+-*-Solver

*-cong : Congruent₂ _≃_ _*_
*-cong {x} {z} {y} {w} x≃z y≃w = equality-lemma-onlyif (x * y) (z * w) partA                                                     
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
        renaming
          ( solve to ℚsolve
          ; _:+_ to _+:_
          ; _:-_ to _-:_
          ; _:*_ to _*:_
          ; _:=_ to _=:_
          )
    open ℤ-Solver.+-*-Solver

    partA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
            ℚ.∣ seq (x * y) n ℚ.- seq (z * w) n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    partA (suc k₁) = N , partB
      where
        j = suc k₁
        r = K x ℕ.⊔ K y
        t = K z ℕ.⊔ K w
        N₁ = proj₁ (equals-to-cauchy x z x≃z (K y ℕ.* (2 ℕ.* j)))
        N₂ = proj₁ (equals-to-cauchy y w y≃w (K z ℕ.* (2 ℕ.* j)))
        N = suc (N₁ ℕ.⊔ N₂)

        partB : ∀ (n : ℕ) -> n ℕ.≥ N -> ℚ.∣ seq (x * y) n ℚ.- seq (z * w) n ∣ ℚ.≤ (+ 1 / j)
        partB (suc k₂) n≥N = let n = suc k₂
                                   ; x₂ᵣₙ = seq x (2 ℕ.* r ℕ.* n)
                                   ; y₂ᵣₙ = seq y (2 ℕ.* r ℕ.* n)
                                   ; z₂ₜₙ = seq z (2 ℕ.* t ℕ.* n)
                                   ; w₂ₜₙ = seq w (2 ℕ.* t ℕ.* n) in begin
          ℚ.∣ x₂ᵣₙ ℚ.* y₂ᵣₙ ℚ.- z₂ₜₙ ℚ.* w₂ₜₙ ∣             ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ x y z w ->
                                                               x *: y -: z *: w =: y *: (x -: z) +: z *: (y -: w))
                                                               ℚP.≃-refl x₂ᵣₙ y₂ᵣₙ z₂ₜₙ w₂ₜₙ) ⟩
          ℚ.∣ y₂ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- z₂ₜₙ) ℚ.+
              z₂ₜₙ ℚ.* (y₂ᵣₙ ℚ.- w₂ₜₙ) ∣                   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (y₂ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- z₂ₜₙ))
                                                                              (z₂ₜₙ ℚ.* (y₂ᵣₙ ℚ.- w₂ₜₙ)) ⟩
          ℚ.∣ y₂ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- z₂ₜₙ) ∣ ℚ.+
          ℚ.∣ z₂ₜₙ ℚ.* (y₂ᵣₙ ℚ.- w₂ₜₙ) ∣                   ≈⟨ ℚP.+-cong (ℚP.∣p*q∣≃∣p∣*∣q∣ y₂ᵣₙ ((x₂ᵣₙ ℚ.- z₂ₜₙ)))
                                                                        (ℚP.∣p*q∣≃∣p∣*∣q∣ z₂ₜₙ (y₂ᵣₙ ℚ.- w₂ₜₙ)) ⟩
          ℚ.∣ y₂ᵣₙ ∣ ℚ.* ℚ.∣ x₂ᵣₙ ℚ.- z₂ₜₙ ∣ ℚ.+
          ℚ.∣ z₂ₜₙ ∣ ℚ.* ℚ.∣ y₂ᵣₙ ℚ.- w₂ₜₙ ∣               ≤⟨ ℚP.+-mono-≤ (ℚP.≤-trans
                                                                          (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ᵣₙ ℚ.- z₂ₜₙ ∣} _
                                                                                               (ℚP.<⇒≤ (canonical-strict-upper-bound y (2 ℕ.* r ℕ.* n))))
                                                                          (ℚP.*-monoʳ-≤-nonNeg {+ K y / 1} _
                                                                                               (proj₂ (equals-to-cauchy x z x≃z (K y ℕ.* (2 ℕ.* j)))
                                                                                                      (2 ℕ.* r ℕ.* n) (2 ℕ.* t ℕ.* n)
                                                                                                      (N₁≤ (2 ℕ.* r ℕ.* n) (N≤2kn r))
                                                                                                      (N₁≤ (2 ℕ.* t ℕ.* n) (N≤2kn t)))))
                                                                          (ℚP.≤-trans
                                                                          (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₂ᵣₙ ℚ.- w₂ₜₙ ∣} _
                                                                                               (ℚP.<⇒≤ (canonical-strict-upper-bound z (2 ℕ.* t ℕ.* n))))
                                                                          (ℚP.*-monoʳ-≤-nonNeg {+ K z / 1} _
                                                                                               (proj₂ (equals-to-cauchy y w y≃w (K z ℕ.* (2 ℕ.* j)))
                                                                                               (2 ℕ.* r ℕ.* n) (2 ℕ.* t ℕ.* n)
                                                                                               (N₂≤ (2 ℕ.* r ℕ.* n) (N≤2kn r))
                                                                                               (N₂≤ (2 ℕ.* t ℕ.* n) (N≤2kn t))))) ⟩
          (+ K y / 1) ℚ.* (+ 1 / (K y ℕ.* (2 ℕ.* j))) ℚ.+
          (+ K z / 1) ℚ.* (+ 1 / (K z ℕ.* (2 ℕ.* j)))     ≈⟨ ℚ.*≡* (solve 3 (λ Ky Kz j ->

          -- Function for solver
          ((Ky :* con (+ 1)) :* (con (+ 1) :* (Kz :* (con (+ 2) :* j))) :+ (Kz :* con (+ 1) :* (con (+ 1) :* (Ky :* (con (+ 2) :* j))))) :* j :=
          con (+ 1) :* ((con (+ 1) :* (Ky :* (con (+ 2) :* j))) :* (con (+ 1) :* (Kz :* (con (+ 2) :* j)))))
          _≡_.refl (+ K y) (+ K z) (+ j)) ⟩
          
          + 1 / j                                          ∎
          where
            N≤2kn : ∀ (k : ℕ) -> {k ≢0} -> N ℕ.≤ 2 ℕ.* k ℕ.* (suc k₂)
            N≤2kn (suc k) = ℕP.≤-trans n≥N (ℕP.m≤n*m (suc k₂) {2 ℕ.* (suc k)} ℕP.0<1+n)

            N₁≤ : ∀ (k : ℕ) -> N ℕ.≤ k -> N₁ ℕ.≤ k
            N₁≤ k N≤k = ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N)) N≤k)

            N₂≤ : ∀ (k : ℕ) -> N ℕ.≤ k -> N₂ ℕ.≤ k
            N₂≤ k N≤k = ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N)) N≤k)

*-congˡ : LeftCongruent _≃_ _*_
*-congˡ y≃z = *-cong ≃-refl y≃z

*-congʳ : RightCongruent _≃_ _*_
*-congʳ y≃z = *-cong y≃z ≃-refl

*-comm : Commutative _≃_ _*_
*-comm x y = *≃* λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ seq (x * y) n ℚ.- seq (y * x) n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (seq (x * y) n)
                                                      (ℚP.-‿cong (ℚP.≃-sym (xyℚ≃yxℚ n)))) ⟩
  ℚ.∣ seq (x * y) n ℚ.- seq (x * y) n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq (x * y) n)) ⟩
  0ℚᵘ                                   ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                ∎}
  where
    open ℚP.≤-Reasoning
    xyℚ≃yxℚ : ∀ (n : ℕ) -> seq (x * y) n ℚ.≃ seq (y * x) n
    xyℚ≃yxℚ n = begin-equality
      seq x (2 ℕ.* (K x ℕ.⊔ K y) ℕ.* n) ℚ.*
      seq y (2 ℕ.* (K x ℕ.⊔ K y) ℕ.* n)     ≡⟨ cong (λ r ->
                                               seq x (2 ℕ.* r ℕ.* n) ℚ.* seq y (2 ℕ.* r ℕ.* n))
                                               (ℕP.⊔-comm (K x) (K y)) ⟩
      seq x (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n) ℚ.*
      seq y (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n)     ≈⟨ ℚP.*-comm (seq x (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n))
                                                         (seq y (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n)) ⟩
      seq y (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n) ℚ.*
      seq x (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n)      ∎

*-assoc : Associative _≃_ _*_
*-assoc x y z = equality-lemma-onlyif (x * y * z) (x * (y * z)) lemA
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _+:_
        ; _:-_ to _-:_
        ; _:*_ to _*:_
        ; :-_  to -:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver
    
    lemA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
          ℚ.∣ seq (x * y * z) n ℚ.- seq (x * (y * z)) n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    lemA (suc k₁) = N , lemB
      where
        j = suc k₁
        N₁ = proj₁ (regular⇒cauchy x (K y ℕ.* K z ℕ.* (3 ℕ.* j)))
        N₂ = proj₁ (regular⇒cauchy y (K x ℕ.* K z ℕ.* (3 ℕ.* j)))
        N₃ = proj₁ (regular⇒cauchy z (K x ℕ.* K y ℕ.* (3 ℕ.* j)))
        N = suc (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃)

        lemB : ∀ (n : ℕ) -> n ℕ.≥ N -> ℚ.∣ seq (x * y * z) n ℚ.- seq (x * (y * z)) n ∣ ℚ.≤ + 1 / j
        lemB (suc k₂) n≥N = begin
          ℚ.∣ x₄ᵣₛₙ ℚ.* y₄ᵣₛₙ ℚ.* z₂ₛₙ ℚ.- x₂ᵤₙ ℚ.* (y₄ₜᵤₙ ℚ.* z₄ₜᵤₙ) ∣ ≈⟨ ℚP.∣-∣-cong (ℚsolve 6 (λ a b c d e f ->
                                                                           a *: b *: c -: d *: (e *: f) =:
                                                                           (b *: c) *: (a -: d) +: d *: (c *: (b -: e) +: e *: (c -: f)))
                                                                           ℚP.≃-refl x₄ᵣₛₙ y₄ᵣₛₙ z₂ₛₙ x₂ᵤₙ y₄ₜᵤₙ z₄ₜᵤₙ) ⟩
          ℚ.∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ) ℚ.+
          x₂ᵤₙ ℚ.* (z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ℚ.+
          y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ)) ∣                                 ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ ((y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ))
                                                                           (x₂ᵤₙ ℚ.* (z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ℚ.+ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ))) ⟩
          ℚ.∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ) ∣ ℚ.+
          ℚ.∣ x₂ᵤₙ ℚ.* (z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ℚ.+
          y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ)) ∣                                 ≤⟨ ℚP.≤-respˡ-≃ (ℚP.≃-sym (ℚP.+-congʳ ℚ.∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ) ∣
                                                                           (ℚP.∣p*q∣≃∣p∣*∣q∣ x₂ᵤₙ (z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ℚ.+ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ)))))
                                                                           (ℚP.+-monoʳ-≤ ℚ.∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ) ∣
                                                                           (ℚP.*-monoʳ-≤-nonNeg {ℚ.∣ x₂ᵤₙ ∣} _ (ℚP.∣p+q∣≤∣p∣+∣q∣
                                                                           (z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ)) (y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ))))) ⟩
          ℚ.∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) ℚ.* (x₄ᵣₛₙ ℚ.- x₂ᵤₙ) ∣ ℚ.+
          ℚ.∣ x₂ᵤₙ ∣ ℚ.* (ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣ ℚ.+
          ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣)                             ≈⟨ ℚP.+-congˡ
                                                                          (ℚ.∣ x₂ᵤₙ ∣ ℚ.* (ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣ ℚ.+  ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣))
                                                                          (ℚP.≃-trans (ℚP.∣p*q∣≃∣p∣*∣q∣ (y₄ᵣₛₙ ℚ.* z₂ₛₙ) (x₄ᵣₛₙ ℚ.- x₂ᵤₙ))
                                                                          (ℚP.*-congʳ (ℚP.∣p*q∣≃∣p∣*∣q∣ y₄ᵣₛₙ z₂ₛₙ))) ⟩
          ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣ ℚ.+
          ℚ.∣ x₂ᵤₙ ∣ ℚ.* (ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣ ℚ.+
          ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣)                             ≈⟨ ℚP.+-congʳ (ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣)
                                                                           (ℚP.*-distribˡ-+ ℚ.∣ x₂ᵤₙ ∣ ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣
                                                                           ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣) ⟩
          ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣ ℚ.+
          (ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣ ℚ.+
          ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣)              ≤⟨ ℚP.≤-trans (ℚP.+-monoʳ-≤ (ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣)
                                                                          (ℚP.≤-trans (ℚP.+-monoʳ-≤ (ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣) part3)
                                                                          (ℚP.+-monoˡ-≤ (+ 1 / (3 ℕ.* j)) part2)))
                                                                          (ℚP.+-monoˡ-≤ (+ 1 / (3 ℕ.* j) ℚ.+ + 1 / (3 ℕ.* j)) part1) ⟩
          (+ 1 / (3 ℕ.* j)) ℚ.+ ((+ 1 / (3 ℕ.* j)) ℚ.+ (+ 1 / (3 ℕ.* j))) ≈⟨ ℚ.*≡* (solve 1 (λ j ->

          (con (+ 1) :* ((con (+ 3) :* j) :* (con (+ 3) :* j)) :+ ((con (+ 1) :* (con (+ 3) :* j)) :+ (con (+ 1) :* (con (+ 3) :* j))) :* (con (+ 3) :* j)) :* j :=
          (con (+ 1) :* ((con (+ 3) :* j) :* ((con (+ 3) :* j) :* (con (+ 3) :* j)))))
          
          _≡_.refl (+ j)) ⟩
          + 1 / j                                                        ∎
          where
            n = suc k₂
            r = K x ℕ.⊔ K y
            s = K (x * y) ℕ.⊔ K z
            u = K x ℕ.⊔ K (y * z)
            t = K y ℕ.⊔ K z

            x₄ᵣₛₙ = seq x (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n))
            y₄ᵣₛₙ = seq y (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n))
            z₂ₛₙ = seq z (2 ℕ.* s ℕ.* n)
            x₂ᵤₙ = seq x (2 ℕ.* u ℕ.* n)
            y₄ₜᵤₙ = seq y (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))
            z₄ₜᵤₙ = seq z (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))

            N≤2an : ∀ (a : ℕ) -> {a ≢0} -> N ℕ.≤ 2 ℕ.* a ℕ.* n
            N≤2an (suc a) = ℕP.≤-trans n≥N (ℕP.m≤n*m n {2 ℕ.* (suc a)} ℕP.0<1+n)

            N≤4abn : ∀ (a b : ℕ) -> {a ≢0} -> {b ≢0} -> N ℕ.≤ 2 ℕ.* a ℕ.* (2 ℕ.* b ℕ.* n)
            N≤4abn (suc a) (suc b) = let a = suc a; b = suc b in
                                     ℕP.≤-trans (N≤2an b) (ℕP.m≤n*m (2 ℕ.* b ℕ.* n) {2 ℕ.* a} ℕP.0<1+n)

            N₁≤_ : {m : ℕ} -> N ℕ.≤ m -> N₁ ℕ.≤ m
            N₁≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃) (ℕP.n≤1+n (ℕ.pred N)))) N≤m

            N₂≤_ : {m : ℕ} -> N ℕ.≤ m -> N₂ ℕ.≤ m
            N₂≤_ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃) (ℕP.n≤1+n (ℕ.pred N)))) N≤m

            N₃≤ : {m : ℕ} -> N ℕ.≤ m -> N₃ ℕ.≤ m
            N₃≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂) N₃) (ℕP.n≤1+n (ℕ.pred N))) N≤m

            part1 : ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣ ℚ.≤ + 1 / (3 ℕ.* j)
            part1 = begin
              ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣            ≤⟨ ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣} _ (ℚP.≤-trans
                                                                               (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₂ₛₙ ∣} _ (ℚP.<⇒≤
                                                                               (canonical-strict-upper-bound y (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)))))
                                                                               (ℚP.*-monoʳ-≤-nonNeg {(+ K y) / 1} _ (ℚP.<⇒≤
                                                                               (canonical-strict-upper-bound z (2 ℕ.* s ℕ.* n))))) ⟩
              (+ (K y ℕ.* K z) / 1) ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣                ≤⟨ ℚP.*-monoʳ-≤-nonNeg {+ (K y ℕ.* K z) / 1} _
                                                                               (proj₂ (regular⇒cauchy x (K y ℕ.* K z ℕ.* (3 ℕ.* j)))
                                                                               (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)) (2 ℕ.* u ℕ.* n)
                                                                               (N₁≤ (N≤4abn r s))
                                                                               (N₁≤ (N≤2an u))) ⟩
              (+ (K y ℕ.* K z) / 1) ℚ.* (+ 1 / (K y ℕ.* K z ℕ.* (3 ℕ.* j))) ≈⟨ ℚ.*≡* (solve 3 (λ Ky Kz j ->
                                                                               ((Ky :* Kz) :* con (+ 1)) :* (con (+ 3) :* j) :=
                                                                               (con (+ 1) :* (con (+ 1) :* (Ky :* Kz :* (con (+ 3) :* j)))))
                                                                               _≡_.refl (+ K y) (+ K z) (+ j)) ⟩
              + 1 / (3 ℕ.* j)                                                ∎

            part2 : ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣ ℚ.≤ + 1 / (3 ℕ.* j)
            part2 = begin
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣     ≈⟨ ℚP.≃-trans (ℚP.*-congˡ {ℚ.∣ x₂ᵤₙ ∣} (ℚP.∣p*q∣≃∣p∣*∣q∣ z₂ₛₙ (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ)))
                                                                    (ℚP.≃-sym (ℚP.*-assoc ℚ.∣ x₂ᵤₙ ∣ ℚ.∣ z₂ₛₙ ∣ ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣)) ⟩
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣ ≤⟨ ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣} _ (ℚP.≤-trans
                                                                    (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₂ₛₙ ∣} _
                                                                    (ℚP.<⇒≤ (canonical-strict-upper-bound x (2 ℕ.* u ℕ.* n))))
                                                                    (ℚP.*-monoʳ-≤-nonNeg {+ K x / 1} _
                                                                    (ℚP.<⇒≤ (canonical-strict-upper-bound z (2 ℕ.* s ℕ.* n))))) ⟩
              (+ (K x ℕ.* K z) / 1) ℚ.* ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣    ≤⟨ ℚP.*-monoʳ-≤-nonNeg {+ (K x ℕ.* K z) / 1} _
                                                                    (proj₂ (regular⇒cauchy y (K x ℕ.* K z ℕ.* (3 ℕ.* j)))
                                                                    (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)) (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))
                                                                    (N₂≤ (N≤4abn r s))
                                                                    (N₂≤ (N≤4abn t u))) ⟩
              (+ (K x ℕ.* K z) / 1) ℚ.*
              (+ 1 / (K x ℕ.* K z ℕ.* (3 ℕ.* j)))                ≈⟨ ℚ.*≡* (solve 3 (λ Kx Kz j ->
                                                                    (Kx :* Kz :* con (+ 1)) :* (con (+ 3) :* j) :=
                                                                    (con (+ 1) :* (con (+ 1) :* (Kx :* Kz :* (con (+ 3) :* j)))))
                                                                    _≡_.refl (+ K x) (+ K z) (+ j)) ⟩
              + 1 / (3 ℕ.* j)                                     ∎

            part3 : ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣ ℚ.≤ + 1 / (3 ℕ.* j)
            part3 = begin
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣     ≈⟨ ℚP.≃-trans (ℚP.*-congˡ {ℚ.∣ x₂ᵤₙ ∣} (ℚP.∣p*q∣≃∣p∣*∣q∣ y₄ₜᵤₙ (z₂ₛₙ ℚ.- z₄ₜᵤₙ)))
                                                                    (ℚP.≃-sym (ℚP.*-assoc ℚ.∣ x₂ᵤₙ ∣ ℚ.∣ y₄ₜᵤₙ ∣ ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣)) ⟩
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ y₄ₜᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣ ≤⟨ ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣} _ (ℚP.≤-trans
                                                                    (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₄ₜᵤₙ ∣} _
                                                                    (ℚP.<⇒≤ (canonical-strict-upper-bound x (2 ℕ.* u ℕ.* n))))
                                                                    (ℚP.*-monoʳ-≤-nonNeg {+ K x / 1} _
                                                                    (ℚP.<⇒≤ (canonical-strict-upper-bound y (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n)))))) ⟩
              (+ (K x ℕ.* K y) / 1) ℚ.* ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣      ≤⟨ ℚP.*-monoʳ-≤-nonNeg {+ (K x ℕ.* K y) / 1} _
                                                                     (proj₂ (regular⇒cauchy z (K x ℕ.* K y ℕ.* (3 ℕ.* j)))
                                                                     (2 ℕ.* s ℕ.* n) (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))
                                                                     (N₃≤ (N≤2an s))
                                                                     (N₃≤ (N≤4abn t u))) ⟩
              (+ (K x ℕ.* K y) / 1) ℚ.*
              (+ 1 / (K x ℕ.* K y ℕ.* (3 ℕ.* j)))                 ≈⟨ ℚ.*≡* (solve 3 (λ Kx Ky j ->
                                                                     (((Kx :* Ky) :* con (+ 1)) :* (con (+ 3) :* j)) :=
                                                                     (con (+ 1) :* (con (+ 1) :* (Kx :* Ky :* (con (+ 3) :* j)))))
                                                                     _≡_.refl (+ K x) (+ K y) (+ j)) ⟩
              + 1 / (3 ℕ.* j)                                      ∎

*-distribˡ-+ : _DistributesOverˡ_ _≃_ _*_ _+_
*-distribˡ-+ x y z = equality-lemma-onlyif (x * (y + z)) ((x * y) + (x * z)) lemA
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _+:_
        ; _:-_ to _-:_
        ; _:*_ to _*:_
        ; :-_  to -:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver

    lemA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
           ℚ.∣ seq (x * (y + z)) n ℚ.- seq ((x * y) + (x * z)) n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    lemA (suc k₁) = N , lemB
      where
        j = suc k₁
        r = K x ℕ.⊔ K (y + z)
        s = K x ℕ.⊔ K y
        t = K x ℕ.⊔ K z
        N₁ = proj₁ (regular⇒cauchy x (K y ℕ.* (4 ℕ.* j)))
        N₂ = proj₁ (regular⇒cauchy y (K x ℕ.* (4 ℕ.* j)))
        N₃ = proj₁ (regular⇒cauchy x (K z ℕ.* (4 ℕ.* j)))
        N₄ = proj₁ (regular⇒cauchy z (K x ℕ.* (4 ℕ.* j)))
        N = suc (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃ ℕ.⊔ N₄)

        lemB : ∀ (n : ℕ) -> n ℕ.≥ N ->
               ℚ.∣ seq (x * (y + z)) n ℚ.- seq ((x * y) + (x * z)) n ∣ ℚ.≤ + 1 / j
        lemB (suc k₂) n≥N = let x₂ᵣₙ = seq x (2 ℕ.* r ℕ.* n)
                                      ; x₄ₛₙ = seq x (2 ℕ.* s ℕ.* (2 ℕ.* n))
                                      ; x₄ₜₙ = seq x (2 ℕ.* t ℕ.* (2 ℕ.* n))
                                      ; y₄ᵣₙ = seq y (2 ℕ.* (2 ℕ.* r ℕ.* n))
                                      ; y₄ₛₙ = seq y (2 ℕ.* s ℕ.* (2 ℕ.* n))
                                      ; z₄ᵣₙ = seq z (2 ℕ.* (2 ℕ.* r ℕ.* n))
                                      ; z₄ₜₙ = seq z (2 ℕ.* t ℕ.* (2 ℕ.* n)) in begin
          ℚ.∣ x₂ᵣₙ ℚ.* (y₄ᵣₙ ℚ.+ z₄ᵣₙ) ℚ.-
            (x₄ₛₙ ℚ.* y₄ₛₙ ℚ.+ x₄ₜₙ ℚ.* z₄ₜₙ) ∣             ≈⟨ ℚP.∣-∣-cong (ℚsolve 7 (λ a b c d e f g ->
                                                               a *: (b +: c) -: (d *: e +: f *: g) =:
                                                               (b *: (a -: d) +: (d *: (b -: e)) +:
                                                               ((c *: (a -: f)) +: (f *: (c -: g)))))
                                                               ℚP.≃-refl
                                                               x₂ᵣₙ y₄ᵣₙ z₄ᵣₙ x₄ₛₙ y₄ₛₙ x₄ₜₙ z₄ₜₙ) ⟩

           ℚ.∣ y₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₛₙ) ℚ.+
              x₄ₛₙ ℚ.* (y₄ᵣₙ ℚ.- y₄ₛₙ) ℚ.+
             (z₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₜₙ) ℚ.+
              x₄ₜₙ ℚ.* (z₄ᵣₙ ℚ.- z₄ₜₙ)) ∣                   ≤⟨ ℚP.≤-trans (ℚP.∣p+q∣≤∣p∣+∣q∣
                                                               (y₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₛₙ) ℚ.+ x₄ₛₙ ℚ.* (y₄ᵣₙ ℚ.- y₄ₛₙ))
                                                               (z₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₜₙ) ℚ.+ x₄ₜₙ ℚ.* (z₄ᵣₙ ℚ.- z₄ₜₙ)))
                                                               (ℚP.+-mono-≤
                                                               (ℚP.∣p+q∣≤∣p∣+∣q∣ (y₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₛₙ)) ( x₄ₛₙ ℚ.* (y₄ᵣₙ ℚ.- y₄ₛₙ)))
                                                               (ℚP.∣p+q∣≤∣p∣+∣q∣ (z₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₜₙ)) ( x₄ₜₙ ℚ.* (z₄ᵣₙ ℚ.- z₄ₜₙ)))) ⟩
           ℚ.∣ y₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₛₙ) ∣ ℚ.+
           ℚ.∣ x₄ₛₙ ℚ.* (y₄ᵣₙ ℚ.- y₄ₛₙ) ∣ ℚ.+
          (ℚ.∣ z₄ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₄ₜₙ) ∣ ℚ.+
           ℚ.∣ x₄ₜₙ ℚ.* (z₄ᵣₙ ℚ.- z₄ₜₙ) ∣)                  ≈⟨ ℚP.+-cong (ℚP.+-cong (ℚP.∣p*q∣≃∣p∣*∣q∣ y₄ᵣₙ (x₂ᵣₙ ℚ.- x₄ₛₙ))
                                                                                    (ℚP.∣p*q∣≃∣p∣*∣q∣ x₄ₛₙ (y₄ᵣₙ ℚ.- y₄ₛₙ)))
                                                                         (ℚP.+-cong (ℚP.∣p*q∣≃∣p∣*∣q∣ z₄ᵣₙ (x₂ᵣₙ ℚ.- x₄ₜₙ))
                                                                                    (ℚP.∣p*q∣≃∣p∣*∣q∣ x₄ₜₙ (z₄ᵣₙ ℚ.- z₄ₜₙ))) ⟩
           ℚ.∣ y₄ᵣₙ ∣ ℚ.* ℚ.∣ x₂ᵣₙ ℚ.- x₄ₛₙ ∣ ℚ.+
           ℚ.∣ x₄ₛₙ ∣ ℚ.* ℚ.∣ y₄ᵣₙ ℚ.- y₄ₛₙ ∣ ℚ.+
          (ℚ.∣ z₄ᵣₙ ∣ ℚ.* ℚ.∣ x₂ᵣₙ ℚ.- x₄ₜₙ ∣ ℚ.+
           ℚ.∣ x₄ₜₙ ∣ ℚ.* ℚ.∣ z₄ᵣₙ ℚ.- z₄ₜₙ ∣)               ≤⟨ ℚP.+-mono-≤
                                                                (ℚP.+-mono-≤
                                                                            (ℚP.≤-trans
                                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ᵣₙ ℚ.- x₄ₛₙ ∣} _
                                                                                                 (ℚP.<⇒≤ (canonical-strict-upper-bound y
                                                                                                         (2 ℕ.* (2 ℕ.* r ℕ.* n)))))
                                                                            (ℚP.*-monoʳ-≤-nonNeg {+ K y / 1} _
                                                                                                 (proj₂ (regular⇒cauchy x (K y ℕ.* (4 ℕ.* j)))
                                                                                                 (2 ℕ.* r ℕ.* n) (2 ℕ.* s ℕ.* (2 ℕ.* n))
                                                                                                 (N₁≤ N≤2rn) (N₁≤ N≤4sn))))
                                                                            (ℚP.≤-trans
                                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₄ᵣₙ ℚ.- y₄ₛₙ ∣} _
                                                                                                 (ℚP.<⇒≤ (canonical-strict-upper-bound x
                                                                                                         (2 ℕ.* s ℕ.* (2 ℕ.* n)))))
                                                                            (ℚP.*-monoʳ-≤-nonNeg {+ K x / 1} _
                                                                                                 (proj₂ (regular⇒cauchy y (K x ℕ.* (4 ℕ.* j)))
                                                                                                 (2 ℕ.* (2 ℕ.* r ℕ.* n)) (2 ℕ.* s ℕ.* (2 ℕ.* n))
                                                                                                 (N₂≤ N≤4rn) (N₂≤ N≤4sn)))))
                                                                (ℚP.+-mono-≤
                                                                            (ℚP.≤-trans
                                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ᵣₙ ℚ.- x₄ₜₙ ∣} _
                                                                                                 (ℚP.<⇒≤ (canonical-strict-upper-bound z
                                                                                                         (2 ℕ.* (2 ℕ.* r ℕ.* n)))))
                                                                            (ℚP.*-monoʳ-≤-nonNeg {+ K z / 1} _
                                                                                                  (proj₂ (regular⇒cauchy x (K z ℕ.* (4 ℕ.* j)))
                                                                                                  (2 ℕ.* r ℕ.* n) (2 ℕ.* t ℕ.* (2 ℕ.* n))
                                                                                                  (N₃≤ N≤2rn) (N₃≤ N≤4tn))))
                                                                            (ℚP.≤-trans
                                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₄ᵣₙ ℚ.- z₄ₜₙ ∣} _
                                                                                                 (ℚP.<⇒≤ (canonical-strict-upper-bound x
                                                                                                         (2 ℕ.* t ℕ.* (2 ℕ.* n)))))
                                                                            (ℚP.*-monoʳ-≤-nonNeg {+ K x / 1} _
                                                                                                 (proj₂ (regular⇒cauchy z (K x ℕ.* (4 ℕ.* j)))
                                                                                                 (2 ℕ.* (2 ℕ.* r ℕ.* n)) (2 ℕ.* t ℕ.* (2 ℕ.* n))
                                                                                                 (N₄≤ N≤4rn) (N₄≤ N≤4tn))))) ⟩
           (+ K y / 1) ℚ.* (+ 1 / (K y ℕ.* (4 ℕ.* j))) ℚ.+
           (+ K x / 1) ℚ.* (+ 1 / (K x ℕ.* (4 ℕ.* j))) ℚ.+
          ((+ K z / 1) ℚ.* (+ 1 / (K z ℕ.* (4 ℕ.* j))) ℚ.+
           (+ K x / 1) ℚ.* (+ 1 / (K x ℕ.* (4 ℕ.* j))))     ≈⟨ ℚ.*≡* (solve 4 (λ Kx Ky Kz j ->

          {- Function for solver -}
          (((Ky :* con (+ 1)) :* (con (+ 1) :* (Kx :* (con (+ 4) :* j))) :+ ((Kx :* con (+ 1)) :* (con (+ 1) :* (Ky :* (con (+ 4) :* j))))) :*
          ((con (+ 1) :* (Kz :* (con (+ 4) :* j))) :* (con (+ 1) :* (Kx :* (con (+ 4) :* j)))) :+
          (((Kz :* con (+ 1)) :* (con (+ 1) :* (Kx :* (con (+ 4) :* j)))) :+ ((Kx :* con (+ 1)) :* (con (+ 1) :* (Kz :* (con (+ 4) :* j))))) :*
          ((con (+ 1) :* (Ky :* (con (+ 4) :* j))) :* (con (+ 1) :* (Kx :* (con (+ 4) :* j))))) :* j :=
          con (+ 1) :* (((con (+ 1) :* (Ky :* (con (+ 4) :* j))) :* (con (+ 1) :* (Kx :* (con (+ 4) :* j)))) :*
          ((con (+ 1) :* (Kz :* (con (+ 4) :* j))) :* (con (+ 1) :* (Kx :* (con (+ 4) :* j))))))
          _≡_.refl (+ K x) (+ K y) (+ K z) (+ j)) ⟩
          + 1 / j                                            ∎
          where
            n : ℕ
            n = suc k₂

            N≤2rn : N ℕ.≤ 2 ℕ.* r ℕ.* n
            N≤2rn = ℕP.≤-trans n≥N (ℕP.m≤n*m n {2 ℕ.* r} ℕP.0<1+n)

            N≤4sn : N ℕ.≤ 2 ℕ.* s ℕ.* (2 ℕ.* n)
            N≤4sn = ℕP.≤-trans (ℕP.≤-trans n≥N (ℕP.m≤n*m n {2} ℕP.0<1+n)) (ℕP.m≤n*m (2 ℕ.* n) {2 ℕ.* s} ℕP.0<1+n)

            N≤4rn : N ℕ.≤ 2 ℕ.* (2 ℕ.* r ℕ.* n)
            N≤4rn = ℕP.≤-trans (ℕP.≤-trans n≥N (ℕP.m≤n*m n {2 ℕ.* r} ℕP.0<1+n)) (ℕP.m≤n*m (2 ℕ.* r ℕ.* n) {2} ℕP.0<1+n)

            N≤4tn : N ℕ.≤ 2 ℕ.* t ℕ.* (2 ℕ.* n)
            N≤4tn = ℕP.≤-trans (ℕP.≤-trans n≥N (ℕP.m≤n*m n {2} ℕP.0<1+n)) (ℕP.m≤n*m (2 ℕ.* n) {2 ℕ.* t} ℕP.0<1+n)

            N₁≤_ : {m : ℕ} -> N ℕ.≤ m -> N₁ ℕ.≤ m
            N₁≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃))
                      (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄) (ℕP.n≤1+n (ℕ.pred N)))) N≤m

            N₂≤_ : {m : ℕ} -> N ℕ.≤ m -> N₂ ℕ.≤ m
            N₂≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃))
                      (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄) (ℕP.n≤1+n (ℕ.pred N)))) N≤m

            N₃≤_ : {m : ℕ} -> N ℕ.≤ m -> N₃ ℕ.≤ m
            N₃≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂) N₃) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄))
                      (ℕP.n≤1+n (ℕ.pred N))) N≤m

            N₄≤_ : {m : ℕ} -> N ℕ.≤ m -> N₄ ℕ.≤ m
            N₄≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄) (ℕP.n≤1+n (ℕ.pred N))) N≤m

*-distribʳ-+ : _DistributesOverʳ_ _≃_ _*_ _+_
*-distribʳ-+ x y z = begin
  (y + z) * x   ≈⟨ *-comm (y + z) x ⟩
  x * (y + z)   ≈⟨ *-distribˡ-+ x y z ⟩
  x * y + x * z ≈⟨ +-cong (*-comm x y) (*-comm x z) ⟩
  y * x + z * x  ∎
  where open ≃-Reasoning

*-distrib-+ : _DistributesOver_ _≃_ _*_ _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-identityˡ : LeftIdentity _≃_ 1ℝ _*_
*-identityˡ x = *≃* (λ { (suc k₁) → let n = suc k₁; k = K 1ℝ ℕ.⊔ K x in begin
  ℚ.∣ ℚ.1ℚᵘ ℚ.* seq x (2 ℕ.* k ℕ.* n) ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- seq x n) (ℚP.*-identityˡ (seq x (2 ℕ.* k ℕ.* n)))) ⟩
  ℚ.∣ seq x (2 ℕ.* k ℕ.* n) ℚ.- seq x n ∣         ≤⟨ reg x (2 ℕ.* k ℕ.* n) n ⟩
  (+ 1 / (2 ℕ.* k ℕ.* n)) ℚ.+ (+ 1 / n)           ≤⟨ ℚP.+-monoˡ-≤ (+ 1 / n) {+ 1 / (2 ℕ.* k ℕ.* n)} {+ 1 / n} (ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg 1 (ℤ.+≤+ (ℕP.m≤n*m n {2 ℕ.* k} ℕP.0<1+n)))) ⟩
  (+ 1 / n) ℚ.+ (+ 1 / n)                         ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                           (con (+ 1) :* n :+ con (+ 1) :* n) :* n := (con (+ 2) :* (n :* n)))
                                                           _≡_.refl (+ n)) ⟩
  + 2 / n                                          ∎})
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver.+-*-Solver

*-identityʳ : RightIdentity _≃_ 1ℝ _*_
*-identityʳ x = ≃-trans (*-comm x 1ℝ) (*-identityˡ x)

*-identity : Identity _≃_ 1ℝ _*_
*-identity = *-identityˡ , *-identityʳ

-‿cong : Congruent₁ _≃_ (-_)
-‿cong {x} {y} (*≃* x₁) = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.- seq x n ℚ.- (ℚ.- seq y n) ∣ ≡⟨ trans (cong (λ x → ℚ.∣ x ∣) (sym (ℚP.neg-distrib-+ (seq x n) (ℚ.- seq y n))))
                                               (ℚP.∣-p∣≡∣p∣ (seq x n ℚ.- seq y n)) ⟩
  ℚ.∣ seq x n ℚ.- seq y n ∣           ≤⟨ x₁ n ⟩
  + 2 / n                              ∎})
  where open ℚP.≤-Reasoning

*-zeroˡ : LeftZero _≃_ 0ℝ _*_
*-zeroˡ x = *≃* (λ { (suc k₁) -> let n = suc k₁; k = K 0ℝ ℕ.⊔ K x in begin
  ℚ.∣ 0ℚᵘ ℚ.* seq x (2 ℕ.* k ℕ.* n) ℚ.- 0ℚᵘ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- 0ℚᵘ) (ℚP.*-zeroˡ (seq x (2 ℕ.* k ℕ.* n)))) ⟩
  0ℚᵘ                                         ≤⟨ ℚ.*≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ n))) (ℤ.+≤+ ℕ.z≤n)) ⟩
  + 2 / n                                      ∎})
  where open ℚP.≤-Reasoning

*-zeroʳ : RightZero _≃_ 0ℝ _*_
*-zeroʳ x = ≃-trans (*-comm x 0ℝ) (*-zeroˡ x)

*-zero : Zero _≃_ 0ℝ _*_
*-zero = *-zeroˡ , *-zeroʳ

-- Algebraic structures
+-rawMagma : RawMagma 0ℓ 0ℓ
+-rawMagma = record
  { _≈_ = _≃_
  ; _∙_ = _+_
  }

+-rawMonoid : RawMonoid 0ℓ 0ℓ
+-rawMonoid = record
  { _≈_ = _≃_
  ; _∙_ = _+_
  ; ε   = 0ℝ
  }

+-0-rawGroup : RawGroup 0ℓ 0ℓ
+-0-rawGroup = record
  { Carrier = ℝ
  ; _≈_ = _≃_
  ; _∙_ = _+_
  ; ε = 0ℝ
  ; _⁻¹ = -_
  }

+-*-rawRing : RawRing 0ℓ 0ℓ
+-*-rawRing = record
  { Carrier = ℝ
  ; _≈_ = _≃_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = 0ℝ
  ; 1# = 1ℝ
  }

+-isMagma : IsMagma _≃_ _+_
+-isMagma = record
  { isEquivalence = ≃-isEquivalence
  ; ∙-cong = +-cong
  }


+-isSemigroup : IsSemigroup _≃_ _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc = +-assoc
  }

+-0-isMonoid : IsMonoid _≃_ _+_ 0ℝ
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity = +-identity
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _≃_ _+_ 0ℝ
+-0-isCommutativeMonoid = record
  { isMonoid = +-0-isMonoid
  ; comm     = +-comm
  }

+-0-isGroup : IsGroup _≃_ _+_ 0ℝ (-_)
+-0-isGroup = record
  { isMonoid = +-0-isMonoid
  ; inverse = +-inverse
  ; ⁻¹-cong = -‿cong
  }


+-0-isAbelianGroup : IsAbelianGroup _≃_ _+_ 0ℝ (-_)
+-0-isAbelianGroup = record
  { isGroup = +-0-isGroup
  ; comm    = +-comm
  }

+-magma : Magma 0ℓ 0ℓ
+-magma = record
  { isMagma = +-isMagma
  }

+-semigroup : Semigroup 0ℓ 0ℓ
+-semigroup = record
  { isSemigroup = +-isSemigroup
  }

+-0-monoid : Monoid 0ℓ 0ℓ
+-0-monoid = record
  { isMonoid = +-0-isMonoid
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { isCommutativeMonoid = +-0-isCommutativeMonoid
  }

+-0-group : Group 0ℓ 0ℓ
+-0-group = record
  { isGroup = +-0-isGroup
  }

+-0-abelianGroup : AbelianGroup 0ℓ 0ℓ
+-0-abelianGroup = record
  { isAbelianGroup = +-0-isAbelianGroup
  }

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record
  { _≈_ = _≃_
  ; _∙_ = _*_
  }

*-rawMonoid : RawMonoid 0ℓ 0ℓ
*-rawMonoid = record
  { _≈_ = _≃_
  ; _∙_ = _*_
  ; ε   = 1ℝ
  }

*-isMagma : IsMagma _≃_ _*_
*-isMagma = record
  { isEquivalence = ≃-isEquivalence
  ; ∙-cong = *-cong
  }


*-isSemigroup : IsSemigroup _≃_ _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = *-assoc
  }

*-1-isMonoid : IsMonoid _≃_ _*_ 1ℝ
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _≃_ _*_ 1ℝ
*-1-isCommutativeMonoid = record
  { isMonoid = *-1-isMonoid
  ; comm     = *-comm
  }


+-*-isRing : IsRing _≃_ _+_ _*_ -_ 0ℝ 1ℝ
+-*-isRing = record
  { +-isAbelianGroup = +-0-isAbelianGroup
  ; *-isMonoid       = *-1-isMonoid
  ; distrib          = *-distrib-+
  ; zero             = *-zero
  }

+-*-isCommutativeRing : IsCommutativeRing _≃_ _+_ _*_ -_ 0ℝ 1ℝ
+-*-isCommutativeRing = record
  { isRing = +-*-isRing
  ; *-comm = *-comm
  }

*-magma : Magma 0ℓ 0ℓ
*-magma = record
  { isMagma = *-isMagma
  }

*-semigroup : Semigroup 0ℓ 0ℓ
*-semigroup = record
  { isSemigroup = *-isSemigroup
  }

*-1-monoid : Monoid 0ℓ 0ℓ
*-1-monoid = record
  { isMonoid = *-1-isMonoid
  }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { isCommutativeMonoid = *-1-isCommutativeMonoid
  }

+-*-ring : Ring 0ℓ 0ℓ
+-*-ring = record
  { isRing = +-*-isRing
  }

+-*-commutativeRing : CommutativeRing 0ℓ 0ℓ
+-*-commutativeRing = record
  { isCommutativeRing = +-*-isCommutativeRing
  }

module ℝ-+-*-Solver =
  Solver +-*-rawRing (ACR.fromCommutativeRing +-*-commutativeRing) (ACR.-raw-almostCommutative⟶ (ACR.fromCommutativeRing +-*-commutativeRing)) (λ x y -> nothing)

{-
The ring solver for ℝ is very weak! It cannot even solve involution of negatives, while the solver for ℚ can.
-}
{-
testing : ∀ x -> - (- x) ≃ x
testing x = solve 1 (λ x -> :- (:- x) := x) {!≃-refl!} {!!}
  where
    open ℝ-+-*-Solver

test : ∀ p -> ℚ.- (ℚ.- p) ℚ.≃ p
test p = solve 1 (λ p -> :- (:- p) := p) ℚP.≃-refl p
  where
    open ℚ-Solver.+-*-Solver
-}

--Properties of -_
neg-involutive : Involutive _≃_ (-_)
neg-involutive x = *≃* λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.- (ℚ.- seq x n) ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseˡ (ℚ.- seq x n)) ⟩
  0ℚᵘ                                 ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                              ∎}
  where open ℚP.≤-Reasoning

neg-distrib-+ : ∀ x y -> - (x + y) ≃ (- x) + (- y)
neg-distrib-+ x y = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.- (seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)) ℚ.-
      (ℚ.- seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n)) ∣   ≈⟨ ℚP.∣-∣-cong (solve 2 (λ x y ->
                                                       :- (x :+ y) :- (:- x :- y) := con (0ℚᵘ)) ℚP.≃-refl
                                                       (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  0ℚᵘ                                               ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                            ∎})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver

--Properties of _⊔_

⊔-cong : Congruent₂ _≃_ _⊔_
⊔-cong {x} {z} {y} {w} (*≃* x≃z) (*≃* y≃w) = *≃* partA
  where
    partA : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ℚ.∣ seq (x ⊔ y) n ℚ.- seq (z ⊔ w) n ∣ ℚ.≤ (+ 2 / n) {n≢0}
    partA (suc k₁) = [ left , right ]′ (ℚP.≤-total (seq x n ℚ.⊔ seq y n) (seq z n ℚ.⊔ seq w n))
      where
        open ℚP.≤-Reasoning
        open ℚ-Solver.+-*-Solver
        n = suc k₁

        partB : ∀ a b c d -> a ℚ.≤ b -> ℚ.∣ b ℚ.- d ∣ ℚ.≤ + 2 / n ->
              (a ℚ.⊔ b) ℚ.- (c ℚ.⊔ d) ℚ.≤ + 2 / n
        partB a b c d a≤b hyp = begin
          (a ℚ.⊔ b) ℚ.- (c ℚ.⊔ d) ≤⟨ ℚP.+-mono-≤ (ℚP.≤-reflexive (ℚP.p≤q⇒p⊔q≃q a≤b)) (ℚP.neg-mono-≤ (ℚP.p≤q⊔p c d)) ⟩
          b ℚ.- d                 ≤⟨ p≤∣p∣ (b ℚ.- d) ⟩
          ℚ.∣ b ℚ.- d ∣           ≤⟨ hyp ⟩
          + 2 / n                  ∎

        left : seq x n ℚ.⊔ seq y n ℚ.≤ seq z n ℚ.⊔ seq w n -> ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
        left hyp1 = [ zn≤wn , wn≤zn ]′ (ℚP.≤-total (seq z n) (seq w n))
          where
            first : ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≃ (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n)
            first = begin-equality
              ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ ((seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n))))
                                                                                            (ℚP.∣-∣-cong (solve 2 (λ a b -> :- (a :- b) := b :- a)
                                                                                            ℚP.≃-refl (seq x n ℚ.⊔ seq y n) (seq z n ℚ.⊔ seq w n))) ⟩
              ℚ.∣ (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
              (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n)        ∎

            zn≤wn : seq z n ℚ.≤ seq w n -> ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
            zn≤wn hyp2 = begin
              ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ first ⟩
              (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n)       ≤⟨ partB (seq z n) (seq w n) (seq x n) (seq y n) hyp2
                                                                       (ℚP.≤-respˡ-≃ (∣p-q∣≃∣q-p∣ (seq y n) (seq w n)) (y≃w n)) ⟩
              + 2 / n                                            ∎

            wn≤zn : seq w n ℚ.≤ seq z n -> ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
            wn≤zn hyp2 = begin
              ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ first ⟩
              (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n)       ≈⟨ ℚP.+-cong (ℚP.⊔-comm (seq z n) (seq w n)) (ℚP.-‿cong (ℚP.⊔-comm (seq x n) (seq y n))) ⟩
              (seq w n ℚ.⊔ seq z n) ℚ.- (seq y n ℚ.⊔ seq x n)       ≤⟨ partB (seq w n) (seq z n) (seq y n) (seq x n) hyp2
                                                                       (ℚP.≤-respˡ-≃ (∣p-q∣≃∣q-p∣ (seq x n) (seq z n)) (x≃z n)) ⟩
              + 2 / n                                                ∎

        right : seq z n ℚ.⊔ seq w n ℚ.≤ seq x n ℚ.⊔ seq y n -> ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
        right hyp1 = [ xn≤yn , yn≤xn ]′ (ℚP.≤-total (seq x n) (seq y n))
          where
            xn≤yn : seq x n ℚ.≤ seq y n -> ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
            xn≤yn hyp2 = begin
              ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
              seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n)       ≤⟨ partB (seq x n) (seq y n) (seq z n) (seq w n) hyp2 (y≃w n) ⟩
              + 2 / n                                              ∎

            yn≤xn : seq y n ℚ.≤ seq x n -> ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
            yn≤xn hyp2 = begin
              ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
              seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n)       ≈⟨ ℚP.+-cong (ℚP.⊔-comm (seq x n) (seq y n)) (ℚP.-‿cong (ℚP.⊔-comm (seq z n) (seq w n))) ⟩
              seq y n ℚ.⊔ seq x n ℚ.- (seq w n ℚ.⊔ seq z n)       ≤⟨ partB (seq y n) (seq x n) (seq w n) (seq z n) hyp2 (x≃z n) ⟩
              + 2 / n                                              ∎
  
⊔-congˡ : LeftCongruent _≃_ _⊔_
⊔-congˡ y≃z = ⊔-cong ≃-refl y≃z

⊔-congʳ : RightCongruent _≃_ _⊔_
⊔-congʳ y≃z = ⊔-cong y≃z ≃-refl

⊔-comm : Commutative _≃_ _⊔_
⊔-comm x y = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq y n ℚ.⊔ seq x n) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (seq x n ℚ.⊔ seq y n) (ℚP.-‿cong (ℚP.⊔-comm (seq y n) (seq x n)))) ⟩
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n ℚ.⊔ seq y n)) ⟩
  0ℚᵘ                                                ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                              ∎})
  where open ℚP.≤-Reasoning

⊔-assoc : Associative _≃_ _⊔_
⊔-assoc x y z = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n ℚ.- (seq x n ℚ.⊔ (seq y n ℚ.⊔ seq z n)) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n)
                                                                                              (ℚP.-‿cong (ℚP.≃-sym (ℚP.⊔-assoc (seq x n) (seq y n) (seq z n))))) ⟩
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n ℚ.- (seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n) ∣   ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n)) ⟩
  0ℚᵘ                                                                          ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                                                       ∎})
  where open ℚP.≤-Reasoning

-- Properties of _⊓_
x⊓y≃x⊓₂y : ∀ x y -> x ⊓ y ≃ x ⊓₂ y
x⊓y≃x⊓₂y x y = *≃* (λ { (suc k₁) -> let n = suc k₁; xₙ = seq x n; yₙ = seq y n in begin
  ℚ.∣ xₙ ℚ.⊓ yₙ ℚ.- ℚ.- ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ)) ∣     ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (xₙ ℚ.⊓ yₙ)
                                                         (ℚP.-‿cong (ℚP.≃-trans (ℚP.neg-distrib-⊔-⊓ (ℚ.- xₙ) (ℚ.- yₙ))
                                                         (ℚP.⊓-cong (ℚP.neg-involutive xₙ) (ℚP.neg-involutive yₙ))))) ⟩
  ℚ.∣ xₙ ℚ.⊓ yₙ ℚ.- xₙ ℚ.⊓ yₙ ∣                       ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (xₙ ℚ.⊓ yₙ)) ⟩
  0ℚᵘ                                                ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                             ∎})
  where open ℚP.≤-Reasoning

⊓₂-cong : Congruent₂ _≃_ _⊓₂_
⊓₂-cong x≃y u≃v = -‿cong (⊔-cong (-‿cong x≃y) (-‿cong u≃v))

⊓₂-congˡ : LeftCongruent _≃_ _⊓₂_
⊓₂-congˡ y≃z = ⊓₂-cong ≃-refl y≃z

⊓₂-congʳ : RightCongruent _≃_ _⊓₂_
⊓₂-congʳ y≃z = ⊓₂-cong y≃z ≃-refl

⊓₂-comm : Commutative _≃_ _⊓₂_
⊓₂-comm x y = -‿cong (⊔-comm (- x) (- y))

⊓₂-assoc : Associative _≃_ _⊓₂_
⊓₂-assoc x y z = -‿cong (begin
  (- (- (- x ⊔ - y))) ⊔ (- z) ≈⟨ ⊔-congʳ (neg-involutive (- x ⊔ - y)) ⟩
  (- x ⊔ - y) ⊔ (- z)         ≈⟨ ⊔-assoc (- x) (- y) (- z) ⟩
  (- x) ⊔ (- y ⊔ - z)         ≈⟨ ⊔-congˡ (≃-symm (neg-involutive (- y ⊔ - z))) ⟩
  (- x) ⊔ (- (- (- y ⊔ - z)))                            ∎)
  where open ≃-Reasoning

⊓-cong : Congruent₂ _≃_ _⊓_
⊓-cong {x} {u} {y} {v} x≃u y≃v = begin
  x ⊓ y  ≈⟨ x⊓y≃x⊓₂y x y ⟩
  x ⊓₂ y ≈⟨ ⊓₂-cong x≃u y≃v ⟩
  u ⊓₂ v ≈⟨ ≃-symm (x⊓y≃x⊓₂y u v) ⟩
  u ⊓ v   ∎
  where open ≃-Reasoning

⊓-congˡ : LeftCongruent _≃_ _⊓_
⊓-congˡ y≃z = ⊓-cong ≃-refl y≃z

⊓-congʳ : RightCongruent _≃_ _⊓_
⊓-congʳ y≃z = ⊓-cong y≃z ≃-refl

⊓-comm : Commutative _≃_ _⊓_
⊓-comm x y = begin
  x ⊓ y  ≈⟨ x⊓y≃x⊓₂y x y ⟩
  x ⊓₂ y ≈⟨ ⊓₂-comm x y ⟩
  y ⊓₂ x ≈⟨ ≃-symm (x⊓y≃x⊓₂y y x) ⟩
  y ⊓ x   ∎
  where open ≃-Reasoning

⊓-assoc : Associative _≃_ _⊓_
⊓-assoc x y z = begin
  x ⊓ y ⊓ z     ≈⟨ ≃-trans (⊓-congʳ (x⊓y≃x⊓₂y x y)) (x⊓y≃x⊓₂y (x ⊓₂ y) z) ⟩
  x ⊓₂ y ⊓₂ z   ≈⟨ ⊓₂-assoc x y z ⟩
  x ⊓₂ (y ⊓₂ z) ≈⟨ ≃-trans (⊓₂-congˡ (≃-symm (x⊓y≃x⊓₂y y z))) (≃-symm (x⊓y≃x⊓₂y x (y ⊓ z))) ⟩
  x ⊓ (y ⊓ z)    ∎
  where open ≃-Reasoning

-- Alternative definition than Bishop's, but equivalent.
∣_∣ : ℝ -> ℝ
seq ∣ x ∣ n = ℚ.∣ seq x n ∣
reg ∣ x ∣ (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  ℚ.∣ ℚ.∣ seq x m ∣ ℚ.- ℚ.∣ seq x n ∣ ∣ ≤⟨ ∣∣p∣-∣q∣∣≤∣p-q∣ (seq x m) (seq x n) ⟩
  ℚ.∣ seq x m ℚ.- seq x n ∣            ≤⟨ reg x m n ⟩
  + 1 / m ℚ.+ + 1 / n                   ∎
  where open ℚP.≤-Reasoning

∣-∣-cong : Congruent₁ _≃_ ∣_∣
∣-∣-cong {x} {y} (*≃* x≃y) = *≃* (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- ℚ.∣ seq y n ∣ ∣ ≤⟨ ∣∣p∣-∣q∣∣≤∣p-q∣ (seq x n) (seq y n) ⟩
  ℚ.∣ seq x n ℚ.- seq y n ∣            ≤⟨ x≃y n ⟩
  + 2 / n                               ∎})
  where open ℚP.≤-Reasoning

∣x*y∣≃∣x∣*∣y∣ : ∀ x y -> ∣ x * y ∣ ≃ ∣ x ∣ * ∣ y ∣
∣x*y∣≃∣x∣*∣y∣ x y = *≃* (λ { (suc k₁) -> let n = suc k₁; r = K x ℕ.⊔ K y in begin
  ℚ.∣ ℚ.∣ seq (x * y) n ∣ ℚ.- seq (∣ x ∣ * ∣ y ∣) n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ ℚ.∣ seq (x * y) n ∣
                                                        (ℚP.-‿cong (ℚP.≃-sym (ℚP.∣p*q∣≃∣p∣*∣q∣ (seq x (2 ℕ.* r ℕ.* n)) (seq y (2 ℕ.* r ℕ.* n)))))) ⟩
  ℚ.∣ ℚ.∣ seq (x * y) n ∣ ℚ.- ℚ.∣ seq (x * y) n ∣ ∣   ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ ℚ.∣ seq (x * y) n ∣) ⟩
  0ℚᵘ                                                ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n ∎})
  where open ℚP.≤-Reasoning

-- Sign predicates
data Positive : Pred ℝ 0ℓ where
  pos* : ∀ {x} -> (∃ λ (n-1 : ℕ) -> seq x (suc n-1) ℚ.> + 1 / (suc n-1)) -> Positive x

data NonNegative : Pred ℝ 0ℓ where
  nonNeg* : ∀ {x} -> (∀ (n : ℕ) -> {n≢0 : n ≢0} -> seq x n ℚ.≥ ℚ.- ((+ 1 / n) {n≢0})) -> NonNegative x

-- Compare this to lemma2-8-1a in Reals.agda. This is much more readable and it's shorter!
lemma-2-8-1-if : ∀ {x} -> Positive x -> ∃ λ (N-1 : ℕ) -> ∀ (m : ℕ) -> m ℕ.≥ suc N-1 -> seq x m ℚ.≥ + 1 / (suc N-1)
lemma-2-8-1-if {x} (pos* (n-1 , posx)) = let n = suc n-1
                                                ; arch = archimedean-ℚ₂ (seq x n ℚ.- + 1 / n) (+ 2) (ℚ.positive (p<q⇒0<q-p (+ 1 / n) (seq x n) posx))
                                                ; N = suc (proj₁ arch) in ℕ.pred N , λ { (suc k₁) m≥N -> let m = suc k₁ in begin
  + 1 / N                               ≈⟨ ℚ.*≡* (solve 1 (λ N ->
                                           con (+ 1) :* (N :* N) := ((con (+ 2) :* N :- con (+ 1) :* N) :* N))
                                           _≡_.refl (+ N)) ⟩
  + 2 / N ℚ.- + 1 / N                   ≤⟨ ℚP.+-mono-≤ (ℚP.<⇒≤ (proj₂ arch)) (ℚP.neg-mono-≤ (q≤r⇒+p/r≤+p/q 1 N m m≥N)) ⟩
  seq x n ℚ.- + 1 / n ℚ.- + 1 / m       ≈⟨ ℚsolve 3 (λ xₙ n⁻¹ m⁻¹ -> xₙ -: n⁻¹ -: m⁻¹ =: xₙ -: (n⁻¹ +: m⁻¹)) ℚP.≃-refl (seq x n) (+ 1 / n) (+ 1 / m) ⟩
  seq x n ℚ.- (+ 1 / n ℚ.+ + 1 / m)     ≤⟨ ℚP.+-monoʳ-≤ (seq x n) (ℚP.neg-mono-≤ (reg x n m)) ⟩
  seq x n ℚ.- ℚ.∣ seq x n ℚ.- seq x m ∣ ≤⟨ ℚP.+-monoʳ-≤ (seq x n) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x n ℚ.- seq x m))) ⟩
  seq x n ℚ.- (seq x n ℚ.- seq x m)     ≈⟨ ℚsolve 2 (λ xₙ xₘ -> xₙ -: (xₙ -: xₘ) =: xₘ) ℚP.≃-refl (seq x n) (seq x m) ⟩
  seq x m  ∎}
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _+:_
        ; _:-_ to _-:_
        ; _:*_ to _*:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver

lemma-2-8-1-onlyif : ∀ {x : ℝ} -> (∃ λ (N-1 : ℕ) -> ∀ (m : ℕ) -> m ℕ.≥ suc N-1 -> seq x m ℚ.≥ + 1 / (suc N-1)) -> Positive x
lemma-2-8-1-onlyif {x} (N-1 , proof) = let N = suc N-1 in pos* (N , (begin-strict
  + 1 / (suc N) <⟨ ℚ.*<* (ℤP.*-monoˡ-<-pos 0 (ℤ.+<+ (ℕP.n<1+n N))) ⟩
  + 1 / N       ≤⟨ proof (suc N) (ℕP.n≤1+n N) ⟩
  seq x (suc N)  ∎))
  where open ℚP.≤-Reasoning

lemma-2-8-2-if : ∀ {x : ℝ} -> NonNegative x -> ∀ (n : ℕ) -> {n≢0 : n ≢0} ->
                 ∃ λ (Nₙ : ℕ) -> Nₙ ≢0 × (∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq x m ℚ.≥ ℚ.- (+ 1 / n) {n≢0})
lemma-2-8-2-if {x} (nonNeg* nonx) (suc k₁) = let n = suc k₁ in n , _ , λ {(suc k₂) m≥n -> let m = suc k₂ in begin
  ℚ.- (+ 1 / n) ≤⟨ ℚP.neg-mono-≤ (q≤r⇒+p/r≤+p/q 1 n m m≥n) ⟩
  ℚ.- (+ 1 / m) ≤⟨ nonx m ⟩
  seq x m        ∎}
  where open ℚP.≤-Reasoning

p-q≤j⁻¹⇒p≤q : ∀ {p q : ℚᵘ} ->
              (∀ (j : ℕ) -> {j≢0 : j ≢0} -> p ℚ.- q ℚ.≤ (+ 1 / j) {j≢0}) -> p ℚ.≤ q
p-q≤j⁻¹⇒p≤q {p} {q} hyp = ℚP.≮⇒≥ λ q<p -> let arch = archimedean-ℚ₂ (p ℚ.- q) (+ 1) (ℚ.positive (p<q⇒0<q-p q p q<p)); j = suc (proj₁ arch) in
                      ℚP.<⇒≱ (proj₂ arch) (hyp j)
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver

p-j⁻¹≤q⇒p≤q : ∀ {p q : ℚᵘ} -> (∀ (j : ℕ) -> {j≢0 : j ≢0} -> p ℚ.- (+ 1 / j) {j≢0} ℚ.≤ q) -> p ℚ.≤ q
p-j⁻¹≤q⇒p≤q {p} {q} hyp = p-q≤j⁻¹⇒p≤q λ { (suc k₁) -> let j = suc k₁ in begin
  p ℚ.- q                         ≈⟨ solve 3 (λ p q j⁻¹ ->
                                     p :- q := p :- j⁻¹ :- q :+ j⁻¹)
                                     ℚP.≃-refl p q (+ 1 / j) ⟩
  p ℚ.- + 1 / j ℚ.- q ℚ.+ + 1 / j ≤⟨ ℚP.+-monoˡ-≤ (+ 1 / j) (ℚP.+-monoˡ-≤ (ℚ.- q) (hyp j)) ⟩
  q ℚ.- q ℚ.+ + 1 / j             ≈⟨ solve 2 (λ q j⁻¹ -> q :- q :+ j⁻¹ := j⁻¹) ℚP.≃-refl q (+ 1 / j) ⟩
  + 1 / j  ∎}
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver

lemma-2-8-2-onlyif : ∀ {x : ℝ} -> (∀ (n : ℕ) -> {n≢0 : n ≢0} -> ∃ λ (Nₙ : ℕ) -> Nₙ ≢0 ×
                     (∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq x m ℚ.≥ ℚ.- (+ 1 / n) {n≢0})) -> NonNegative x
lemma-2-8-2-onlyif {x} hyp = nonNeg* (λ { (suc k₁) -> let n = suc k₁ in p-j⁻¹≤q⇒p≤q (λ { (suc k₂) ->
                           let j = suc k₂; N₂ⱼ = suc (proj₁ (hyp (2 ℕ.* j))); m = N₂ⱼ ℕ.⊔ (2 ℕ.* j) in begin
  ℚ.- (+ 1 / n) ℚ.- (+ 1 / j)                             ≈⟨ ℚP.+-congʳ (ℚ.- (+ 1 / n)) {ℚ.- (+ 1 / j)} {ℚ.- (+ 1 / (2 ℕ.* j) ℚ.+ + 1 / (2 ℕ.* j))}
                                                             (ℚP.-‿cong (ℚ.*≡* (solve 1 (λ j ->
                                                             con (+ 1) :* (con (+ 2) :* j :* (con (+ 2) :* j)) :=
                                                             (((con (+ 1) :* (con (+ 2) :* j) :+ con (+ 1) :* (con (+ 2) :* j)) :* j)))
                                                             _≡_.refl (+ j)))) ⟩
  ℚ.- (+ 1 / n) ℚ.- (+ 1 / (2 ℕ.* j) ℚ.+ + 1 / (2 ℕ.* j)) ≤⟨ ℚP.+-monoʳ-≤ (ℚ.- (+ 1 / n))
                                                             (ℚP.neg-mono-≤ (ℚP.+-monoˡ-≤ (+ 1 / (2 ℕ.* j))
                                                             (q≤r⇒+p/r≤+p/q 1 (2 ℕ.* j) m (ℕP.m≤n⊔m N₂ⱼ (2 ℕ.* j))))) ⟩
  ℚ.- (+ 1 / n) ℚ.- (+ 1 / m ℚ.+ + 1 / (2 ℕ.* j))         ≈⟨ ℚsolve 3 (λ n⁻¹ m⁻¹ k⁻¹ ->
                                                             -: n⁻¹ -: (m⁻¹ +: k⁻¹) =: -: k⁻¹ -: (m⁻¹ +: n⁻¹))
                                                             ℚP.≃-refl (+ 1 / n) (+ 1 / m) (+ 1 / (2 ℕ.* j)) ⟩
  ℚ.- (+ 1 / (2 ℕ.* j)) ℚ.- (+ 1 / m ℚ.+ + 1 / n)         ≤⟨ ℚP.+-mono-≤
                                                             (proj₂ (proj₂ (hyp (2 ℕ.* j))) m (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N₂ⱼ)) (ℕP.m≤m⊔n N₂ⱼ (2 ℕ.* j))))
                                                             (ℚP.neg-mono-≤ (reg x m n)) ⟩
  seq x m ℚ.- ℚ.∣ seq x m ℚ.- seq x n ∣                   ≤⟨ ℚP.+-monoʳ-≤ (seq x m) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x m ℚ.- seq x n))) ⟩
  seq x m ℚ.- (seq x m ℚ.- seq x n)                       ≈⟨ ℚsolve 2 (λ xₘ xₙ -> xₘ -: (xₘ -: xₙ) =: xₙ) ℚP.≃-refl (seq x m) (seq x n) ⟩
  seq x n                                                  ∎})})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _+:_
        ; _:-_ to _-:_
        ; _:*_ to _*:_
        ; :-_  to -:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver
  
pos-cong : ∀ {x y} -> x ≃ y -> Positive x -> Positive y
pos-cong {x} {y} x≃y posx = let fromPosx = lemma-2-8-1-if posx; N₁ = suc (proj₁ fromPosx); fromx≃y = equality-lemma-if x y x≃y (2 ℕ.* N₁)
                                     ; N₂ = suc (proj₁ fromx≃y); N = N₁ ℕ.⊔ N₂ in
                        lemma-2-8-1-onlyif {y} (ℕ.pred (2 ℕ.* N) , λ { (suc k₁) m≥2N -> let m = suc k₁ in begin
  + 1 / (2 ℕ.* N)                       ≤⟨ q≤r⇒+p/r≤+p/q 1 (2 ℕ.* N₁) (2 ℕ.* N) (ℕP.*-monoʳ-≤ 2 (ℕP.m≤m⊔n N₁ N₂)) ⟩
  + 1 / (2 ℕ.* N₁)                      ≈⟨ ℚ.*≡* (solve 1 (λ N₁ ->
                                           con (+ 1) :* (N₁ :* (con (+ 2) :* N₁)) :=
                                           (con (+ 1) :* (con (+ 2) :* N₁) :+ (:- con (+ 1)) :* N₁) :* (con (+ 2) :* N₁))
                                           _≡_.refl (+ N₁)) ⟩
  + 1 / N₁ ℚ.- + 1 / (2 ℕ.* N₁)         ≤⟨ ℚP.+-mono-≤
                                           (proj₂ fromPosx m (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.≤-trans (ℕP.m≤n*m N {2} ℕP.0<1+n) m≥2N)))
                                           (ℚP.neg-mono-≤ (proj₂ fromx≃y m
                                           (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N₂)) (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.≤-trans (ℕP.m≤n*m N {2} ℕP.0<1+n) m≥2N))))) ⟩
  seq x m ℚ.- ℚ.∣ seq x m ℚ.- seq y m ∣ ≤⟨ ℚP.+-monoʳ-≤ (seq x m) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x m ℚ.- seq y m))) ⟩
  seq x m ℚ.- (seq x m ℚ.- seq y m)     ≈⟨ ℚsolve 2 (λ xₘ yₘ -> xₘ -: (xₘ -: yₘ) =: yₘ) ℚP.≃-refl (seq x m) (seq y m) ⟩
  seq y m                                ∎})
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:-_ to _-:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver

pos⇒nonNeg : ∀ {x} -> Positive x -> NonNegative x
pos⇒nonNeg {x} posx = let fromPosx = lemma-2-8-1-if posx; N = suc (proj₁ fromPosx) in
                      lemma-2-8-2-onlyif (λ { (suc k₁) -> let n = suc k₁ in N , _ , λ { (suc k₂) m≥N -> let m = suc k₂ in
                      begin
  ℚ.- (+ 1 / n) <⟨ ℚP.negative⁻¹ _ ⟩
  0ℚᵘ           ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 1 / N       ≤⟨ proj₂ fromPosx m m≥N ⟩
  seq x m        ∎}})
  where open ℚP.≤-Reasoning

posx,y⇒posx+y : ∀ {x y} -> Positive x -> Positive y -> Positive (x + y)
posx,y⇒posx+y {x} {y} posx posy = let fromPosx = lemma-2-8-1-if posx; fromPosy = lemma-2-8-1-if posy
                                               ; N₁ = suc (proj₁ fromPosx); N₂ = suc (proj₁ fromPosy); N = N₁ ℕ.⊔ N₂ in
                                  lemma-2-8-1-onlyif (ℕ.pred N , λ { (suc k₁) m≥N -> let m = suc k₁ in begin
  + 1 / N                             ≤⟨ ℚP.p≤p+q {+ 1 / N} {+ 1 / N} _ ⟩
  + 1 / N ℚ.+ + 1 / N                 ≤⟨ ℚP.+-mono-≤
                                         (q≤r⇒+p/r≤+p/q 1 N₁ N (ℕP.m≤m⊔n N₁ N₂))
                                         (q≤r⇒+p/r≤+p/q 1 N₂ N (ℕP.m≤n⊔m N₁ N₂)) ⟩
  + 1 / N₁ ℚ.+ + 1 / N₂               ≤⟨ ℚP.+-mono-≤
                                         (proj₂ fromPosx (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) m≥N) (ℕP.m≤n*m m {2} ℕP.0<1+n)))
                                         (proj₂ fromPosy (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) m≥N) (ℕP.m≤n*m m {2} ℕP.0<1+n))) ⟩
  seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m)  ∎})
  where open ℚP.≤-Reasoning

nonNegx,y⇒nonNegx+y : ∀ {x y} -> NonNegative x -> NonNegative y -> NonNegative (x + y)
nonNegx,y⇒nonNegx+y {x} {y} nonx nony = lemma-2-8-2-onlyif (λ { (suc k₁) ->
                                        let n = suc k₁; fromNonx = lemma-2-8-2-if nonx (2 ℕ.* n); fromNony = lemma-2-8-2-if nony (2 ℕ.* n)
                                              ; Nx = proj₁ fromNonx; Ny = proj₁ fromNony; N = suc (Nx ℕ.⊔ Ny)
                                              ; Nx≤N = ℕP.≤-trans (ℕP.m≤m⊔n Nx Ny) (ℕP.n≤1+n (ℕ.pred N))
                                              ; Ny≤N = ℕP.≤-trans (ℕP.m≤n⊔m Nx Ny) (ℕP.n≤1+n (ℕ.pred N)) in
                                        N , _ , λ { (suc k₂) m≥N -> let m = suc k₂; m≤2m = ℕP.m≤n*m m {2} ℕP.0<1+n in begin
  ℚ.- (+ 1 / n)                               ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                 (:- con (+ 1)) :* (con (+ 2) :* n :* (con (+ 2) :* n)) :=
                                                 (((:- con (+ 1)) :* (con (+ 2) :* n) :+ ((:- con (+ 1)) :* (con (+ 2) :* n))) :* n))
                                                 _≡_.refl (+ n)) ⟩
  ℚ.- (+ 1 / (2 ℕ.* n)) ℚ.- (+ 1 / (2 ℕ.* n)) ≤⟨ ℚP.+-mono-≤
                                                 (proj₂ (proj₂ fromNonx) (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans Nx≤N m≥N) m≤2m))
                                                 (proj₂ (proj₂ fromNony) (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans Ny≤N m≥N) m≤2m)) ⟩
  seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m)          ∎}})
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver.+-*-Solver

nonNeg-cong : ∀ {x y} -> x ≃ y -> NonNegative x -> NonNegative y
nonNeg-cong {x} {y} x≃y nonx = lemma-2-8-2-onlyif λ { (suc k₁) ->
                               let n = suc k₁; fromNonx = lemma-2-8-2-if nonx (2 ℕ.* n); fromx≃y = equality-lemma-if x y x≃y (2 ℕ.* n)
                                      ; N₁ = proj₁ fromNonx; N₂ = proj₁ fromx≃y; N = suc (N₁ ℕ.⊔ N₂)
                                      ; N₁≤N = ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.n≤1+n (ℕ.pred N))
                                      ; N₂≤N = ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.n≤1+n (ℕ.pred N)) in
                               N , _ , λ { (suc k₂) m≥N -> let m = suc k₂ in begin
  ℚ.- (+ 1 / n)                               ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                 (:- con (+ 1)) :* (con (+ 2) :* n :* (con (+ 2) :* n)) :=
                                                 (((:- con (+ 1)) :* (con (+ 2) :* n) :+ ((:- con (+ 1)) :* (con (+ 2) :* n))) :* n))
                                                 _≡_.refl (+ n)) ⟩
  ℚ.- (+ 1 / (2 ℕ.* n)) ℚ.- (+ 1 / (2 ℕ.* n)) ≤⟨ ℚP.+-mono-≤
                                                 (proj₂ (proj₂ fromNonx) m (ℕP.≤-trans N₁≤N m≥N))
                                                 (ℚP.neg-mono-≤ (proj₂ fromx≃y m (ℕP.≤-trans N₂≤N m≥N))) ⟩
  seq x m ℚ.- ℚ.∣ seq x m ℚ.- seq y m ∣       ≤⟨ ℚP.+-monoʳ-≤ (seq x m) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x m ℚ.- seq y m))) ⟩
  seq x m ℚ.- (seq x m ℚ.- seq y m)           ≈⟨ ℚsolve 2 (λ x y -> x -: (x -: y) =: y) ℚP.≃-refl (seq x m) (seq y m) ⟩
  seq y m                                      ∎}}
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _+:_
        ; _:-_ to _-:_
        ; _:=_ to _=:_
        )
    open ℤ-Solver.+-*-Solver

posx∧nonNegy⇒posx+y : ∀ {x y} -> Positive x -> NonNegative y -> Positive (x + y)
posx∧nonNegy⇒posx+y {x} {y} posx nony = let fromPosx = lemma-2-8-1-if posx; N₁ = suc (proj₁ fromPosx)
                                                     ; fromNony = lemma-2-8-2-if nony (2 ℕ.* N₁)
                                                     ; N₂ = suc (proj₁ fromNony); N = 2 ℕ.* (N₁ ℕ.⊔ N₂)
                                                     ; N₁≤N = ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤n*m (N₁ ℕ.⊔ N₂) {2} ℕP.0<1+n)
                                                     ; N₂-1≤N = ℕP.≤-trans (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N₂)) (ℕP.m≤n⊔m N₁ N₂))
                                                                (ℕP.m≤n*m (N₁ ℕ.⊔ N₂) {2} ℕP.0<1+n) in
                                                     
                                        lemma-2-8-1-onlyif (ℕ.pred N , (λ { (suc k₁) m≥N -> let m = suc k₁ in begin
  + 1 / N                             ≤⟨ q≤r⇒+p/r≤+p/q 1 (2 ℕ.* N₁) N (ℕP.*-monoʳ-≤ 2 (ℕP.m≤m⊔n N₁ N₂)) ⟩
  + 1 / (2 ℕ.* N₁)                    ≈⟨ ℚ.*≡* (solve 1 (λ N₁ ->
                                         con (+ 1) :* (N₁ :* (con (+ 2) :* N₁)) :=
                                         (con (+ 1) :* (con (+ 2) :* N₁) :+ (:- con (+ 1)) :* N₁) :* (con (+ 2) :* N₁))
                                         _≡_.refl (+ N₁)) ⟩
  + 1 / N₁ ℚ.- + 1 / (2 ℕ.* N₁)       ≤⟨ ℚP.+-mono-≤
                                         (proj₂ fromPosx (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans N₁≤N m≥N) (ℕP.m≤n*m m {2} ℕP.0<1+n)))
                                         (proj₂ (proj₂ fromNony) (2 ℕ.* m) (ℕP.≤-trans (ℕP.≤-trans N₂-1≤N m≥N) (ℕP.m≤n*m m {2} ℕP.0<1+n))) ⟩
  seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m)  ∎}))
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver.+-*-Solver

nonNeg∣x∣ : ∀ x -> NonNegative ∣ x ∣
nonNeg∣x∣ x = nonNeg* (λ { (suc k₁) -> let n = suc k₁ in ℚP.≤-trans (ℚP.nonPositive⁻¹ _) (ℚP.0≤∣p∣ (seq x n))})

nonNegx⇒∣x∣≃x : ∀ {x} -> NonNegative x -> ∣ x ∣ ≃ x
nonNegx⇒∣x∣≃x {x} nonx = equality-lemma-onlyif ∣ x ∣ x partA
  where
    open ℚP.≤-Reasoning
    open ℤ-Solver.+-*-Solver
    partA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
            ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    partA (suc k₁) = N , partB
      where
        j = suc k₁
        fromNonx = lemma-2-8-2-if nonx (2 ℕ.* j)
        N = suc (proj₁ fromNonx)

        partB : ∀ (n : ℕ) -> n ℕ.≥ N -> ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣ ℚ.≤ + 1 / j
        partB (suc k₂) n≥N = [ left , right ]′ (ℚP.≤-total (seq x n) 0ℚᵘ)
          where
            n = suc k₂

            -xₙ≤1/2j = begin
              ℚ.- seq x n                 ≤⟨ ℚP.neg-mono-≤ (proj₂ (proj₂ fromNonx) n (ℕP.≤-trans (ℕP.n≤1+n (ℕ.pred N)) n≥N)) ⟩
              ℚ.- (ℚ.- (+ 1 / (2 ℕ.* j))) ≈⟨ ℚP.neg-involutive (+ 1 / (2 ℕ.* j)) ⟩
              + 1 / (2 ℕ.* j)              ∎

            left : seq x n ℚ.≤ 0ℚᵘ -> ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣ ℚ.≤ + 1 / j
            left hyp = begin
              ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣         ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p (p≤∣p∣ (seq x n))) ⟩
              ℚ.∣ seq x n ∣ ℚ.- seq x n               ≈⟨ ℚP.+-congˡ (ℚ.- seq x n) (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (seq x n))) ⟩
              ℚ.∣ ℚ.- seq x n ∣ ℚ.- seq x n           ≈⟨ ℚP.+-congˡ (ℚ.- seq x n) (ℚP.0≤p⇒∣p∣≃p (ℚP.neg-mono-≤ hyp)) ⟩
              ℚ.- seq x n ℚ.- seq x n                 ≤⟨ ℚP.+-mono-≤ -xₙ≤1/2j -xₙ≤1/2j ⟩
              (+ 1 / (2 ℕ.* j)) ℚ.+ (+ 1 / (2 ℕ.* j)) ≈⟨ ℚ.*≡* (solve 1 (λ j ->
                                                         (con (+ 1) :* (con (+ 2) :* j) :+ con (+ 1) :* (con (+ 2) :* j)) :* j :=
                                                         (con (+ 1) :* (con (+ 2) :* j :* (con (+ 2) :* j)))) _≡_.refl (+ j)) ⟩
              + 1 / j                                  ∎

            right : 0ℚᵘ ℚ.≤ seq x n -> ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣ ℚ.≤ + 1 / j
            right hyp = begin
              ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣  ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p (p≤∣p∣ (seq x n))) ⟩
              ℚ.∣ seq x n ∣ ℚ.- seq x n       ≈⟨ ℚP.+-congˡ (ℚ.- seq x n) (ℚP.0≤p⇒∣p∣≃p hyp) ⟩
              seq x n ℚ.- seq x n             ≈⟨ ℚP.+-inverseʳ (seq x n) ⟩
              0ℚᵘ                             ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
              + 1 / j                          ∎

nonNegx,y⇒nonNegx*y : ∀ {x y} -> NonNegative x -> NonNegative y -> NonNegative (x * y)
nonNegx,y⇒nonNegx*y {x} {y} nonx nony = nonNeg-cong lem (nonNeg∣x∣ (x * y))
  where
    open ≃-Reasoning
    lem : ∣ x * y ∣ ≃ x * y
    lem = begin
      ∣ x * y ∣     ≈⟨ ∣x*y∣≃∣x∣*∣y∣ x y ⟩
      ∣ x ∣ * ∣ y ∣ ≈⟨ *-cong (nonNegx⇒∣x∣≃x nonx) (nonNegx⇒∣x∣≃x nony) ⟩
      x * y          ∎

ℚ-*-mono-≤ : ∀ {p q r s} -> ℚ.NonNegative p -> ℚ.NonNegative r ->
             p ℚ.≤ q -> r ℚ.≤ s -> p ℚ.* r ℚ.≤ q ℚ.* s
ℚ-*-mono-≤ {p} {q} {r} {s} nonp nonr p≤q r≤s = begin
  p ℚ.* r ≤⟨ ℚP.*-monoˡ-≤-nonNeg nonr p≤q ⟩
  q ℚ.* r ≤⟨ ℚP.*-monoʳ-≤-nonNeg {q} (ℚ.nonNegative (ℚP.≤-trans (ℚP.nonNegative⁻¹ nonp) p≤q)) r≤s ⟩
  q ℚ.* s  ∎
  where open ℚP.≤-Reasoning

posx,y⇒posx*y : ∀ {x y} -> Positive x -> Positive y -> Positive (x * y)
posx,y⇒posx*y {x} {y} posx posy = let k = K x ℕ.⊔ K y; fromPosx = lemma-2-8-1-if posx; fromPosy = lemma-2-8-1-if posy
                                        ; N₁ = suc (proj₁ fromPosx); N₂ = suc (proj₁ fromPosy); N = N₁ ℕ.⊔ N₂
                                        ; N₁≤N² = ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤n*m N {N} ℕP.0<1+n)
                                        ; N₂≤N² = ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.m≤n*m N {N} ℕP.0<1+n) in
                                  lemma-2-8-1-onlyif (ℕ.pred (N ℕ.* N) , λ {(suc k₁) m≥N² ->
                                  let m = suc k₁; N²≤2km = ℕP.≤-trans m≥N² (ℕP.m≤n*m m {2 ℕ.* k} ℕP.0<1+n) in begin
  + 1 / N ℚ.* (+ 1 / N)                           ≤⟨ q≤r⇒+p/r≤+p/q 1 (N₁ ℕ.* N₂) (N ℕ.* N) (ℕP.*-mono-≤ (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤n⊔m N₁ N₂)) ⟩
  + 1 / N₁ ℚ.* (+ 1 / N₂)                         ≤⟨ ℚ-*-mono-≤ _ _
                                                     (proj₂ fromPosx (2 ℕ.* k ℕ.* m) (ℕP.≤-trans N₁≤N² N²≤2km))
                                                     (proj₂ fromPosy (2 ℕ.* k ℕ.* m) (ℕP.≤-trans N₂≤N² N²≤2km)) ⟩
  seq x (2 ℕ.* k ℕ.* m) ℚ.* seq y (2 ℕ.* k ℕ.* m)  ∎})
  where open ℚP.≤-Reasoning

posx⇒posx⊔y : ∀ {x y} -> Positive x -> Positive (x ⊔ y)
posx⇒posx⊔y {x} {y} posx = let fromPosx = lemma-2-8-1-if posx; N = suc (proj₁ fromPosx) in
                           lemma-2-8-1-onlyif (ℕ.pred N , λ {(suc k₁) m≥N -> let m = suc k₁ in begin
  + 1 / N             ≤⟨ proj₂ fromPosx m m≥N ⟩
  seq x m             ≤⟨ ℚP.p≤p⊔q (seq x m) (seq y m) ⟩
  seq x m ℚ.⊔ seq y m  ∎})
  where open ℚP.≤-Reasoning

nonNegx⇒nonNegx⊔y : ∀ {x y} -> NonNegative x -> NonNegative (x ⊔ y)
nonNegx⇒nonNegx⊔y {x} {y} nonx = lemma-2-8-2-onlyif (λ {(suc k₁) ->
                                 let n = suc k₁; fromNonx = lemma-2-8-2-if nonx n
                                        ; N = proj₁ fromNonx in
                                 N , proj₁ (proj₂ fromNonx) , λ m m≥N -> begin
  ℚ.- (+ 1 / n)       ≤⟨ proj₂ (proj₂ fromNonx) m m≥N ⟩
  seq x m             ≤⟨ ℚP.p≤p⊔q (seq x m) (seq y m) ⟩
  seq x m ℚ.⊔ seq y m  ∎})
  where open ℚP.≤-Reasoning

nonNegx,y⇒nonNegx⊓y : ∀ {x y} -> NonNegative x -> NonNegative y -> NonNegative (x ⊓ y)
nonNegx,y⇒nonNegx⊓y {x} {y} nonx nony = lemma-2-8-2-onlyif partA
  where
    open ℚP.≤-Reasoning
    partA : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ∃ λ (Nₙ : ℕ) -> Nₙ ≢0 ×
           (∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq (x ⊓ y) m ℚ.≥ ℚ.- (+ 1 / n) {n≢0})
    partA (suc k₁) = N , _ , partB
      where
        n = suc k₁
        fromNonx = lemma-2-8-2-if nonx n
        Nx = proj₁ fromNonx
        fromNony = lemma-2-8-2-if nony n
        Ny = proj₁ fromNony
        N = suc (Nx ℕ.⊔ Ny)
        Nx≤N = ℕP.≤-trans (ℕP.m≤m⊔n Nx Ny) (ℕP.n≤1+n (ℕ.pred N))
        Ny≤N = ℕP.≤-trans (ℕP.m≤n⊔m Nx Ny) (ℕP.n≤1+n (ℕ.pred N))

        partB : ∀ (m : ℕ) -> m ℕ.≥ N -> seq (x ⊓ y) m ℚ.≥ ℚ.- (+ 1 / n)
        partB m m≥N = [ left , right ]′ (ℚP.≤-total (seq x m) (seq y m))
          where
            left : seq x m ℚ.≤ seq y m -> seq (x ⊓ y) m ℚ.≥ ℚ.- (+ 1 / n)
            left hyp = begin
              ℚ.- (+ 1 / n)       ≤⟨ proj₂ (proj₂ fromNonx) m (ℕP.≤-trans Nx≤N m≥N) ⟩
              seq x m             ≈⟨ ℚP.≃-sym (ℚP.p≤q⇒p⊓q≃p hyp) ⟩
              seq x m ℚ.⊓ seq y m   ∎

            right : seq y m ℚ.≤ seq x m -> seq (x ⊓ y) m ℚ.≥ ℚ.- (+ 1 / n)
            right hyp = begin
              ℚ.- (+ 1 / n)       ≤⟨ proj₂ (proj₂ fromNony) m (ℕP.≤-trans Ny≤N m≥N) ⟩
                  seq y m             ≈⟨ ℚP.≃-sym (ℚP.p≥q⇒p⊓q≃q hyp) ⟩
              seq x m ℚ.⊓ seq y m  ∎

posx,y⇒posx⊓y : ∀ x y -> Positive x -> Positive y -> Positive (x ⊓ y)
posx,y⇒posx⊓y x y posx posy = lemma-2-8-1-onlyif (ℕ.pred N , lem)
  where
    open ℚP.≤-Reasoning
    fromPosx = lemma-2-8-1-if posx
    Nx = suc (proj₁ fromPosx)
    fromPosy = lemma-2-8-1-if posy
    Ny = suc (proj₁ fromPosy)
    N = Nx ℕ.⊔ Ny
    Nx≤N = ℕP.m≤m⊔n Nx Ny
    Ny≤N = ℕP.m≤n⊔m Nx Ny

    lem : ∀ (m : ℕ) -> m ℕ.≥ N -> seq (x ⊓ y) m ℚ.≥ + 1 / N
    lem m m≥N = [ left , right ]′ (ℚP.≤-total (seq x m) (seq y m))
      where
        left : seq x m ℚ.≤ seq y m -> seq (x ⊓ y) m ℚ.≥ + 1 / N
        left hyp = begin
          + 1 / N             ≤⟨ q≤r⇒+p/r≤+p/q 1 Nx N Nx≤N ⟩
          + 1 / Nx            ≤⟨ proj₂ fromPosx m (ℕP.≤-trans Nx≤N m≥N) ⟩
          seq x m             ≈⟨ ℚP.≃-sym (ℚP.p≤q⇒p⊓q≃p hyp) ⟩
          seq x m ℚ.⊓ seq y m   ∎

        right : seq y m ℚ.≤ seq x m -> seq (x ⊓ y) m ℚ.≥ + 1 / N
        right hyp = begin
          + 1 / N             ≤⟨ q≤r⇒+p/r≤+p/q 1 Ny N Ny≤N ⟩
          + 1 / Ny            ≤⟨ proj₂ fromPosy m (ℕP.≤-trans Ny≤N m≥N) ⟩
          seq y m             ≈⟨ ℚP.≃-sym (ℚP.p≥q⇒p⊓q≃q hyp) ⟩
          seq x m ℚ.⊓ seq y m   ∎

infix 4 _<_ _>_ _≤_ _≥_

_<_ : Rel ℝ 0ℓ
x < y = Positive (y - x)

_>_ : Rel ℝ 0ℓ
x > y = y < x

_≤_ : Rel ℝ 0ℓ
x ≤ y = NonNegative (y - x)

_≥_ : Rel ℝ 0ℓ
x ≥ y = y ≤ x

Negative : Pred ℝ 0ℓ
Negative x = Positive (- x)

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ {x} {y} x<y = pos⇒nonNeg x<y

-- Helper lemmas often used in the next few order property proofs
private
  z-y+y-x≃z-x : ∀ {x y z} -> (z - y) + (y - x) ≃ z - x
  z-y+y-x≃z-x {x} {y} {z} = begin
      (z - y) + (y - x)   ≈⟨ +-assoc z (- y) (y - x) ⟩
      z + (- y + (y - x)) ≈⟨ +-congʳ z (≃-symm (+-assoc (- y) y (- x))) ⟩
      z + ((- y + y) - x) ≈⟨ +-congʳ z (+-congˡ (- x) (+-inverseˡ y)) ⟩
      z + (0ℝ - x)        ≈⟨ +-congʳ z (+-identityˡ (- x)) ⟩
      z - x                ∎
    where open ≃-Reasoning

  z-x+t-y≃z+t-x+y : ∀ {x y z t} -> (z - x) + (t - y) ≃ (z + t) - (x + y)
  z-x+t-y≃z+t-x+y {x} {y} {z} {t} = begin
      (z - x) + (t - y)     ≈⟨ +-congʳ (z - x) (+-comm t (- y)) ⟩
      (z - x) + (- y + t)   ≈⟨ +-assoc z (- x) (- y + t) ⟩
      z + (- x + (- y + t)) ≈⟨ ≃-symm (+-congʳ z (+-assoc (- x) (- y) t)) ⟩
      z + ((- x + - y) + t) ≈⟨ +-congʳ z (+-comm (- x + - y) t) ⟩
      z + (t + (- x + - y)) ≈⟨ ≃-symm (+-assoc z t (- x + - y)) ⟩
      (z + t) + (- x + - y) ≈⟨ +-congʳ (z + t) (≃-symm (neg-distrib-+ x y)) ⟩
      (z + t) - (x + y)      ∎
    where open ≃-Reasoning

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans {x} {y} {z} x<y y≤z = pos-cong (≃-trans (+-comm (y - x) (z - y)) z-y+y-x≃z-x) (posx∧nonNegy⇒posx+y x<y y≤z)

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans {x} {y} {z} x≤y y<z = pos-cong z-y+y-x≃z-x (posx∧nonNegy⇒posx+y y<z x≤y)

<-trans : Transitive _<_
<-trans = ≤-<-trans ∘ <⇒≤

≤-trans : Transitive _≤_
≤-trans {x} {y} {z} x≤y y≤z = nonNeg-cong z-y+y-x≃z-x (nonNegx,y⇒nonNegx+y y≤z x≤y)

nonNeg0 : NonNegative 0ℝ
nonNeg0 = nonNeg* (λ {(suc k₁) -> ℚP.<⇒≤ (ℚP.negative⁻¹ _)})

nonNeg-refl : ∀ {x} -> NonNegative (x - x)
nonNeg-refl {x} = nonNeg-cong (≃-symm (+-inverseʳ x)) nonNeg0

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ x≤z y≤t = nonNeg-cong z-x+t-y≃z+t-x+y (nonNegx,y⇒nonNegx+y x≤z y≤t)

+-monoʳ-≤ : ∀ (x : ℝ) -> (_+_ x) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ x y≤z = +-mono-≤ nonNeg-refl y≤z

+-monoˡ-≤ : ∀ (x : ℝ) -> (_+ x) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ x y≤z = +-mono-≤ y≤z nonNeg-refl

+-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< x<z y<t = pos-cong z-x+t-y≃z+t-x+y (posx,y⇒posx+y x<z y<t)

neg-distribˡ-* : ∀ x y -> - (x * y) ≃ - x * y
neg-distribˡ-* x y = begin
  - (x * y)                       ≈⟨ ≃-trans 
                                     (≃-symm (+-identityʳ (- (x * y))))
                                     (+-congʳ (- (x * y)) (≃-symm (*-zeroˡ y))) ⟩
  - (x * y) + 0ℝ * y              ≈⟨ +-congʳ (- (x * y)) (*-congʳ (≃-symm (+-inverseʳ x))) ⟩
  - (x * y) + (x - x) * y         ≈⟨ +-congʳ (- (x * y)) (*-distribʳ-+ y x (- x)) ⟩
  - (x * y) + (x * y + (- x) * y) ≈⟨ ≃-symm (+-assoc (- (x * y)) (x * y) ((- x) * y)) ⟩
  - (x * y) + x * y + (- x) * y   ≈⟨ +-congˡ (- x * y) (+-inverseˡ (x * y)) ⟩
  0ℝ + (- x) * y                  ≈⟨ +-identityˡ ((- x) * y) ⟩
  (- x) * y                        ∎
  where
    open ≃-Reasoning

neg-distribʳ-* : ∀ x y -> - (x * y) ≃ x * (- y)
neg-distribʳ-* x y = begin
  - (x * y) ≈⟨ -‿cong (*-comm x y) ⟩
  - (y * x) ≈⟨ neg-distribˡ-* y x ⟩
  - y * x   ≈⟨ *-comm (- y) x ⟩
  x * (- y)  ∎
  where
    open ≃-Reasoning

≤-reflexive : _≃_ ⇒ _≤_
≤-reflexive {x} x≃y = nonNeg-cong (+-congˡ (- x) x≃y) nonNeg-refl

≤-refl : Reflexive _≤_
≤-refl = ≤-reflexive ≃-refl

≤-isPreorder : IsPreorder _≃_ _≤_
≤-isPreorder = record
  { isEquivalence = ≃-isEquivalence
  ; reflexive     = ≤-reflexive
  ; trans         = ≤-trans
  }

<-respʳ-≃ : _<_ Respectsʳ _≃_
<-respʳ-≃ y≃z x<y = <-≤-trans x<y (≤-reflexive y≃z)

<-respˡ-≃ : _<_ Respectsˡ _≃_
<-respˡ-≃ y≃z y<x = ≤-<-trans (≤-reflexive (≃-symm y≃z)) y<x

<-resp-≃ : _<_ Respects₂ _≃_
<-resp-≃ = <-respʳ-≃ , <-respˡ-≃

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    <-trans
    <-resp-≃
    <⇒≤
    <-≤-trans 
    ≤-<-trans
    public

*-monoʳ-≤-nonNeg : ∀ {x y z} -> x ≤ z -> NonNegative y -> x * y ≤ z * y
*-monoʳ-≤-nonNeg {x} {y} {z} x≤z nony = nonNeg-cong lem (nonNegx,y⇒nonNegx*y x≤z nony)
  where
    open ≃-Reasoning
    lem : (z - x) * y ≃ z * y - x * y
    lem = begin
      (z - x) * y        ≈⟨ *-distribʳ-+ y z (- x) ⟩
      z * y + (- x) * y  ≈⟨ +-congʳ (z * y) (≃-symm (neg-distribˡ-* x y)) ⟩
      z * y - x * y       ∎

*-monoˡ-≤-nonNeg : ∀ {x y z} -> x ≤ z -> NonNegative y -> y * x ≤ y * z
*-monoˡ-≤-nonNeg {x} {y} {z} x≤z nony = begin
  y * x ≈⟨ *-comm y x ⟩
  x * y ≤⟨ *-monoʳ-≤-nonNeg x≤z nony ⟩
  z * y ≈⟨ *-comm z y ⟩
  y * z  ∎
  where
    open ≤-Reasoning

*-monoʳ-<-pos : ∀ {y} -> Positive y -> (_*_ y) Preserves _<_ ⟶ _<_
*-monoʳ-<-pos {y} posy {x} {z} x<z = pos-cong lem (posx,y⇒posx*y posy x<z)
  where
    open ≃-Reasoning
    lem : y * (z - x) ≃ y * z - y * x
    lem = begin
      y * (z - x)       ≈⟨ *-distribˡ-+ y z (- x) ⟩
      y * z + y * (- x) ≈⟨ +-congʳ (y * z) (≃-symm (neg-distribʳ-* y x)) ⟩
      y * z - y * x      ∎

*-monoˡ-<-pos : ∀ {y} -> Positive y -> (_* y) Preserves _<_ ⟶ _<_
*-monoˡ-<-pos {y} posy {x} {z} x<z = begin-strict
  x * y ≈⟨ *-comm x y ⟩
  y * x <⟨ *-monoʳ-<-pos posy x<z ⟩
  y * z ≈⟨ *-comm y z ⟩
  z * y  ∎
  where
    open ≤-Reasoning

neg-mono-< : -_ Preserves _<_ ⟶ _>_
neg-mono-< {x} {y} x<y = pos-cong lem x<y
  where
    open ≃-Reasoning
    lem : y - x ≃ - x - (- y)
    lem = begin
      y - x       ≈⟨ +-congˡ (- x) (≃-symm (neg-involutive y)) ⟩
      - (- y) - x ≈⟨ +-comm (- (- y)) (- x) ⟩
      - x - (- y)  ∎

neg-mono-≤ : -_ Preserves _≤_ ⟶ _≥_
neg-mono-≤ {x} {y} x≤y = nonNeg-cong lem x≤y
  where
    open ≃-Reasoning
    lem : y - x ≃ - x - (- y)
    lem = begin
      y - x       ≈⟨ +-congˡ (- x) (≃-symm (neg-involutive y)) ⟩
      - (- y) - x ≈⟨ +-comm (- (- y)) (- x) ⟩
      - x - (- y)  ∎

x≤x⊔y : ∀ x y -> x ≤ x ⊔ y
x≤x⊔y x y = nonNeg* (λ {(suc k₁) -> let n = suc k₁ in begin (
  ℚ.- (+ 1 / n)                                           ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
  0ℚᵘ                                                     ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ (seq x (2 ℕ.* n))) ⟩
  seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)                     ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- seq x (2 ℕ.* n)) (ℚP.p≤p⊔q (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  seq x (2 ℕ.* n) ℚ.⊔ seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)  ∎)})
  where open ℚP.≤-Reasoning

x≤y⊔x : ∀ x y -> x ≤ y ⊔ x
x≤y⊔x x y = begin
  x     ≤⟨ x≤x⊔y x y ⟩
  x ⊔ y ≈⟨ ⊔-comm x y ⟩
  y ⊔ x  ∎
  where
    open ≤-Reasoning

x⊓y≤x : ∀ x y -> x ⊓ y ≤ x
x⊓y≤x x y = nonNeg* λ {(suc k₁) -> let n = suc k₁ in begin 
      ℚ.- (+ 1 / n)                             ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
      0ℚᵘ                                       ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ (seq x (2 ℕ.* n))) ⟩ 
      seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)       ≤⟨ ℚP.+-monoʳ-≤ (seq x (2 ℕ.* n)) (ℚP.neg-mono-≤ (ℚP.p⊓q≤p (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)))) ⟩
      seq x (2 ℕ.* n) ℚ.- seq (x ⊓ y) (2 ℕ.* n) ∎}
  where open ℚP.≤-Reasoning

x⊓y≤y : ∀ x y -> x ⊓ y ≤ y
x⊓y≤y x y = begin
  x ⊓ y ≈⟨ ⊓-comm x y ⟩
  y ⊓ x ≤⟨ x⊓y≤x y x ⟩
  y      ∎
  where
    open ≤-Reasoning

≤-antisym : Antisymmetric _≃_ _≤_
≤-antisym {x} {y} (nonNeg* x≤y) (nonNeg* y≤x) = ≃-symm partB
  where
    partA : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ℚ.∣ seq (x - y) n ℚ.- 0ℚᵘ ∣ ℚ.≤ (+ 2 / n) {n≢0}
    partA (suc k₁) = begin
      ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ℚ.- 0ℚᵘ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-identityʳ (seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n))) ⟩
      ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣         ≤⟨ [ left , right ]′ (ℚP.≤-total (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
      + 2 / n                                            ∎
      where
        open ℚP.≤-Reasoning
        open ℚ-Solver.+-*-Solver
        n = suc k₁

        left : seq x (2 ℕ.* n) ℚ.≤ seq y (2 ℕ.* n) -> ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ℚ.≤ + 2 / n
        left hyp = begin
          ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n))))
                                                       (ℚP.0≤p⇒∣p∣≃p (ℚP.neg-mono-≤ (ℚP.p≤q⇒p-q≤0 hyp))) ⟩
          ℚ.- (seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n)) ≤⟨ ℚP.≤-respʳ-≃ (ℚP.neg-involutive (+ 1 / n)) (ℚP.neg-mono-≤ (y≤x n)) ⟩
          + 1 / n                                   ≤⟨ p≤q⇒p/r≤q/r (+ 1) (+ 2) n (ℤ.+≤+ (ℕ.s≤s ℕ.z≤n)) ⟩
          + 2 / n                                    ∎

        right : seq y (2 ℕ.* n) ℚ.≤ seq x (2 ℕ.* n) -> ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ℚ.≤ + 2 / n
        right hyp = begin
          ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp) ⟩
          seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n)       ≈⟨ solve 2 (λ x y -> x :- y := :- (y :- x)) ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)) ⟩
          ℚ.- (seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)) ≤⟨ ℚP.≤-respʳ-≃ (ℚP.neg-involutive (+ 1 / n)) (ℚP.neg-mono-≤ (x≤y n)) ⟩
          + 1 / n                                   ≤⟨ p≤q⇒p/r≤q/r (+ 1) (+ 2) n (ℤ.+≤+ (ℕ.s≤s ℕ.z≤n)) ⟩
          + 2 / n                                    ∎

    partB : y ≃ x
    partB = begin
      y             ≈⟨ ≃-symm (+-identityʳ y) ⟩
      y + 0ℝ        ≈⟨ +-congʳ y (≃-symm (*≃* partA)) ⟩
      y + (x - y)   ≈⟨ +-congʳ y (+-comm x (- y)) ⟩
      y + (- y + x) ≈⟨ ≃-symm (+-assoc y (- y) x) ⟩
      y - y + x     ≈⟨ +-congˡ x (+-inverseʳ y) ⟩
      0ℝ + x        ≈⟨ +-identityˡ x ⟩
      x              ∎
      where open ≃-Reasoning

-- Strange new interaction: 0 = -0 is no longer provable by reflexivity.
0≃-0 : 0ℝ ≃ - 0ℝ
0≃-0 = ⋆-distrib-neg 0ℚᵘ

{-0test : 0ℝ ≃ - 0ℝ
0test = {!≃-refl!}
-}

private
  -- Helper for the next few proofs
  x-0≃x : ∀ {x} -> x - 0ℝ ≃ x
  x-0≃x {x} = ≃-trans (+-congʳ x (≃-symm 0≃-0)) (+-identityʳ x)

{- Some solver testing
  0≡-0 : 0ℝ ≡ - 0ℝ
  0≡-0 = {!!}

  testx-0≃x : ∀ {x} -> x - 0ℝ ≃ x
  testx-0≃x {x} rewrite (sym 0≡-0) = solve 1 (λ x -> x :+ con 0ℝ := x) {!!} {!!}
    where open ℝ-+-*-Solver-}

0<x⇒posx : ∀ {x} -> 0ℝ < x -> Positive x
0<x⇒posx {x} 0<x = pos-cong x-0≃x 0<x

posx⇒0<x : ∀ {x} -> Positive x -> 0ℝ < x
posx⇒0<x {x} posx = pos-cong (≃-symm x-0≃x) posx

0≤x⇒nonNegx : ∀ {x} -> 0ℝ ≤ x -> NonNegative x
0≤x⇒nonNegx {x} 0≤x = nonNeg-cong x-0≃x 0≤x

nonNegx⇒0≤x : ∀ {x} -> NonNegative x -> 0ℝ ≤ x
nonNegx⇒0≤x {x} nonx = nonNeg-cong (≃-symm x-0≃x) nonx

0≤∣x∣ : ∀ x -> 0ℝ ≤ ∣ x ∣
0≤∣x∣ x = nonNegx⇒0≤x (nonNeg∣x∣ x)

∣x+y∣≤∣x∣+∣y∣ : ∀ x y -> ∣ x + y ∣ ≤ ∣ x ∣ + ∣ y ∣
∣x+y∣≤∣x∣+∣y∣ x y = nonNeg* (λ {(suc k₁) ->
                  let n = suc k₁; ∣x₄ₙ∣ = ℚ.∣ seq x (2 ℕ.* (2 ℕ.* n)) ∣
                         ; ∣y₄ₙ∣ = ℚ.∣ seq y (2 ℕ.* (2 ℕ.* n)) ∣
                         ; ∣x₄ₙ+y₄ₙ∣ = ℚ.∣ seq x (2 ℕ.* (2 ℕ.* n)) ℚ.+ seq y (2 ℕ.* (2 ℕ.* n)) ∣ in begin
  ℚ.- (+ 1 / n)                        ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
  0ℚᵘ                                  ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ (∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣)) ⟩
  ∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣ ℚ.- (∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣) ≤⟨ ℚP.+-monoʳ-≤ (∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣)
                                          (ℚP.neg-mono-≤ (ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x (2 ℕ.* (2 ℕ.* n))) (seq y (2 ℕ.* (2 ℕ.* n))))) ⟩
  ∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣ ℚ.- ∣x₄ₙ+y₄ₙ∣          ∎})
  where open ℚP.≤-Reasoning

-- Should I use a constructor here too?
_≄_ : Rel ℝ 0ℓ
x ≄ y = x < y ⊎ y < x

_≄0 : ℝ -> Set
x ≄0 = x ≄ 0ℝ

x≤∣x∣ : ∀ {x} -> x ≤ ∣ x ∣
x≤∣x∣ {x} = nonNeg* (λ {(suc k₁) -> let n = suc k₁ in begin
  ℚ.- (+ 1 / n)                             ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
  0ℚᵘ                                       ≤⟨ ℚP.p≤q⇒0≤q-p (p≤∣p∣ (seq x (2 ℕ.* n))) ⟩
  ℚ.∣ seq x (2 ℕ.* n) ∣ ℚ.- seq x (2 ℕ.* n)  ∎})
  where open ℚP.≤-Reasoning

∣-x∣≃∣x∣ : ∀ {x} -> ∣ - x ∣ ≃ ∣ x ∣
∣-x∣≃∣x∣ {x} = *≃* λ {(suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.∣ ℚ.- seq x n ∣ ℚ.- ℚ.∣ seq x n ∣ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- ℚ.∣ seq x n ∣) (ℚP.∣-p∣≃∣p∣ (seq x n))) ⟩
  ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- ℚ.∣ seq x n ∣ ∣     ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ ℚ.∣ seq x n ∣) ⟩
  0ℚᵘ                                      ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                   ∎}
  where open ℚP.≤-Reasoning


_⁻¹ : (x : ℝ) -> {x ≄0} -> ℝ
seq ((x ⁻¹) {x≄0}) n = {!!}
reg ((x ⁻¹) {x≄0}) (suc k₁) (suc k₂) = {!!}
