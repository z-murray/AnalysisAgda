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
  *≃* : ∀ (x y : ℝ) -> (∀ (n : ℕ) -> {n≢0 : n ≢0} -> ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0}) -> x ≃ y

{-≃-refl : Reflexive _≃_
≃-refl {x} = *≃* x x lem
  where
    open ℚP.≤-Reasoning
    lem : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ℚ.∣ seq x n ℚ.- seq x n ∣ ℚ.≤ (+ 2 / n) {n≢0}
    lem (suc k₁) = begin
      ℚ.∣ seq x n ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n)) ⟩
      0ℚᵘ                       ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
      + 2 / n                    ∎
      where
        n : ℕ
        n = suc k₁-}

≃-refl : Reflexive _≃_
≃-refl {x} = *≃* x x λ { (suc k₁) → let n = suc k₁ in begin
  ℚ.∣ seq x n ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n)) ⟩
  0ℚᵘ                       ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                    ∎}
  where
    open ℚP.≤-Reasoning

∣p-q∣≃∣q-p∣ : ∀ p q -> ℚ.∣ p ℚ.- q ∣ ℚ.≃ ℚ.∣ q ℚ.- p ∣
∣p-q∣≃∣q-p∣ p q = begin-equality
  ℚ.∣ p ℚ.- q ∣       ≈⟨ ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (p ℚ.- q)) ⟩
  ℚ.∣ ℚ.- (p ℚ.- q) ∣ ≈⟨ ℚP.∣-∣-cong (solve 2 (λ p q -> :- (p :- q) := q :- p) ℚP.≃-refl p q) ⟩
  ℚ.∣ q ℚ.- p ∣        ∎
  where
    open ℚP.≤-Reasoning
    open ℚ-Solver.+-*-Solver

≃-symm : Symmetric _≃_
≃-symm {x} {y} (*≃* .x .y x₁) = *≃* y x (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ seq y n ℚ.- seq x n ∣ ≈⟨ ∣p-q∣≃∣q-p∣ (seq y n) (seq x n) ⟩
  ℚ.∣ seq x n ℚ.- seq y n ∣ ≤⟨ x₁ n ⟩
  + 2 / n                    ∎})
  where
    open ℚP.≤-Reasoning

m≤∣m∣ : ∀ m -> m ℤ.≤ + ℤ.∣ m ∣
m≤∣m∣ (+_ n) = ℤP.≤-refl
m≤∣m∣ (-[1+_] n) = ℤ.-≤+

archimedean-ℚ : ∀ p r -> ℚ.Positive p -> ∃ λ (N : ℕ) -> r ℚ.< ((+ N) ℤ.* ↥ p) / (↧ₙ p)
archimedean-ℚ (mkℚᵘ +[1+ g ] q-1) (mkℚᵘ u v-1) posp = let p = suc g; q = suc q-1; v = suc v-1; r = (u ℤ.* + q) modℕ (p ℕ.* v); t = (u ℤ.* + q) divℕ (p ℕ.* v) in
                                                      ℤ.∣ (+ 1) ℤ.+ t ∣ , ℚ.*<* (begin-strict
  u ℤ.* + q                           ≡⟨ a≡a%ℕn+[a/ℕn]*n (u ℤ.* + q) (p ℕ.* v) ⟩
  + r ℤ.+ t ℤ.* + (p ℕ.* v)           <⟨ ℤP.+-monoˡ-< (t ℤ.* + (p ℕ.* v)) (ℤ.+<+ (n%d<d (u ℤ.* + q) (+ p ℤ.* + v))) ⟩
  + (p ℕ.* v) ℤ.+ t ℤ.* + (p ℕ.* v)   ≡⟨ solve 2 (λ pv t ->
                                         pv :+ (t :* pv) := (con (+ 1) :+ t) :* pv)
                                         _≡_.refl (+ p ℤ.* + v) t ⟩
  (+ 1 ℤ.+ t) ℤ.* + (p ℕ.* v)         ≤⟨ ℤP.*-monoʳ-≤-nonNeg (p ℕ.* v) (m≤∣m∣ (+ 1 ℤ.+ t)) ⟩
  + ℤ.∣ + 1 ℤ.+ t ∣ ℤ.* (+ p ℤ.* + v) ≡⟨ sym (ℤP.*-assoc (+ ℤ.∣ + 1 ℤ.+ t ∣) (+ p) (+ v)) ⟩
  + ℤ.∣ + 1 ℤ.+ t ∣ ℤ.* + p ℤ.* + v    ∎)
  where
    open ℤP.≤-Reasoning
    open ℤ-Solver.+-*-Solver

archimedean-ℚ₂ : ∀ (p : ℚᵘ) -> ∀ (r : ℤ) -> ℚ.Positive p -> ∃ λ (N-1 : ℕ) -> r / (suc N-1) ℚ.< p
archimedean-ℚ₂ = {!!}

equality-lemma-if : ∀ x y -> x ≃ y -> ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
                  ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
                  ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 1 / j) {j≢0}
equality-lemma-if x y (*≃* .x .y x₁) (suc k₁) = let j = suc k₁ in 2 ℕ.* j , let N = 2 ℕ.* j in λ { (suc k₂) n≥N → let n = suc k₂ in begin
  ℚ.∣ seq x n ℚ.- seq y n ∣ ≤⟨ x₁ n ⟩
  + 2 / n                   ≤⟨ ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg 2 (ℤ.+≤+ n≥N)) ⟩
  + 2 / N                   ≈⟨ ℚ.*≡* (sym (ℤP.*-identityˡ (+ 2 ℤ.* + j))) ⟩
  + 1 / j                     ∎}
  where
    open ℚP.≤-Reasoning

0<p⇒Positivep-ℚ : ∀ p -> 0ℚᵘ ℚ.< p -> ℚ.Positive p
0<p⇒Positivep-ℚ p 0<p = {!!}

p<q⇒0<q-p : ∀ p q -> p ℚ.< q -> 0ℚᵘ ℚ.< q ℚ.- p
p<q⇒0<q-p p q p<q = begin-strict
  0ℚᵘ     ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ p) ⟩
  p ℚ.- p <⟨ ℚP.+-monoˡ-< (ℚ.- p) p<q ⟩
  q ℚ.- p  ∎
  where
    open ℚP.≤-Reasoning

equality-lemma-onlyif : ∀ x y ->
                        (∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> n ℕ.≥ N ->
                         ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 1 / j) {j≢0}) ->
                        x ≃ y
                        
equality-lemma-onlyif x y hyp1 = *≃* x y λ { n {n≢0} -> partA n {n≢0} (∣xₙ-yₙ∣≤2/n+3/j n {n≢0})}
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
      

    partA : ∀ (n : ℕ) -> {n≢0 : n ≢0} ->
            (∀ (j : ℕ) -> {j≢0 : j ≢0} ->
             ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0} ℚ.+ (+ 3 / j) {j≢0}) ->
            ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0}
    partA (suc k₂) hyp2 = let n = suc k₂ in
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

antidensity-ℤ : ¬(∃ λ (n : ℤ) -> + 0 ℤ.< n × n ℤ.< + 1)
antidensity-ℤ (.(+[1+ n ]) , ℤ.+<+ {n = suc n} m<n , ℤ.+<+ (ℕ.s≤s ()))

p≤∣p∣ : ∀ p -> p ℚ.≤ ℚ.∣ p ∣
p≤∣p∣ = {!!}

infixl 6 _+_ _-_ _⊔_ _⊓_
infixl 7 _*_
infix 8 -_ _⋆

_+_ : ℝ -> ℝ -> ℝ
seq (x + y) n = seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)
reg (x + y) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  ℚ.∣ seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m) ℚ.-
     (seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)) ∣    ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ xₘ yₘ xₙ yₙ ->
                                                   xₘ ℚ:+ yₘ ℚ:- (xₙ ℚ:+ yₙ) ℚ:= (xₘ ℚ:- xₙ ℚ:+ (yₘ ℚ:- yₙ)))
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
        ; _:+_ to _ℚ:+_
        ; _:-_ to _ℚ:-_
        ; _:=_ to _ℚ:=_
        )
    open ℤ-Solver.+-*-Solver

-_ : ℝ -> ℝ
seq (- x) n = ℚ.- seq x n
reg (- x) (suc k₁) (suc k₂) = let m = suc k₁; n = suc k₂ in begin
  ℚ.∣ ℚ.- seq x m ℚ.- ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.≃-sym (ℚP.≃-reflexive (ℚP.neg-distrib-+ (seq x m) (ℚ.- seq x n)))) ⟩
  ℚ.∣ ℚ.- (seq x m ℚ.- seq x n) ∣   ≤⟨ ℚP.≤-respˡ-≃ (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (seq x m ℚ.- seq x n))) (reg x m n) ⟩
  + 1 / m ℚ.+ + 1 / n                ∎
  where
    open ℚP.≤-Reasoning

_-_ : ℝ -> ℝ -> ℝ
x - y = x + (- y)

_⊔_ : ℝ -> ℝ -> ℝ
seq (x ⊔ y) n = (seq x n) ℚ.⊔ (seq y n)
reg (x ⊔ y) (suc k₁) (suc k₂) = [ left , right ]′ (ℚP.≤-total (seq x m ℚ.⊔ seq y m) (seq x n ℚ.⊔ seq y n))
  where
    open ℚP.≤-Reasoning
    open import Data.Rational.Unnormalised.Solver
    open +-*-Solver
    m : ℕ
    m = suc k₁

    n : ℕ
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

{-

-}
K : ℝ -> ℕ
K x = let p = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ); q = ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) in suc ℤ.∣ p divℕ q ∣

{-
Kx = suc ∣p div q∣ = 1 + ∣p div q∣
-}
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
      where
        open ℚP.≤-Reasoning

    right : ∀ (n : ℤ) -> ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< n / 1 -> + K x ℤ.≤ n
    right n hyp = let t = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) in begin
      + K x     ≡⟨ Kx=1+t x ⟩
      + 1 ℤ.+ t ≤⟨ proj₂ (proj₂ (least-ℤ>ℚ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))) n hyp ⟩
      n          ∎
      
      where
        open ℤP.≤-Reasoning

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
                                                  xm ℚ:* ym ℚ:- xn ℚ:* yn ℚ:=
                                                  xm ℚ:* (ym ℚ:- yn) ℚ:+ yn ℚ:* (xm ℚ:- xn))
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
        ; _:+_ to _ℚ:+_
        ; _:-_ to _ℚ:-_
        ; _:*_ to _ℚ:*_
        ; _:=_ to _ℚ:=_
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

+-cong : Congruent₂ _≃_ _+_
+-cong {x} {z} {y} {w} (*≃* .x .z x₁) (*≃* .y .w x₂) = *≃* (x + y) (z + w) (λ { (suc k₁) -> let n = suc k₁ in begin
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
+-congʳ x {y} {z} y≃z = +-cong {x} {x} {y} {z} ≃-refl y≃z

+-congˡ : ∀ x {y z} -> y ≃ z -> y + x ≃ z + x
+-congˡ x {y} {z} y≃z = +-cong {y} {z} {x} {x} y≃z ≃-refl

+-comm : Commutative _≃_ _+_
+-comm x y = *≃* (x + y) (y + x) (λ { (suc k₁) -> let n = suc k₁ in begin
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
+-assoc x y z = *≃* (x + y + z) (x + (y + z)) (λ { (suc k₁) -> let n = suc k₁; 2n = 2 ℕ.* n; 4n = 2 ℕ.* 2n in begin
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
+-identityˡ x = *≃* (0ℝ + x) x (λ { (suc k₁) -> let n = suc k₁ in begin
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
+-inverseʳ x = *≃* (x + - x) 0ℝ (λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ (seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)) ℚ.+ 0ℚᵘ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ 0ℚᵘ (ℚP.+-inverseʳ (seq x (2 ℕ.* n)))) ⟩
  0ℚᵘ                                                 ≤⟨ ℚ.*≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ n))) (ℤ.+≤+ ℕ.z≤n)) ⟩
  + 2 / n                                              ∎})
  where open ℚP.≤-Reasoning

+-inverseˡ : LeftInverse _≃_ 0ℝ -_ _+_
+-inverseˡ x = ≃-trans (+-comm (- x) x) (+-inverseʳ x)

+-inverse : Inverse _≃_ 0ℝ -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

⋆-distrib-+ : ∀ (p r : ℚᵘ) -> (p ℚ.+ r) ⋆ ≃ p ⋆ + r ⋆
⋆-distrib-+ x y = *≃* ((x ℚ.+ y) ⋆) (x ⋆ + y ⋆) (λ { (suc k₁) -> let n = suc k₁; p = ↥ x; q = ↧ₙ x; u = ↥ y; v = ↧ₙ y in begin
  ℚ.∣ ((p / q) ℚ.+ (u / v)) ℚ.- ((p / q) ℚ.+ (u / v)) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ ((p / q) ℚ.+ (u / v))) ⟩
  0ℚᵘ                                                   ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  (+ 2) / n                                              ∎})
  where open ℚP.≤-Reasoning

⋆-distrib-neg : ∀ (p : ℚᵘ) -> (ℚ.- p) ⋆ ≃ - (p ⋆)
⋆-distrib-neg p = *≃* ((ℚ.- p) ⋆) (- (p ⋆)) λ { (suc k₁) -> let n = suc k₁ in begin
  ℚ.∣ ℚ.- p ℚ.- (ℚ.- p) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (ℚ.- p)) ⟩
  0ℚᵘ                     ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  (+ 2) / n                ∎}
  where open ℚP.≤-Reasoning

q≤r⇒+p/r≤+p/q : ∀ p q r -> {q≢0 : q ≢0} -> {r≢0 : r ≢0} -> q ℕ.≤ r -> (+ p / r) {r≢0} ℚ.≤ (+ p / q) {q≢0}
q≤r⇒+p/r≤+p/q p (suc k₁) (suc k₂) q≤r = ℚ.*≤* (ℤP.*-monoˡ-≤-nonNeg p (ℤ.+≤+ q≤r))

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
        j r t N₁ N₂ N : ℕ
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
*-comm x y = *≃* (x * y) (y * x) λ { (suc k₁) -> let n = suc k₁ in begin
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
*-assoc = {!!}

*-distribˡ-+ : _DistributesOverˡ_ _≃_ _*_ _+_
*-distribˡ-+ = {!!}

*-distribʳ-+ : _DistributesOverʳ_ _≃_ _*_ _+_
*-distribʳ-+ = {!!}

*-distrib-+ : _DistributesOver_ _≃_ _*_ _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-identityˡ : LeftIdentity _≃_ 1ℝ _*_
*-identityˡ = {!!}

*-identityʳ : RightIdentity _≃_ 1ℝ _*_
*-identityʳ x = ≃-trans (*-comm x 1ℝ) (*-identityˡ x)

*-identity : Identity _≃_ 1ℝ _*_
*-identity = *-identityˡ , *-identityʳ

-‿cong : Congruent₁ _≃_ (-_)
-‿cong = {!!}

*-zeroˡ : LeftZero _≃_ 0ℝ _*_
*-zeroˡ = {!!}

*-zeroʳ : RightZero _≃_ 0ℝ _*_
*-zeroʳ x = ≃-trans (*-comm x 0ℝ) (*-zeroˡ x)

*-zero : Zero _≃_ 0ℝ _*_
*-zero = *-zeroˡ , *-zeroʳ

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

neg-involutive : Involutive _≃_ (-_)
neg-involutive = {!!}

{-
module ℝ-+-*-Solver =
  Solver +-*-rawRing (ACR.fromCommutativeRing +-*-commutativeRing) (ACR.-raw-almostCommutative⟶ (ACR.fromCommutativeRing +-*-commutativeRing)) (λ x y -> nothing)
-}

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


neg-distrib-+ : ∀ x y -> - (x + y) ≃ (- x) + (- y)
neg-distrib-+ = {!!}

⊔-cong : Congruent₂ _≃_ _⊔_
⊔-cong = {!!}

⊔-congˡ : LeftCongruent _≃_ _⊔_
⊔-congˡ = {!!}

⊔-congʳ : RightCongruent _≃_ _⊔_
⊔-congʳ = {!!}

⊔-comm : Commutative _≃_ _⊔_
⊔-comm = {!!}

⊔-assoc : Associative _≃_ _⊔_
⊔-assoc = {!!}

⊓-cong : Congruent₂ _≃_ _⊓_
⊓-cong = {!!}

⊓-congˡ : LeftCongruent _≃_ _⊓_
⊓-congˡ y≃z = ⊓-cong ≃-refl y≃z

⊓-congʳ : RightCongruent _≃_ _⊓_
⊓-congʳ y≃z = ⊓-cong y≃z ≃-refl

⊓-comm : Commutative _≃_ _⊓_
⊓-comm = {!!}

⊓-assoc : Associative _≃_ _⊓_
⊓-assoc = {!!}

-- Alternative definition than Bishop's, but equivalent.
∣_∣ : ℝ -> ℝ
seq ∣ x ∣ n = ℚ.∣ seq x n ∣
reg ∣ x ∣ (suc k₁) (suc k₂) = {!!}
