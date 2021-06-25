{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Bool.Base using (Bool; if_then_else_)
open import Function.Base using (_∘_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; +0; +[1+_]; -[1+_]; +<+; +≤+)
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
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong; sym; subst; trans; ≢-sym)
open import Relation.Binary
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; mkℚᵘ; _≢0; *≤*; _/_; 0ℚᵘ; ↥_; ↧_; ↧ₙ_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Algebra.Bundles
open import Algebra.Structures
open import Data.Empty
open import Data.Sum
open import Data.Maybe.Base
import Algebra.Solver.Ring as Solver
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR

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

_≃_ : Rel ℝ 0ℓ
x ≃ y = ∀ (n : ℕ) -> {n≢0 : n ≢0} ->
        ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ ((+ 2) / n) {n≢0}

≃-refl : Reflexive _≃_
≃-refl {x} (suc k) = begin
  ℚ.∣ seq x n ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n)) ⟩
  ℚ.∣ 0ℚᵘ ∣                 ≈⟨ ℚP.≃-refl ⟩
  0ℚᵘ                       ≤⟨ ℚP.∣p∣≃p⇒0≤p ℚP.≃-refl ⟩
  ((+ 2) / n)                ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k

≃-symm : Symmetric _≃_
≃-symm {x} {y} x≃y (suc k) = begin
  (ℚ.∣ seq y n ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.≃-trans (ℚP.≃-sym (ℚP.≃-reflexive (ℚP.∣-p∣≡∣p∣ (seq y n ℚ.- seq x n))))
                              (ℚP.∣-∣-cong (solve 2 (λ a b -> (:- (a :- b)) := b :- a) (ℚ.*≡* _≡_.refl) (seq y n) (seq x n)))) ⟩
  ℚ.∣ seq x n ℚ.- seq y n ∣ ≤⟨ x≃y n ⟩
  (+ 2) / n ∎)
  where
    open ℚP.≤-Reasoning
    open import Data.Rational.Unnormalised.Solver
    open +-*-Solver
    n : ℕ
    n = suc k

lemma1A : ∀ (x y : ℝ) -> x ≃ y -> ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
          ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> N ℕ.< n ->
          ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ ((+ 1) / j) {j≢0}
lemma1A x y x≃y (suc j) {j≢0} = 2 ℕ.* (suc j) ,
        λ { (suc n) N<n → ℚP.≤-trans (x≃y (suc n)) (*≤* (+≤+ (ℕP.<⇒≤ (subst (ℕ._<_ (2 ℕ.* (suc j))) (cong suc (sym (ℕP.+-identityʳ n))) N<n))))}

abstract
  no-0-divisors : ∀ (m n : ℕ) -> m ≢0 -> n ≢0 -> m ℕ.* n ≢0
  no-0-divisors (suc m) (suc n) m≢0 n≢0 with (suc m) ℕ.* (suc n) ℕ.≟ 0
  ...                                   | res = _

  m≤∣m∣ : ∀ (m : ℤ) -> m ℤ.≤ + ℤ.∣ m ∣
  m≤∣m∣ (+_ n) = ℤP.≤-reflexive _≡_.refl
  m≤∣m∣ (-[1+_] n) = ℤ.-≤+

  pos⇒≢0 : ∀ p → ℚ.Positive p → ℤ.∣ ↥ p ∣ ≢0
  pos⇒≢0 p p>0 = fromWitnessFalse (contraposition ℤP.∣n∣≡0⇒n≡0 (≢-sym (ℤP.<⇒≢ (ℤP.positive⁻¹ p>0))))

  0<⇒pos : ∀ p -> 0ℚᵘ ℚ.< p -> ℚ.Positive p
  0<⇒pos p p>0 = ℚ.positive p>0

archimedean-ℚ : ∀ (p r : ℚᵘ) -> ℚ.Positive p -> ∃ λ (N : ℕ) -> r ℚ.< ((+ N) ℤ.* (↥ p)) / (↧ₙ p)
archimedean-ℚ (mkℚᵘ (+ p) q-1) (mkℚᵘ u v-1) p/q>0 = ℤ.∣ (+ 1) ℤ.+ t ∣ , ℚ.*<* (begin-strict
   u ℤ.* (+ q)                                ≡⟨ a≡a%ℕn+[a/ℕn]*n (u ℤ.* (+ q)) (p ℕ.* v) ⟩
  (+ r) ℤ.+ (t ℤ.* (+ (p ℕ.* v)))             <⟨ ℤP.+-monoˡ-< (t ℤ.* (+ (p ℕ.* v))) (+<+ (n%d<d (u ℤ.* (+ q)) (+ (p ℕ.* v)))) ⟩
  (+ (p ℕ.* v)) ℤ.+ (t ℤ.* (+ (p ℕ.* v)))     ≡⟨ solve 2 (λ pv t ->
                                                     pv :+ (t :* pv) := (con (+ 1) :+ t) :* pv)
                                                     _≡_.refl (+ (p ℕ.* v)) t ⟩
  ((+ 1) ℤ.+ t) ℤ.* (+ (p ℕ.* v))             ≤⟨ ℤP.*-monoʳ-≤-nonNeg (p ℕ.* v) (m≤∣m∣ ((+ 1) ℤ.+ t)) ⟩
  (+ ℤ.∣ (+ 1) ℤ.+ t ∣) ℤ.* (+ (p ℕ.* v))     ≡⟨ cong (λ x -> (+ ℤ.∣ (+ 1) ℤ.+ t ∣) ℤ.* x) (sym (ℤP.pos-distrib-* p v)) ⟩
  (+ ℤ.∣ (+ 1) ℤ.+ t ∣) ℤ.* ((+ p) ℤ.* (+ v)) ≡⟨ sym (ℤP.*-assoc (+ ℤ.∣ (+ 1) ℤ.+ t ∣) (+ p) (+ v)) ⟩
  (+ ℤ.∣ (+ 1) ℤ.+ t ∣) ℤ.* + p ℤ.* + v        ∎)
  where
    open ℤP.≤-Reasoning
    open import Data.Integer.Solver
    open +-*-Solver
    q : ℕ
    q = suc q-1

    v : ℕ
    v = suc v-1

    p≢0 : p ≢0
    p≢0 = pos⇒≢0 ((+ p) / q) p/q>0

    pv≢0 : p ℕ.* v ≢0
    pv≢0 = no-0-divisors p v p≢0 _

    r : ℕ
    r = ((u ℤ.* (+ q)) modℕ (p ℕ.* v)) {pv≢0}

    t : ℤ
    t = ((u ℤ.* (+ q)) divℕ (p ℕ.* v)) {pv≢0}

alternate : ∀ (p : ℚᵘ) -> ∀ (N : ℕ) -> ((+ N) ℤ.* (↥ p)) / (↧ₙ p) ℚ.≃ ((+ N) / 1) ℚ.* p
alternate p N = ℚ.*≡* (cong (λ x -> ((+ N) ℤ.* (↥ p)) ℤ.* x) (ℤP.*-identityˡ (↧ p)))

get0ℚᵘ : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ((+ 0) / n) {n≢0} ℚ.≃ 0ℚᵘ
get0ℚᵘ (suc n) = ℚ.*≡* (trans (ℤP.*-zeroˡ (+ 1)) (sym (ℤP.*-zeroˡ (+ (suc n)))))

lemma1B : ∀ (x y : ℝ) -> (∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) ->
          ∀ (n : ℕ) -> N ℕ.< n ->
          ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ ((+ 1) / j) {j≢0}) -> x ≃ y
lemma1B x y hyp (suc k₁) = lemA lemB
  where
    n : ℕ
    n = suc k₁

    ∣xn-yn∣ : ℚᵘ
    ∣xn-yn∣ = ℚ.∣ seq x n ℚ.- seq y n ∣

    2/n : ℚᵘ
    2/n = (+ 2) / n
 
    lemA : (∀ (j : ℕ) -> {j≢0 : j ≢0} ->
          ∣xn-yn∣ ℚ.≤ 2/n ℚ.+ ((+ 3) / j) {j≢0}) ->
          ∣xn-yn∣ ℚ.≤ 2/n
    lemA hyp with ℚP.<-cmp ∣xn-yn∣ 2/n
    ... | tri< a ¬b ¬c = ℚP.<⇒≤ a
    ... | tri≈ ¬a b ¬c = ℚP.≤-reflexive b
    ... | tri> ¬a ¬b c with archimedean-ℚ (∣xn-yn∣ ℚ.- 2/n) ((+ 3) / 1) isPos
      where
        0<res : 0ℚᵘ ℚ.< ∣xn-yn∣ ℚ.- 2/n
        0<res = ℚP.<-respˡ-≃ (ℚP.+-inverseʳ 2/n) (ℚP.+-monoˡ-< (ℚ.- 2/n) c)

        isPos : ℚ.Positive (∣xn-yn∣ ℚ.- 2/n)
        isPos = ℚ.positive 0<res

    ... | 0 , 3<Nres = ⊥-elim (ℚP.<-asym 3<Nres (ℚP.<-respˡ-≃ (ℚP.≃-sym (get0ℚᵘ _)) (ℚP.positive⁻¹ {(+ 3) / 1} _)))
    ... | suc M , 3<Nres = ⊥-elim (ℚP.<-irrefl ℚP.≃-refl (ℚP.<-≤-trans part4 part5))
      where
        open ℚP.≤-Reasoning
        open import Data.Integer.Solver
        open +-*-Solver
        
        N : ℕ
        N = suc M

        part1 : (+ 3) / 1 ℚ.< ((+ N) / 1) ℚ.* (∣xn-yn∣ ℚ.- 2/n)
        part1 = ℚP.<-respʳ-≃ (alternate (∣xn-yn∣ ℚ.- 2/n) N) 3<Nres

        part2a : ((+ 1) / N) ℚ.* (((+ N) / 1) ℚ.* (∣xn-yn∣ ℚ.- 2/n)) ℚ.≃ ∣xn-yn∣ ℚ.- 2/n
        part2a = begin-equality
          ((+ 1) / N) ℚ.* (((+ N) / 1) ℚ.* (∣xn-yn∣ ℚ.- 2/n)) ≈⟨ ℚP.≃-sym (ℚP.*-assoc ((+ 1) / N) ((+ N) / 1) (∣xn-yn∣ ℚ.- 2/n)) ⟩
          ((+ 1) / N) ℚ.* ((+ N) / 1) ℚ.* (∣xn-yn∣ ℚ.- 2/n)   ≈⟨ ℚP.*-congʳ {∣xn-yn∣ ℚ.- 2/n} (ℚ.*≡* {((+ 1) / N) ℚ.* ((+ N) / 1)} {ℚ.1ℚᵘ}
                                                                 (solve 1 (λ N ->
                                                                      (con (+ 1) :* N) :* con (+ 1) := con (+ 1) :* (N :* con (+ 1)))
                                                                      _≡_.refl (+ N))) ⟩
          ℚ.1ℚᵘ ℚ.* (∣xn-yn∣ ℚ.- 2/n)                         ≈⟨ ℚP.*-identityˡ (∣xn-yn∣ ℚ.- 2/n) ⟩
          ∣xn-yn∣ ℚ.- 2/n                                      ∎

        part2 : ((+ 1) / N) ℚ.* ((+ 3) / 1) ℚ.< ∣xn-yn∣ ℚ.- 2/n
        part2 = ℚP.<-respʳ-≃ part2a (ℚP.*-monoʳ-<-pos {(+ 1) / N} _ part1)

        part3a : ((+ 1) / N) ℚ.* ((+ 3) / 1) ℚ.≃ (+ 3) / N
        part3a = ℚ.*≡* (trans (cong (λ x -> x ℤ.* (+ N)) (ℤP.*-identityˡ (+ 3))) (cong (λ x -> (+ 3) ℤ.* x) (sym (ℤP.*-identityʳ (+ N)))))
  
        part3 : (+ 3) / N ℚ.< ∣xn-yn∣ ℚ.- 2/n
        part3 = ℚP.<-respˡ-≃ part3a part2

        part4 : 2/n ℚ.+ ((+ 3) / N) ℚ.< ∣xn-yn∣
        part4 = ℚP.<-respˡ-≃ (ℚP.+-comm ((+ 3) / N) 2/n) (ℚP.<-respʳ-≃ (ℚP.≃-trans (ℚP.+-congʳ ∣xn-yn∣ (ℚP.+-inverseʳ 2/n)) (ℚP.+-identityʳ ∣xn-yn∣))
                (ℚP.<-respʳ-≃ (ℚP.+-assoc ∣xn-yn∣ (ℚ.- 2/n) 2/n) (ℚP.+-monoˡ-< 2/n part3)))

        part5 : ∣xn-yn∣ ℚ.≤ 2/n ℚ.+ ((+ 3) / N)
        part5 = hyp N

    
    lemB : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∣xn-yn∣ ℚ.≤ 2/n ℚ.+ ((+ 3) / j) {j≢0}
    lemB (suc k₂) with hyp (suc k₂)
    ...           | N , proof = begin
      ∣xn-yn∣                                                                                ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ xn yn xm ym ->
                                                                                                                  xn ℚ:- yn ℚ:= (xn ℚ:- xm) ℚ:+ (xm ℚ:- ym) ℚ:+ (ym ℚ:- yn))
                                                                                                                  (ℚ.*≡* _≡_.refl) (seq x n) (seq y n) (seq x m) (seq y m)) ⟩
      ℚ.∣ (seq x n ℚ.- seq x m) ℚ.+ (seq x m ℚ.- seq y m) ℚ.+ (seq y m ℚ.- seq y n) ∣        ≤⟨ ℚP.≤-trans (ℚP.∣p+q∣≤∣p∣+∣q∣
                                                                                                ((seq x n ℚ.- seq x m) ℚ.+ (seq x m ℚ.- seq y m)) (seq y m ℚ.- seq y n))
                                                                                                (ℚP.+-monoˡ-≤ ℚ.∣ seq y m ℚ.- seq y n ∣
                                                                                                (ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x n ℚ.- seq x m) (seq x m ℚ.- seq y m))) ⟩
      ℚ.∣ seq x n ℚ.- seq x m ∣ ℚ.+ ℚ.∣ seq x m ℚ.- seq y m ∣ ℚ.+ ℚ.∣ seq y m ℚ.- seq y n ∣   ≤⟨ ℚP.+-monoʳ-≤ (ℚ.∣ seq x n ℚ.- seq x m ∣ ℚ.+ ℚ.∣ seq x m ℚ.- seq y m ∣)
                                                                                                (reg y m n) ⟩
      ℚ.∣ seq x n ℚ.- seq x m ∣ ℚ.+ ℚ.∣ seq x m ℚ.- seq y m ∣ ℚ.+ (((+ 1) / m) ℚ.+ (+ 1) / n) ≤⟨ ℚP.+-monoˡ-≤ (((+ 1) / m) ℚ.+ (+ 1) / n)
                                                                                                (ℚP.+-monoʳ-≤ ℚ.∣ seq x n ℚ.- seq x m ∣ (proof m (ℕP.m≤m⊔n (suc N) j))) ⟩
      ℚ.∣ seq x n ℚ.- seq x m ∣ ℚ.+ ((+ 1) / j) ℚ.+ (((+ 1) / m) ℚ.+ ((+ 1) / n))             ≤⟨ ℚP.+-monoˡ-≤ (((+ 1) / m) ℚ.+ (+ 1) / n)
                                                                                                 (ℚP.+-monoˡ-≤ ((+ 1) / j) (reg x n m)) ⟩
      (((+ 1) / n) ℚ.+ (+ 1) / m) ℚ.+ ((+ 1) / j) ℚ.+ (((+ 1) / m) ℚ.+ ((+ 1) / n))           ≤⟨ ℚP.+-monoˡ-≤ ((((+ 1) / m) ℚ.+ ((+ 1) / n)))
                                                                                                 (ℚP.+-monoˡ-≤ ((+ 1) / j)
                                                                                                 (ℚP.+-monoʳ-≤ ((+ 1) / n) 1/m≤1/j)) ⟩
      (((+ 1) / n) ℚ.+ (+ 1) / j) ℚ.+ ((+ 1) / j) ℚ.+ (((+ 1) / m) ℚ.+ ((+ 1) / n))           ≤⟨ ℚP.+-monoʳ-≤ ((((+ 1) / n) ℚ.+ (+ 1) / j) ℚ.+ ((+ 1) / j))
                                                                                                 (ℚP.+-monoˡ-≤ ((+ 1) / n) 1/m≤1/j) ⟩
      (((+ 1) / n) ℚ.+ (+ 1) / j) ℚ.+ ((+ 1) / j) ℚ.+ (((+ 1) / j) ℚ.+ (+ 1) / n)             ≈⟨ ℚ.*≡* (solve 2 (λ n j ->

      {- Function for the solver -}
      (((((con (+ 1) :* j :+ con (+ 1) :* n) :* j) :+ con (+ 1) :* (n :* j)) :* (j :* n)) :+ ((con (+ 1) :* n :+ con (+ 1) :* j) :* ((n :* j) :* j))) :* (n :* j) :=
      ((con (+ 2) :* j :+ con (+ 3) :* n) :* (((n :* j) :* j) :* (j :* n)))) _≡_.refl (+ n) (+ j)) ⟩

      ((+ 2) / n) ℚ.+ ((+ 3) / j)                                                              ∎
      where
        open ℚP.≤-Reasoning
        open import Data.Rational.Unnormalised.Solver as ℚ-Solver
        open ℚ-Solver.+-*-Solver using ()
          renaming
            ( solve to ℚsolve
            ; _:+_ to _ℚ:+_
            ; _:-_ to _ℚ:-_
            ; _:=_ to _ℚ:=_
            )
        open import Data.Integer.Solver as ℤ-Solver
        open ℤ-Solver.+-*-Solver
        j : ℕ
        j = suc k₂

        m : ℕ
        m = (suc N) ℕ.⊔ j

        1/m≤1/j : ((+ 1) / m) ℚ.≤ (+ 1) / j
        1/m≤1/j = *≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-identityˡ (+ j)))
                      (ℤP.≤-trans (+≤+ (ℕP.m≤n⊔m (suc N) j))
                      (ℤP.≤-reflexive (sym (ℤP.*-identityˡ (+ m))))))

≃-trans : Transitive _≃_
≃-trans {x} {y} {z} x≃y y≃z = lemma1B x z lem
  where
    lem : ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
          ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> N ℕ.< n ->
          ℚ.∣ seq x n ℚ.- seq z n ∣ ℚ.≤ ((+ 1) / j) {j≢0}
    lem (suc k₁) with (lemma1A x y x≃y (2 ℕ.* (suc k₁))) | (lemma1A y z y≃z (2 ℕ.* (suc k₁)))
    lem (suc k₁) | N₁ , xy | N₂ , yz = N , λ {n N<n -> begin
      ℚ.∣ seq x n ℚ.- seq z n ∣                               ≈⟨ ℚP.∣-∣-cong (ℚsolve 3 (λ x y z ->
                                                                                  x ℚ:- z ℚ:= (x ℚ:- y) ℚ:+ (y ℚ:- z)) (ℚ.*≡* _≡_.refl) (seq x n) (seq y n) (seq z n)) ⟩
      ℚ.∣ (seq x n ℚ.- seq y n) ℚ.+ (seq y n ℚ.- seq z n) ∣   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x n ℚ.- seq y n) (seq y n ℚ.- seq z n) ⟩
      ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.+ ℚ.∣ seq y n ℚ.- seq z n ∣ ≤⟨ ℚP.≤-trans (ℚP.+-monoˡ-≤ ℚ.∣ seq y n ℚ.- seq z n ∣ (xy n (ℕP.m⊔n≤o⇒m≤o (suc N₁) (suc N₂) N<n)))
                                                                (ℚP.+-monoʳ-≤ ((+ 1) / (2 ℕ.* j)) (yz n (ℕP.m⊔n≤o⇒n≤o (suc N₁) (suc N₂) N<n))) ⟩
      ((+ 1) / (2 ℕ.* j)) ℚ.+ ((+ 1) / (2 ℕ.* j))            ≈⟨ ℚ.*≡* (solve 1 (λ j ->
                                                                           (con (+ 1) :* (con (+ 2) :* j) :+ (con (+ 1) :* (con (+ 2) :* j))) :* j :=
                                                                           (con (+ 1) :* ((con (+ 2) :* j) :* (con (+ 2) :* j)))) _≡_.refl (+ j)) ⟩
      (+ 1) / j                                               ∎}
      where
        open ℚP.≤-Reasoning
        open import Data.Rational.Unnormalised.Solver as ℚ-Solver
        open ℚ-Solver.+-*-Solver using ()
          renaming
            ( solve to ℚsolve
            ; _:+_ to _ℚ:+_
            ; _:=_ to _ℚ:=_
            ; _:*_ to _ℚ:*_
            ; _:-_ to _ℚ:-_
            )
        open import Data.Integer.Solver as ℤ-Solver
        open ℤ-Solver.+-*-Solver
        N : ℕ
        N = N₁ ℕ.⊔ N₂
        
        j : ℕ
        j = suc k₁
        
antidensity-ℤ : ¬(∃ λ (n : ℤ) -> + 0 ℤ.< n × n ℤ.< + 1)
antidensity-ℤ (+[1+ n ] , +<+ m<n , +<+ (ℕ.s≤s ()))

  
infixl 6 _+_ _-_ _⊔_ _⊓_
infixl 7 _*_
infix 8 -_ _⋆

_+_ : ℝ -> ℝ -> ℝ
seq (x + y) n = seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)
reg (x + y) (suc k₁) (suc k₂) = begin
  ℚ.∣ (seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m))
  ℚ.- (seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)) ∣                             ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ xm ym xn yn ->
                                                                                               (xm ℚ:+ ym) ℚ:- (xn ℚ:+ yn) ℚ:=
                                                                                               (xm ℚ:- xn) ℚ:+ (ym ℚ:- yn))
                                                                                               (ℚ.*≡* _≡_.refl)
                                                                                               (seq x (2 ℕ.* m)) (seq y (2 ℕ.* m))
                                                                                               (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  ℚ.∣ (seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n))
  ℚ.+ (seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n)) ∣                             ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n))
                                                                                             (seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n)) ⟩
  ℚ.∣ seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n) ∣
  ℚ.+ ℚ.∣ seq y (2 ℕ.* m) ℚ.- seq y (2 ℕ.* n)∣                            ≤⟨ ℚP.≤-trans (ℚP.+-monoʳ-≤ ℚ.∣ seq x (2 ℕ.* m) ℚ.- seq x (2 ℕ.* n) ∣
                                                                                     (reg y (2 ℕ.* m) (2 ℕ.* n)))
                                                                                   (ℚP.+-monoˡ-≤ (((+ 1) / (2 ℕ.* m)) ℚ.+ ((+ 1) / (2 ℕ.* n)))
                                                                                     (reg x (2 ℕ.* m) (2 ℕ.* n))) ⟩
  (((+ 1) / (2 ℕ.* m)) ℚ.+ ((+ 1) / (2 ℕ.* n))) ℚ.+ (((+ 1) / (2 ℕ.* m))
    ℚ.+ ((+ 1) / (2 ℕ.* n)))                                             ≈⟨ ℚ.*≡* (solve 2 (λ m n ->
                                                                                       (((con (+ 1) :* (con (+ 2) :* n) :+ con (+ 1) :* (con (+ 2) :* m))
                                                                                       :* ((con (+ 2) :* m) :* (con (+ 2) :* n))) :+
                                                                                       (con (+ 1) :* (con (+ 2) :* n) :+ con (+ 1) :* (con (+ 2) :* m))
                                                                                       :* ((con (+ 2) :* m) :* (con (+ 2) :* n))) :* (m :* n) :=
                                                                                       (con (+ 1) :* n :+ con (+ 1) :* m) :*
                                                                                       (((con (+ 2) :* m) :* (con (+ 2) :* n)) :*
                                                                                       (((con (+ 2) :* m) :* (con (+ 2) :* n)))))
                                                                                       _≡_.refl (+ m) (+ n)) ⟩
  ((+ 1) / m) ℚ.+ ((+ 1) / n)                                             ∎
  where
    open ℚP.≤-Reasoning
    open import Data.Rational.Unnormalised.Solver as ℚ-Solver
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _ℚ:+_
        ; _:-_ to _ℚ:-_
        ; _:=_ to _ℚ:=_
        )
    open import Data.Integer.Solver as ℤ-Solver
    open ℤ-Solver.+-*-Solver
    m : ℕ
    m = suc k₁

    n : ℕ
    n = suc k₂

2ℚᵘ : ℚᵘ
2ℚᵘ = (+ 2) / 1

least-ℤ>ℚ : ℚᵘ -> ℤ
least-ℤ>ℚ p = + 1 ℤ.+ (↥ p divℕ ↧ₙ p)

abstract
  least-ℤ>ℚ-greater : ∀ (p : ℚᵘ) -> p ℚ.< least-ℤ>ℚ p / 1
  least-ℤ>ℚ-greater (mkℚᵘ p q-1) = ℚ.*<* (begin-strict
    p ℤ.* (+ 1)           ≡⟨ trans (ℤP.*-identityʳ p) (a≡a%ℕn+[a/ℕn]*n p q) ⟩
    (+ r) ℤ.+ t ℤ.* (+ q) <⟨ ℤP.+-monoˡ-< (t ℤ.* (+ q)) (+<+ (n%ℕd<d p q)) ⟩
    (+ q) ℤ.+ t ℤ.* (+ q) ≡⟨ solve 2 (λ q t -> q :+ t :* q := (con (+ 1) :+ t) :* q) _≡_.refl (+ q) t ⟩
    (+ 1 ℤ.+ t) ℤ.* (+ q)  ∎)
    where
      open ℤP.≤-Reasoning
      open import Data.Integer.Solver
      open +-*-Solver
      q : ℕ
      q = suc q-1

      t : ℤ
      t = p divℕ q

      r : ℕ
      r = p modℕ q

  least-ℤ>ℚ-least : ∀ (p : ℚᵘ) -> ∀ (n : ℤ) -> p ℚ.< n / 1 -> least-ℤ>ℚ p ℤ.≤ n
  least-ℤ>ℚ-least (mkℚᵘ p q-1) n p/q<n with (least-ℤ>ℚ (mkℚᵘ p q-1)) ℤP.≤? n
  ... | .Bool.true because ofʸ P = P
  ... | .Bool.false because ofⁿ ¬P = ⊥-elim (antidensity-ℤ (n ℤ.- t , 0<n-t ,′ n-t<1))
    where
      open ℤP.≤-Reasoning
      open import Data.Integer.Solver
      open +-*-Solver
      q : ℕ
      q = suc q-1

      t : ℤ
      t = p divℕ q

      r : ℕ
      r = p modℕ q

      n-t<1 : n ℤ.- t ℤ.< + 1
      n-t<1 = ℤP.<-≤-trans (ℤP.+-monoˡ-< (ℤ.- t) (ℤP.≰⇒> ¬P))
            (ℤP.≤-reflexive (solve 1 (λ t -> con (+ 1) :+ t :- t := con (+ 1)) _≡_.refl t))

      part1 : (+ r) ℤ.+ t ℤ.* (+ q) ℤ.< n ℤ.* (+ q)
      part1 = begin-strict
        (+ r) ℤ.+ t ℤ.* (+ q) ≡⟨ trans (sym (a≡a%ℕn+[a/ℕn]*n p q)) (sym (ℤP.*-identityʳ p)) ⟩
        p ℤ.* (+ 1)           <⟨ ℚP.drop-*<* p/q<n ⟩
        n ℤ.* (+ q) ∎

      part2 : (+ r) ℤ.< (n ℤ.- t) ℤ.* (+ q)
      part2 = begin-strict
        + r                                   ≡⟨ solve 2 (λ r t -> r := r :+ t :- t) _≡_.refl (+ r) (t ℤ.* (+ q)) ⟩
        (+ r) ℤ.+ t ℤ.* (+ q) ℤ.- t ℤ.* (+ q) <⟨ ℤP.+-monoˡ-< (ℤ.- (t ℤ.* + q)) part1 ⟩
        n ℤ.* (+ q) ℤ.- t ℤ.* (+ q)           ≡⟨ solve 3 (λ n q t -> n :* q :- t :* q := (n :- t) :* q) _≡_.refl n (+ q) t ⟩
        (n ℤ.- t) ℤ.* (+ q)                    ∎

      part3 : + 0 ℤ.< (n ℤ.- t) ℤ.* (+ q)
      part3 = ℤP.≤-<-trans (+≤+ ℕ.z≤n) part2

      0<n-t : + 0 ℤ.< n ℤ.- t
      0<n-t = ℤP.*-cancelʳ-<-nonNeg q (ℤP.≤-<-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ q))) part3)

least : ∀ (p : ℚᵘ) -> ∃ λ (K : ℤ) ->
        p ℚ.< (K / 1) × (∀ (n : ℤ) -> p ℚ.< (n / 1) -> K ℤ.≤ n)
least p = least-ℤ>ℚ p , least-ℤ>ℚ-greater p ,′ least-ℤ>ℚ-least p

K : ℝ -> ℕ
K x with ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ
... | mkℚᵘ p q-1 = suc ℤ.∣ p divℕ (suc q-1) ∣

private
  Kx=1+t : ∀ (x : ℝ) -> + K x ≡ (+ 1) ℤ.+ (↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))
  Kx=1+t x = sym (trans (cong (λ x -> (+ 1) ℤ.+ x) (sym ∣t∣=t)) _≡_.refl)
    where
       t : ℤ
       t = ↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) divℕ ↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ)

       0≤∣x₁∣+2 : 0ℚᵘ ℚ.≤ ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ
       0≤∣x₁∣+2 = ℚP.≤-trans (ℚP.0≤∣p∣ (seq x 1)) (ℚP.p≤p+q {ℚ.∣ seq x 1 ∣} {2ℚᵘ} _)

       ∣t∣=t : + ℤ.∣ t ∣ ≡ t
       ∣t∣=t = ℤP.0≤n⇒+∣n∣≡n (0≤n⇒0≤n/ℕd (↥ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ)) (↧ₙ (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ)) (ℚP.≥0⇒↥≥0 0≤∣x₁∣+2))
      

canonical-property : ∀ (x : ℝ) -> ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< (+ K x) / 1 ×
                 (∀ (n : ℤ) -> ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< n / 1 -> + K x ℤ.≤ n)
canonical-property x = left ,′ right
  where
    left : ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< (+ K x) / 1
    left = ℚP.<-respʳ-≃ (ℚP.≃-reflexive (ℚP./-cong (sym (Kx=1+t x)) _≡_.refl _ _))
                   (least-ℤ>ℚ-greater (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ))

    right : ∀ (n : ℤ) -> ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ ℚ.< n / 1 -> + K x ℤ.≤ n
    right n hyp = ℤP.≤-trans (ℤP.≤-reflexive (Kx=1+t x)) (least-ℤ>ℚ-least (ℚ.∣ seq x 1 ∣ ℚ.+ 2ℚᵘ) n hyp)

canonical-greater : ∀ (x : ℝ) -> ∀ (n : ℕ) -> {n ≢0} -> ℚ.∣ seq x n ∣ ℚ.< (+ K x) / 1
canonical-greater x (suc k₁) = begin-strict
  ℚ.∣ seq x n ∣                               ≈⟨ ℚP.∣-∣-cong (solve 2 (λ xn x1 ->
                                                             xn := xn :- x1 :+ x1)
                                                (ℚ.*≡* _≡_.refl) (seq x n) (seq x 1)) ⟩
  ℚ.∣ seq x n ℚ.- seq x 1 ℚ.+ seq x 1 ∣       ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x n ℚ.- seq x 1) (seq x 1) ⟩
  ℚ.∣ seq x n ℚ.- seq x 1 ∣ ℚ.+ ℚ.∣ seq x 1 ∣ ≤⟨ ℚP.+-monoˡ-≤ ℚ.∣ seq x 1 ∣ (reg x n 1) ⟩
  (+ 1 / n) ℚ.+ (+ 1 / 1) ℚ.+ ℚ.∣ seq x 1 ∣   ≤⟨ ℚP.+-monoˡ-≤ ℚ.∣ seq x 1 ∣
                                               (ℚP.≤-trans (ℚP.+-monoˡ-≤ (+ 1 / 1) 1/n≤1) ℚP.≤-refl) ⟩
  2ℚᵘ ℚ.+ ℚ.∣ seq x 1 ∣                       <⟨ ℚP.<-respˡ-≃ (ℚP.+-comm ℚ.∣ seq x 1 ∣ 2ℚᵘ) (proj₁ (canonical-property x)) ⟩
  (+ K x) / 1                                  ∎
  where
    open ℚP.≤-Reasoning
    open import Data.Rational.Unnormalised.Solver
    open +-*-Solver
    n : ℕ
    n = suc k₁

    1/n≤1 : + 1 / n ℚ.≤ + 1 / 1
    1/n≤1 = *≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-identityˡ (+ 1)))
                (ℤP.≤-trans (+≤+ (ℕ.s≤s ℕ.z≤n)) (ℤP.≤-reflexive (sym (ℤP.*-identityˡ (+ n))))))

∣∣p∣-∣q∣∣≤∣p-q∣ : ∀ p q -> ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ℚ.≤ ℚ.∣ p ℚ.- q ∣
∣∣p∣-∣q∣∣≤∣p-q∣ p q = [ lemA p q , lemB p q ]′ (ℚP.≤-total ℚ.∣ q ∣ ℚ.∣ p ∣)
  where
    open ℚP.≤-Reasoning
    open import Data.Rational.Unnormalised.Solver
    open +-*-Solver

    lemA : ∀ p q -> ℚ.∣ q ∣ ℚ.≤ ℚ.∣ p ∣ -> ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ℚ.≤ ℚ.∣ p ℚ.- q ∣
    lemA p q hyp = begin
      ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣             ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp) ⟩
      ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣                   ≈⟨ ℚP.+-congˡ (ℚ.- ℚ.∣ q ∣) (ℚP.∣-∣-cong (solve 2 (λ p q ->
                                               p := p :- q :+ q) ℚP.≃-refl p q)) ⟩
      ℚ.∣ p ℚ.- q ℚ.+ q ∣ ℚ.- ℚ.∣ q ∣       ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- ℚ.∣ q ∣) (ℚP.∣p+q∣≤∣p∣+∣q∣ (p ℚ.- q) q) ⟩
      ℚ.∣ p ℚ.- q ∣ ℚ.+ ℚ.∣ q ∣ ℚ.- ℚ.∣ q ∣ ≈⟨ solve 2 (λ x y -> x :+ y :- y := x)
                                              ℚP.≃-refl ℚ.∣ p ℚ.- q ∣ ℚ.∣ q ∣ ⟩
      ℚ.∣ p ℚ.- q ∣ ∎

    lemB : ∀ p q -> ℚ.∣ p ∣ ℚ.≤ ℚ.∣ q ∣ -> ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ℚ.≤ ℚ.∣ p ℚ.- q ∣
    lemB p q hyp = begin
      ℚ.∣ ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣ ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (ℚ.∣ p ∣ ℚ.- ℚ.∣ q ∣))) (ℚP.∣-∣-cong
                                  (solve 2 (λ p q -> :- (p :- q) := q :- p) ℚP.≃-refl ℚ.∣ p ∣ ℚ.∣ q ∣)) ⟩
      ℚ.∣ ℚ.∣ q ∣ ℚ.- ℚ.∣ p ∣ ∣ ≤⟨ lemA q p hyp ⟩
      ℚ.∣ q ℚ.- p ∣            ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (q ℚ.- p))) (ℚP.∣-∣-cong
                                  (solve 2 (λ p q -> :- (q :- p) := p :- q) ℚP.≃-refl p q)) ⟩
      ℚ.∣ p ℚ.- q ∣  ∎
      
    {-
Reminder: Make the proof of reg (x * y) abstract to avoid performance issues. Maybe do the same
with the other long proofs too.
-}
_*_ : ℝ -> ℝ -> ℝ
seq (x * y) n = seq x (2 ℕ.* (K x ℕ.⊔ K y) ℕ.* n) ℚ.* seq y (2 ℕ.* (K x ℕ.⊔ K y) ℕ.* n)
reg (x * y) (suc k₁) (suc k₂) = begin
  ℚ.∣ x₂ₖₘ ℚ.* y₂ₖₘ ℚ.- x₂ₖₙ ℚ.* y₂ₖₙ ∣        ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ xm ym xn yn ->
                                                              xm ℚ:* ym ℚ:- xn ℚ:* yn ℚ:=
                                                              xm ℚ:* (ym ℚ:- yn) ℚ:+ yn ℚ:* (xm ℚ:- xn))
                                                              (ℚ.*≡* _≡_.refl) x₂ₖₘ y₂ₖₘ x₂ₖₙ y₂ₖₙ) ⟩
  ℚ.∣ x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ) ℚ.+
      y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ) ∣              ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ))
                                                                (y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ)) ⟩
  ℚ.∣ x₂ₖₘ ℚ.* (y₂ₖₘ ℚ.- y₂ₖₙ) ∣ ℚ.+
  ℚ.∣ y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ) ∣              ≈⟨ ℚP.≃-trans (ℚP.+-congˡ ℚ.∣ y₂ₖₙ ℚ.* (x₂ₖₘ ℚ.- x₂ₖₙ) ∣
                                                            (ℚP.∣p*q∣≃∣p∣*∣q∣ x₂ₖₘ (y₂ₖₘ ℚ.- y₂ₖₙ)))
                                                            (ℚP.+-congʳ (ℚ.∣ x₂ₖₘ ∣ ℚ.* ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣)
                                                            (ℚP.∣p*q∣≃∣p∣*∣q∣ y₂ₖₙ (x₂ₖₘ ℚ.- x₂ₖₙ))) ⟩
  ℚ.∣ x₂ₖₘ ∣ ℚ.* ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣ ℚ.+
  ℚ.∣ y₂ₖₙ ∣ ℚ.* ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣           ≤⟨ ℚP.≤-trans (ℚP.+-monoˡ-≤ (ℚ.∣ y₂ₖₙ ∣ ℚ.* ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣ )
                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣} _ ∣x₂ₖₘ∣≤k))
                                                            (ℚP.+-monoʳ-≤ ((+ k / 1) ℚ.* ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣)
                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣} _ ∣y₂ₖₙ∣≤k)) ⟩
  (+ k / 1) ℚ.* ℚ.∣ y₂ₖₘ ℚ.- y₂ₖₙ ∣ ℚ.+
  (+ k / 1) ℚ.* ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣           ≤⟨ ℚP.≤-trans (ℚP.+-monoˡ-≤ ((+ k / 1) ℚ.* ℚ.∣ x₂ₖₘ ℚ.- x₂ₖₙ ∣)
                                                            (ℚP.*-monoʳ-≤-nonNeg {+ k / 1} _ (reg y 2km 2kn)))
                                                            (ℚP.+-monoʳ-≤ ((+ k / 1) ℚ.* ((+ 1 / 2km) ℚ.+ (+ 1 / 2kn)))
                                                            (ℚP.*-monoʳ-≤-nonNeg {+ k / 1} _ (reg x 2km 2kn))) ⟩
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
    open import Data.Rational.Unnormalised.Solver as ℚ-Solver
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _ℚ:+_
        ; _:-_ to _ℚ:-_
        ; _:*_ to _ℚ:*_
        ; _:=_ to _ℚ:=_
        )
    open import Data.Integer.Solver as ℤ-Solver
    open ℤ-Solver.+-*-Solver
    m : ℕ
    m = suc k₁

    n : ℕ
    n = suc k₂

    k : ℕ
    k = K x ℕ.⊔ K y

    2km : ℕ
    2km = 2 ℕ.* k ℕ.* m

    2kn : ℕ
    2kn = 2 ℕ.* k ℕ.* n

    x₂ₖₘ : ℚᵘ
    x₂ₖₘ = seq x (2 ℕ.* k ℕ.* m)

    x₂ₖₙ : ℚᵘ
    x₂ₖₙ = seq x (2 ℕ.* k ℕ.* n)

    y₂ₖₘ : ℚᵘ
    y₂ₖₘ = seq y (2 ℕ.* k ℕ.* m)

    y₂ₖₙ : ℚᵘ
    y₂ₖₙ = seq y (2 ℕ.* k ℕ.* n)

    ∣x₂ₖₘ∣≤k : ℚ.∣ x₂ₖₘ ∣ ℚ.≤ (+ k) / 1
    ∣x₂ₖₘ∣≤k = ℚP.≤-trans (ℚP.<⇒≤ (canonical-greater x 2km))
               (*≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-identityʳ (+ K x)))
               (ℤP.≤-trans (+≤+ (ℕP.m≤m⊔n (K x) (K y))) (ℤP.≤-reflexive (sym (ℤP.*-identityʳ (+ k)))))))

    ∣y₂ₖₙ∣≤k : ℚ.∣ y₂ₖₙ ∣ ℚ.≤ (+ k) / 1
    ∣y₂ₖₙ∣≤k = ℚP.≤-trans (ℚP.<⇒≤ (canonical-greater y 2kn))
               (*≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-identityʳ (+ K y)))
               (ℤP.≤-trans (+≤+ (ℕP.m≤n⊔m (K x) (K y))) (ℤP.≤-reflexive (sym (ℤP.*-identityʳ (+ k)))))))

p≃q⇒-p≃-q : ∀ (p q : ℚᵘ) -> p ℚ.≃ q -> ℚ.- p ℚ.≃ ℚ.- q
p≃q⇒-p≃-q p q p≃q = ℚP.p-q≃0⇒p≃q (ℚ.- p) (ℚ.- q) (ℚP.≃-trans (ℚP.+-comm (ℚ.- p) (ℚ.- (ℚ.- q)))
                                                 (ℚP.≃-trans (ℚP.+-congˡ (ℚ.- p) (ℚP.neg-involutive q))
                                                 (ℚP.p≃q⇒p-q≃0 q p (ℚP.≃-sym p≃q))))

p≤∣p∣ : ∀ (p : ℚᵘ) -> p ℚ.≤ ℚ.∣ p ∣
p≤∣p∣ (mkℚᵘ (+_ n) q-1) = ℚP.≤-refl
p≤∣p∣ (mkℚᵘ (-[1+_] n) q-1) = *≤* ℤ.-≤+

{-
  The book uses an extra assumption to simplify this proof. It seems, for a proper proof, a 4-way
  case split is required, as done below.
-}
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
                                                                   (p≃q⇒-p≃-q (seq x m ℚ.⊔ seq y m) (seq y m ℚ.⊔ seq x m) (ℚP.⊔-comm (seq x m) (seq y m))))
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
                                                                    (p≃q⇒-p≃-q (seq x n ℚ.⊔ seq y n) (seq y n ℚ.⊔ seq x n) (ℚP.⊔-comm (seq x n) (seq y n)))) ⟩
           (seq y m ℚ.⊔ seq x m) ℚ.- (seq y n ℚ.⊔ seq x n)       ≤⟨ lem (seq y m) (seq x m) (seq y n) (seq x n) hyp2 m n (reg x m n) ⟩
           (+ 1 / m) ℚ.+ (+ 1 / n)                                                      ∎
    
-_ : ℝ -> ℝ
seq (- x) n = ℚ.- seq x n
reg (- x) m n {m≢0} {n≢0} = begin
  ℚ.∣ ℚ.- seq x m ℚ.- (ℚ.- seq x n) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.≃-sym (ℚP.≃-reflexive (ℚP.neg-distrib-+ (seq x m) (ℚ.- seq x n)))) ⟩
  ℚ.∣ ℚ.- (seq x m ℚ.- seq x n) ∣     ≤⟨ ℚP.≤-respˡ-≃ (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (seq x m ℚ.- seq x n))) (reg x m n {m≢0} {n≢0}) ⟩
  ((+ 1) / m) ℚ.+ ((+ 1) / n)          ∎
  where
    open ℚP.≤-Reasoning

_-_ : ℝ -> ℝ -> ℝ
x - y = x + (- y)

-- Gets a real representation of a rational number.
-- For a rational α, one real representation is the sequence
-- α* = (α, α, α, α, α, ...).
_⋆ : ℚᵘ -> ℝ
seq (p ⋆) n = p
reg (p ⋆) (suc m) (suc n) = begin
  ℚ.∣ p ℚ.- p ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.p≃q⇒p-q≃0 p p ℚP.≃-refl) ⟩
  0ℚᵘ ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  ((+ 1) / (suc m)) ℚ.+ ((+ 1) / (suc n)) ∎
  where
    open ℚP.≤-Reasoning

{-
Proofs that the above operations are well-defined functions
(for setoid equality).
-}

{-
∣ x₂ₙ + y₂ₙ - z₂ₙ - w₂ₙ ∣
≤ ∣ x₂ₙ - z₂ₙ ∣ + ∣ y₂ₙ - w₂ₙ ∣
≤ 2/2n + 2/2n
= 2/n
-}
+-cong : Congruent₂ _≃_ _+_
+-cong {x} {z} {y} {w} x≃z y≃w (suc k₁) = begin
  ℚ.∣ seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n) ℚ.-
      (seq z (2 ℕ.* n) ℚ.+ seq w (2 ℕ.* n)) ∣   ≤⟨ ℚP.≤-respˡ-≃ (ℚP.∣-∣-cong (ℚsolve 4 (λ x y z w ->
                                                   (x ℚ:- z) ℚ:+ (y ℚ:- w) ℚ:= x ℚ:+ y ℚ:- (z ℚ:+ w))
                                                   ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)) (seq z (2 ℕ.* n)) (seq w (2 ℕ.* n))))
                                                   (ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x (2 ℕ.* n) ℚ.- seq z (2 ℕ.* n)) (seq y (2 ℕ.* n) ℚ.- seq w (2 ℕ.* n))) ⟩
  ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq z (2 ℕ.* n) ∣ ℚ.+
  ℚ.∣ seq y (2 ℕ.* n) ℚ.- seq w (2 ℕ.* n) ∣     ≤⟨ ℚP.≤-trans (ℚP.+-monoˡ-≤ ℚ.∣ seq y (2 ℕ.* n) ℚ.- seq w (2 ℕ.* n) ∣ (x≃z (2 ℕ.* n)))
                                                              (ℚP.+-monoʳ-≤ (+ 2 / (2 ℕ.* n)) (y≃w (2 ℕ.* n))) ⟩
  (+ 2 / (2 ℕ.* n)) ℚ.+ (+ 2 / (2 ℕ.* n))       ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                   (con (+ 2) :* (con (+ 2) :* n) :+ con (+ 2) :* (con (+ 2) :* n)) :* n :=
                                                   (con (+ 2) :* ((con (+ 2) :* n) :* (con (+ 2) :* n)))) _≡_.refl (+ n)) ⟩
  + 2 / n                                        ∎
  where
    open ℚP.≤-Reasoning
    open import Data.Rational.Unnormalised.Solver as ℚ-Solver
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _ℚ:+_
        ; _:-_ to _ℚ:-_
        ; _:=_ to _ℚ:=_
        )
    open import Data.Integer.Solver as ℤ-Solver
    open ℤ-Solver.+-*-Solver
    n : ℕ
    n = suc k₁

+-congʳ : ∀ x {y z} -> y ≃ z -> x + y ≃ x + z
+-congʳ x {y} {z} y≃z = +-cong {x} {x} {y} {z} (≃-refl {x}) y≃z

+-congˡ : ∀ x {y z} -> y ≃ z -> y + x ≃ z + x
+-congˡ x {y} {z} y≃z = +-cong {y} {z} {x} {x} y≃z (≃-refl {x})

+-comm : Commutative _≃_ _+_
+-comm x y (suc k₁) = begin
  ℚ.∣ (seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)) ℚ.-
      (seq y (2 ℕ.* n) ℚ.+ seq x (2 ℕ.* n)) ∣   ≈⟨ ℚP.∣-∣-cong (solve 2 (λ x y ->
                                                   (x :+ y) :- (y :+ x) := con (0ℚᵘ))
                                                   ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  0ℚᵘ                                           ≤⟨ *≤* (+≤+ ℕ.z≤n) ⟩
  (+ 2) / n                                      ∎
  where
    open import Data.Rational.Unnormalised.Solver
    open +-*-Solver
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

+-assoc : Associative _≃_ _+_
+-assoc x y z (suc k₁) = begin
  ℚ.∣ ((seq x 4n ℚ.+ seq y 4n) ℚ.+ seq z 2n) ℚ.-
      (seq x 2n ℚ.+ (seq y 4n ℚ.+ seq z 4n)) ∣                ≈⟨ ℚP.∣-∣-cong (ℚsolve 5 (λ x4 y4 z2 x2 z4 ->
                                                                                  ((x4 ℚ:+ y4) ℚ:+ z2) ℚ:- (x2 ℚ:+ (y4 ℚ:+ z4)) ℚ:=
                                                                                  (x4 ℚ:- x2) ℚ:+ (z2 ℚ:- z4))
                                                                                  ℚP.≃-refl (seq x 4n) (seq y 4n) (seq z 2n) (seq x 2n) (seq z 4n)) ⟩
  ℚ.∣ (seq x 4n ℚ.- seq x 2n) ℚ.+ (seq z 2n ℚ.- seq z 4n) ∣   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x 4n ℚ.- seq x 2n) (seq z 2n ℚ.- seq z 4n) ⟩
  ℚ.∣ seq x 4n ℚ.- seq x 2n ∣ ℚ.+ ℚ.∣ seq z 2n ℚ.- seq z 4n ∣ ≤⟨ ℚP.≤-trans (ℚP.+-monoʳ-≤ ℚ.∣ seq x 4n ℚ.- seq x 2n ∣ (reg z 2n 4n))
                                                                            (ℚP.+-monoˡ-≤ ((+ 1 / 2n) ℚ.+ (+ 1 / 4n)) (reg x 4n 2n)) ⟩
  ((+ 1 / 4n) ℚ.+ (+ 1 / 2n)) ℚ.+ ((+ 1 / 2n) ℚ.+ (+ 1 / 4n)) ≈⟨ ℚ.*≡* (solve 1 ((λ 2n ->
                                                                            ((con (+ 1) :* 2n :+ con (+ 1) :* (con (+ 2) :* 2n)) :*
                                                                            (2n :* (con (+ 2) :* 2n)) :+
                                                                            (con (+ 1) :* (con (+ 2) :* 2n) :+ con (+ 1) :* 2n) :*
                                                                            ((con (+ 2) :* 2n) :* 2n)) :* 2n :=
                                                                            con (+ 3) :* (((con (+ 2) :* 2n) :* 2n) :*
                                                                            (2n :* (con (+ 2) :* 2n)))))
                                                                            _≡_.refl (+ 2n)) ⟩
  + 3 / 2n                                                    ≤⟨ *≤* (ℤP.*-monoʳ-≤-nonNeg 2n (+≤+ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n {1})))))) ⟩
  + 4 / 2n                                                    ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                                            con (+ 4) :* n := con (+ 2) :* (con (+ 2) :* n))
                                                                            _≡_.refl (+ n)) ⟩
  + 2 / n                                                      ∎
  where
    open import Data.Rational.Unnormalised.Solver as ℚ-Solver
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _ℚ:+_
        ; _:-_ to _ℚ:-_
        ; _:=_ to _ℚ:=_
        )
    open import Data.Integer.Solver as ℤ-Solver
    open ℤ-Solver.+-*-Solver
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

    2n : ℕ
    2n = 2 ℕ.* n

    4n : ℕ
    4n = 2 ℕ.* 2n

0ℝ : ℝ
0ℝ = 0ℚᵘ ⋆

1ℝ : ℝ
1ℝ = ℚ.1ℚᵘ ⋆

+-identityˡ : LeftIdentity _≃_ 0ℝ _+_
+-identityˡ x (suc k₁) = begin
  ℚ.∣ (0ℚᵘ ℚ.+ seq x (2 ℕ.* n)) ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- seq x n) (ℚP.+-identityˡ (seq x (2 ℕ.* n)))) ⟩
  ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq x n ∣           ≤⟨ reg x (2 ℕ.* n) n ⟩
  (+ 1 / (2 ℕ.* n)) ℚ.+ (+ 1 / n)             ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                            (con (+ 1) :* n :+ con (+ 1) :* (con (+ 2) :* n)) :* (con (+ 2) :* n) :=
                                                            con (+ 3) :* ((con (+ 2) :* n) :* n))
                                                            _≡_.refl (+ n)) ⟩
  + 3 / (2 ℕ.* n)                             ≤⟨ *≤* (ℤP.*-monoʳ-≤-nonNeg (2 ℕ.* n) (+≤+ (ℕ.s≤s (ℕ.s≤s (ℕ.s≤s (ℕ.z≤n {1})))))) ⟩
  + 4 / (2 ℕ.* n)                             ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                            con (+ 4) :* n := con (+ 2) :* (con (+ 2) :* n))
                                                            _≡_.refl (+ n)) ⟩
  + 2 / n                                      ∎
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver as ℤ-Solver
    open ℤ-Solver.+-*-Solver
    n : ℕ
    n = suc k₁

+-identityʳ : RightIdentity _≃_ 0ℝ _+_
+-identityʳ x = ≃-trans {x + 0ℝ} {0ℝ + x} {x} (+-comm x 0ℝ) (+-identityˡ x)

+-identity : Identity _≃_ 0ℝ _+_
+-identity = +-identityˡ , +-identityʳ

+-inverseʳ : RightInverse _≃_ 0ℝ -_ _+_
+-inverseʳ x (suc k₁) = begin
  ℚ.∣ (seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)) ℚ.+ 0ℚᵘ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ 0ℚᵘ (ℚP.+-inverseʳ (seq x (2 ℕ.* n)))) ⟩
  0ℚᵘ                                                 ≤⟨ *≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ n))) (+≤+ ℕ.z≤n)) ⟩
  + 2 / n                                              ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

+-inverseˡ : LeftInverse _≃_ 0ℝ -_ _+_
+-inverseˡ x = ≃-trans {(- x) + x} {x - x} {0ℝ} (+-comm (- x) x) (+-inverseʳ x)

+-inverse : Inverse _≃_ 0ℝ -_ _+_
+-inverse = +-inverseˡ , +-inverseʳ

⋆-distrib-+ : ∀ (p r : ℚᵘ) -> (p ℚ.+ r) ⋆ ≃ p ⋆ + r ⋆
⋆-distrib-+ (mkℚᵘ p q-1) (mkℚᵘ u v-1) (suc k₁) = begin
  ℚ.∣ ((p / q) ℚ.+ (u / v)) ℚ.- ((p / q) ℚ.+ (u / v)) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ ((p / q) ℚ.+ (u / v))) ⟩
  0ℚᵘ                                                   ≤⟨ *≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ n))) (+≤+ ℕ.z≤n)) ⟩
  (+ 2) / n                                              ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

    q : ℕ
    q = suc q-1

    v : ℕ
    v = suc v-1

⋆-distrib-neg : ∀ (p : ℚᵘ) -> (ℚ.- p) ⋆ ≃ - (p ⋆)
⋆-distrib-neg p (suc k₁) = begin
  ℚ.∣ ℚ.- p ℚ.- (ℚ.- p) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (ℚ.- p)) ⟩
  0ℚᵘ                     ≤⟨ *≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ n))) (+≤+ ℕ.z≤n)) ⟩
  (+ 2) / n                ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

abstract
  regular⇒cauchy : ∀ (x : ℝ) -> ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (m n : ℕ) ->
                   N ℕ.≤ m -> N ℕ.≤ n -> ℚ.∣ seq x m ℚ.- seq x n ∣ ℚ.≤ (+ 1 / j) {j≢0}
  regular⇒cauchy x (suc k₁) = 2 ℕ.* j , right
    where
      open ℚP.≤-Reasoning
      open import Data.Integer.Solver
      open +-*-Solver
      j : ℕ
      j = suc k₁

      N≤m⇒m≢0 : ∀ (m : ℕ) -> 2 ℕ.* j ℕ.≤ m -> m ≢0
      N≤m⇒m≢0 (suc m) N≤m = _

      N≤m⇒1/m≤1/N : ∀ (m : ℕ) -> (N≤m : 2 ℕ.* j ℕ.≤ m) -> (+ 1 / m) {N≤m⇒m≢0 m N≤m} ℚ.≤ (+ 1 / (2 ℕ.* j))
      N≤m⇒1/m≤1/N (suc m) N≤m = *≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-identityˡ (+ (2 ℕ.* j))))
                              (ℤP.≤-trans (ℤ.+≤+ N≤m) (ℤP.≤-reflexive (sym (ℤP.*-identityˡ (+ (suc m)))))))
  
      right : ∀ (m n : ℕ) -> 2 ℕ.* j ℕ.≤ m -> 2 ℕ.* j ℕ.≤ n ->
              ℚ.∣  seq x m ℚ.- seq x n ∣ ℚ.≤ + 1 / j
      right m n N≤m N≤n = begin 
        ℚ.∣ seq x m ℚ.- seq x n ∣ ≤⟨ reg x m n {N≤m⇒m≢0 m N≤m} {N≤m⇒m≢0 n N≤n} ⟩
        (+ 1 / m) {N≤m⇒m≢0 m N≤m} ℚ.+ (+ 1 / n) {N≤m⇒m≢0 n N≤n}   ≤⟨ ℚP.≤-trans
                                                                     (ℚP.+-monoˡ-≤ ((+ 1 / n) {N≤m⇒m≢0 n N≤n}) (N≤m⇒1/m≤1/N m N≤m))
                                                                     (ℚP.+-monoʳ-≤ (+ 1 / (2 ℕ.* j)) (N≤m⇒1/m≤1/N n N≤n)) ⟩
        (+ 1 / (2 ℕ.* j)) ℚ.+ (+ 1 / (2 ℕ.* j)) ≈⟨ ℚ.*≡* (solve 1 (λ j ->
                                                   (con (+ 1) :* (con (+ 2) :* j) :+ con (+ 1) :* (con (+ 2) :* j)) :* j :=
                                                   (con (+ 1) :* ((con (+ 2) :* j) :* (con (+ 2) :* j)))) _≡_.refl (+ j)) ⟩
        + 1 / j                    ∎

  equals-to-cauchy : ∀ (x y : ℝ) -> x ≃ y -> ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
                     ∃ λ (N : ℕ) -> ∀ (m n : ℕ) -> N ℕ.< m -> N ℕ.< n ->
                     ℚ.∣ seq x m ℚ.- seq y n ∣ ℚ.≤ (+ 1 / j) {j≢0}
  equals-to-cauchy x y x≃y (suc k₁) = N , lemA
    where
      open ℚP.≤-Reasoning
      open import Data.Integer.Solver as ℤ-Solver
      open ℤ-Solver.+-*-Solver
      open import Data.Rational.Unnormalised.Solver as ℚ-Solver
      open ℚ-Solver.+-*-Solver using ()
        renaming
          ( solve to ℚsolve
          ; _:+_ to _ℚ:+_
          ; _:-_ to _ℚ:-_
          ; _:*_ to _ℚ:*_
          ; _:=_ to _ℚ:=_
          )
      j : ℕ
      j = suc k₁

      N₁ : ℕ
      N₁ = proj₁ (lemma1A x y x≃y (2 ℕ.* j))

      N₂ : ℕ
      N₂ = proj₁ (regular⇒cauchy x (2 ℕ.* j))

      N : ℕ
      N = N₁ ℕ.⊔ N₂

      lemA : ∀ (m n : ℕ) -> N ℕ.< m -> N ℕ.< n ->
             ℚ.∣ seq x m ℚ.- seq y n ∣ ℚ.≤ + 1 / j
      lemA (suc k₂) (suc k₃) N<m N<n = begin
        ℚ.∣ seq x m ℚ.- seq y n ∣     ≈⟨ ℚP.∣-∣-cong (ℚsolve 3 (λ xm yn xn ->
                                         xm ℚ:- yn ℚ:= (xm ℚ:- xn) ℚ:+ (xn ℚ:- yn))
                                         ℚP.≃-refl (seq x m) (seq y n) (seq x n)) ⟩
        ℚ.∣ (seq x m ℚ.- seq x n) ℚ.+
            (seq x n ℚ.- seq y n) ∣   ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x m ℚ.- seq x n)
                                                         (seq x n ℚ.- seq y n) ⟩
        ℚ.∣ seq x m ℚ.- seq x n ∣ ℚ.+
        ℚ.∣ seq x n ℚ.- seq y n ∣     ≤⟨ ℚP.+-mono-≤ (proj₂ (regular⇒cauchy x (2 ℕ.* j)) m n
                                                            (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.<⇒≤ N<m))
                                                            (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.<⇒≤ N<n)))
                                                     (proj₂ (lemma1A x y x≃y (2 ℕ.* j)) n
                                                            (ℕP.<-transʳ (ℕP.m≤m⊔n N₁ N₂) N<n)) ⟩
        (+ 1 / (2 ℕ.* j)) ℚ.+
        (+ 1 / (2 ℕ.* j))             ≈⟨ ℚ.*≡* (solve 1 (λ j ->
                                         (con (+ 1) :* (con (+ 2) :* j) :+ (con (+ 1) :* (con (+ 2) :* j))) :* j :=
                                         (con (+ 1) :* ((con (+ 2) :* j) :* (con (+ 2) :* j))))
                                         _≡_.refl (+ j)) ⟩
        + 1 / j                                  ∎
        where
          m : ℕ
          m = suc k₂

          n : ℕ
          n = suc k₃
            
*-cong : Congruent₂ _≃_ _*_
*-cong {x} {z} {y} {w} x≃z y≃w = lemma1B (x * y) (z * w) lemA
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver as ℤ-Solver
    open ℤ-Solver.+-*-Solver
    open import Data.Rational.Unnormalised.Solver as ℚ-Solver
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _ℚ:+_
        ; _:-_ to _ℚ:-_
        ; _:*_ to _ℚ:*_
        ; _:=_ to _ℚ:=_
        )
    lemA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> N ℕ.< n ->
           ℚ.∣ seq (x * y) n ℚ.- seq (z * w) n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    lemA (suc k₁) = N , lemB
      where
        j : ℕ
        j = suc k₁

        r : ℕ
        r = K x ℕ.⊔ K y

        t : ℕ
        t = K z ℕ.⊔ K w

        N₁ : ℕ
        N₁ = proj₁ (equals-to-cauchy x z x≃z (K y ℕ.* (2 ℕ.* j)))

        N₂ : ℕ
        N₂ = proj₁ (equals-to-cauchy y w y≃w (K z ℕ.* (2 ℕ.* j)))

        N : ℕ
        N = N₁ ℕ.⊔ N₂

        lemB : ∀ (n : ℕ) -> N ℕ.< n ->
               ℚ.∣ seq (x * y) n ℚ.- seq (z * w) n ∣ ℚ.≤ (+ 1 / j)
        lemB (suc k₂) N<n = begin
          ℚ.∣ x₂ᵣₙ ℚ.* y₂ᵣₙ ℚ.- z₂ₜₙ ℚ.* w₂ₜₙ ∣             ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ x y z w ->
                                                               x ℚ:* y ℚ:- z ℚ:* w ℚ:= y ℚ:* (x ℚ:- z) ℚ:+ z ℚ:* (y ℚ:- w))
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
                                                                                               (ℚP.<⇒≤ (canonical-greater y (2 ℕ.* r ℕ.* n))))
                                                                          (ℚP.*-monoʳ-≤-nonNeg {+ K y / 1} _
                                                                                               (proj₂ (equals-to-cauchy x z x≃z (K y ℕ.* (2 ℕ.* j)))
                                                                                                      (2 ℕ.* r ℕ.* n) (2 ℕ.* t ℕ.* n)
                                                                                                      (N₁< (2 ℕ.* r ℕ.* n) (N<2kn r))
                                                                                                      (N₁< (2 ℕ.* t ℕ.* n) (N<2kn t)))))
                                                                          (ℚP.≤-trans
                                                                          (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₂ᵣₙ ℚ.- w₂ₜₙ ∣} _
                                                                                               (ℚP.<⇒≤ (canonical-greater z (2 ℕ.* t ℕ.* n))))
                                                                          (ℚP.*-monoʳ-≤-nonNeg {+ K z / 1} _
                                                                                               (proj₂ (equals-to-cauchy y w y≃w (K z ℕ.* (2 ℕ.* j)))
                                                                                               (2 ℕ.* r ℕ.* n) (2 ℕ.* t ℕ.* n)
                                                                                               (N₂< (2 ℕ.* r ℕ.* n) (N<2kn r))
                                                                                               (N₂< (2 ℕ.* t ℕ.* n) (N<2kn t))))) ⟩
          (+ K y / 1) ℚ.* (+ 1 / (K y ℕ.* (2 ℕ.* j))) ℚ.+
          (+ K z / 1) ℚ.* (+ 1 / (K z ℕ.* (2 ℕ.* j)))     ≈⟨ ℚ.*≡* (solve 3 (λ Ky Kz j ->

          -- Function for solver
          ((Ky :* con (+ 1)) :* (con (+ 1) :* (Kz :* (con (+ 2) :* j))) :+ (Kz :* con (+ 1) :* (con (+ 1) :* (Ky :* (con (+ 2) :* j))))) :* j :=
          con (+ 1) :* ((con (+ 1) :* (Ky :* (con (+ 2) :* j))) :* (con (+ 1) :* (Kz :* (con (+ 2) :* j)))))
          _≡_.refl (+ K y) (+ K z) (+ j)) ⟩
          
          + 1 / j                                          ∎
          where
            n : ℕ
            n = suc k₂

            x₂ᵣₙ : ℚᵘ
            x₂ᵣₙ = seq x (2 ℕ.* r ℕ.* n)

            y₂ᵣₙ : ℚᵘ
            y₂ᵣₙ = seq y (2 ℕ.* r ℕ.* n)

            z₂ₜₙ : ℚᵘ
            z₂ₜₙ = seq z (2 ℕ.* t ℕ.* n)

            w₂ₜₙ : ℚᵘ
            w₂ₜₙ = seq w (2 ℕ.* t ℕ.* n)

            N<2kn : ∀ (k : ℕ) -> {k ≢0} -> N ℕ.< 2 ℕ.* k ℕ.* n
            N<2kn (suc k) = ℕP.<-transˡ N<n (ℕP.m≤n*m n {2 ℕ.* (suc k)} ℕP.0<1+n)

            N₁< : ∀ (k : ℕ) -> N ℕ.< k -> N₁ ℕ.< k
            N₁< k N<k = ℕP.<-transʳ (ℕP.m≤m⊔n N₁ N₂) N<k

            N₂< : ∀ (k : ℕ) -> N ℕ.< k -> N₂ ℕ.< k
            N₂< k N<k = ℕP.<-transʳ (ℕP.m≤n⊔m N₁ N₂) N<k

*-congˡ : LeftCongruent _≃_ _*_
*-congˡ {x} {y} {z} y≃z = *-cong {x} {x} {y} {z} (≃-refl {x}) y≃z

*-congʳ : RightCongruent _≃_ _*_
*-congʳ {x} {y} {z} y≃z = *-cong {y} {z} {x} {x} y≃z (≃-refl {x})

*-comm : Commutative _≃_ _*_
*-comm x y (suc k₁) = begin
  ℚ.∣ seq (x * y) n ℚ.- seq (y * x) n ∣     ≈⟨ ℚP.∣-∣-cong (ℚP.≃-trans (ℚP.+-congʳ (seq (x * y) n)
                                                                       (p≃q⇒-p≃-q _ _ (ℚP.≃-sym xyℚ=yxℚ)))
                                                           (ℚP.+-inverseʳ (seq (x * y) n))) ⟩
  0ℚᵘ                                       ≤⟨ *≤* (+≤+ ℕ.z≤n) ⟩
  + 2 / n                                    ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁
    
    xyℚ=yxℚ : seq (x * y) n ℚ.≃ seq (y * x) n
    xyℚ=yxℚ = begin-equality
      seq x (2 ℕ.* (K x ℕ.⊔ K y) ℕ.* n) ℚ.*
      seq y (2 ℕ.* (K x ℕ.⊔ K y) ℕ.* n)     ≡⟨ cong (λ r ->
                                               seq x (2 ℕ.* r ℕ.* n) ℚ.* seq y (2 ℕ.* r ℕ.* n))
                                               (ℕP.⊔-comm (K x) (K y)) ⟩
      seq x (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n) ℚ.*
      seq y (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n)     ≈⟨ ℚP.*-comm (seq x (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n))
                                                         (seq y (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n)) ⟩
      seq y (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n) ℚ.*
      seq x (2 ℕ.* (K y ℕ.⊔ K x) ℕ.* n)      ∎

{-
Proposition:
  Multiplication on ℝ is associative.
Proof:
  Let x,y,z∈ℝ. We must show that (xy)z = x(yz). Define
          r = max{Kx, Ky}     s = max{Kxy, Kz}
          u = max{Kx, Kyz}    t = max{Ky, Kz},
noting that Kxy is the canonical bound for x * y (similarly for Kyz).
Let j∈ℤ⁺. Since (xₙ), (yₙ), and (zₙ) are Cauchy sequences, there is
N₁,N₂,N₃∈ℤ⁺ such that:
          ∣xₘ - xₙ∣  ≤ 1 / (Ky * Kz * 3j)     (m, n ≥ N₁),
          ∣yₘ - yₙ∣ ≤ 1 / (Kx * Kz * 3j)     (m, n ≥ N₂), and
          ∣zₘ - zₙ∣  ≤ 1 / (Kx * Ky * 3j)     (m, n ≥ N₃).
x = z and y = w
then
x * y = z * w
∣xₘ - zₙ∣ ≤ ε

Define N = max{N₁, N₂, N₃}. If we show that
       ∣x₄ᵣₛₙ * y₄ᵣₛₙ * z₂ₛₙ - x₂ᵤₙ * y₄ₜᵤₙ * z₄ₜᵤₙ∣ ≤ 1 / j
for all n ≥ N, then (xy)z = x(yz) by Lemma 1.
  Note that, for all a, b, c, d in ℚ, we have
               ab - cd = b(a - c) + c(b - d).
We will use this trick in our proof. We have: 
∀ ε > 0 ∃ N ∈ ℕ ∀ m, n ≥ N -> ∣xₘ - xₙ∣ ≤ ε

∀ j ∈ ℤ⁺ ∃ N ∈ ℕ ∀ m, n ≥ N ∣ xn - yn ∣ ≤ 1/j
∀ n ∈ ℕ (∣ xn - yn ∣ ≤ 2/n)

∣x₄ᵣₛₙ * y₄ᵣₛₙ * z₂ₛₙ - x₂ᵤₙ * y₄ₜᵤₙ * z₄ₜᵤₙ∣
= ∣y₄ᵣₛₙ * z₂ₛₙ(x₄ᵣₛₙ - x₂ᵤₙ) + x₂ᵤₙ(y₄ᵣₛₙ * z₂ₛₙ - y₄ₜᵤₙ * z₄ₜᵤₙ)∣  
= ∣y₄ᵣₛₙ * z₂ₛₙ(x₄ᵣₛₙ - x₂ᵤₙ) + x₂ᵤₙ(z₂ₛₙ(y₄ᵣₛₙ - y₄ₜᵤₙ) + y₄ₜᵤₙ(z₂ₛₙ - z₄ₜᵤₙ)∣                    
≤ ∣y₄ᵣₛₙ∣*∣z₂ₛₙ∣*∣x₄ᵣₛₙ - x₂ᵤₙ∣ + ∣x₂ᵤₙ∣*∣z₂ₛₙ∣*∣y₄ᵣₛₙ - y₄ₜᵤₙ∣ + ∣x₂ᵤₙ∣*∣y₄ₜᵤₙ∣*∣z₂ₛₙ - z₄ₜᵤₙ∣
≤ Ky * Kz * (1 / (Ky * Kz * 3j)) + Kx * Kz * (1 / (Kx * Kz * 3j)) + Kx * Ky * (1 / (Kx * Ky * 3j))
= 1 / 3j + 1 / 3j + 1 / 3j
= 1 / j.
Thus ∣x₄ᵣₛₙ*y₄ᵣₛₙ*z₂ₛₙ - x₂ᵤₙ*y₄ₜᵤₙ*z₄ₜᵤₙ∣ ≤ 1/j, as desired.                                    □
-}

*-assoc : Associative _≃_ _*_
*-assoc x y z = lemma1B ((x * y) * z) (x * (y * z)) lemA
  where
    open ℚP.≤-Reasoning

    r : ℕ
    r = K x ℕ.⊔ K y

    s : ℕ
    s = K (x * y) ℕ.⊔ K z

    u : ℕ
    u = K x ℕ.⊔ K (y * z)

    t : ℕ
    t = K y ℕ.⊔ K z

    lemA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> N ℕ.< n ->
          ℚ.∣ seq x (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)) ℚ.* seq y (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)) ℚ.* seq z (2 ℕ.* s ℕ.* n) ℚ.-
              seq x (2 ℕ.* u ℕ.* n) ℚ.* (seq y (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n)) ℚ.* seq z (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n)))∣ ℚ.≤ (+ 1 / j) {j≢0}
    lemA (suc k₁) = N , lemB
      where
        open ℚP.≤-Reasoning
        open import Data.Integer.Solver as ℤ-Solver
        open ℤ-Solver.+-*-Solver
        open import Data.Rational.Unnormalised.Solver as ℚ-Solver
        open ℚ-Solver.+-*-Solver using ()
          renaming
            ( solve to ℚsolve
            ; _:+_ to _ℚ:+_
            ; _:-_ to _ℚ:-_
            ; _:*_ to _ℚ:*_
            ; _:=_ to _ℚ:=_
            )
        j : ℕ
        j = suc k₁

        N₁ : ℕ
        N₁ = proj₁ (regular⇒cauchy x ((K y ℕ.* K z) ℕ.* (3 ℕ.* j)))

        N₂ : ℕ
        N₂ = proj₁ (regular⇒cauchy y (K x ℕ.* K z ℕ.* (3 ℕ.* j)))

        N₃ : ℕ
        N₃ = proj₁ (regular⇒cauchy z (K x ℕ.* K y ℕ.* (3 ℕ.* j)))

        N : ℕ
        N = (N₁ ℕ.⊔ N₂) ℕ.⊔ N₃

        lemB : ∀ (n : ℕ) -> N ℕ.< n ->
              ℚ.∣ seq x (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)) ℚ.* seq y (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)) ℚ.* seq z (2 ℕ.* s ℕ.* n) ℚ.-
              seq x (2 ℕ.* u ℕ.* n) ℚ.* (seq y (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n)) ℚ.* seq z (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n)))∣ ℚ.≤ (+ 1 / j)
        lemB (suc k₂) N<n = begin
          ℚ.∣ x₄ᵣₛₙ ℚ.* y₄ᵣₛₙ ℚ.* z₂ₛₙ ℚ.- x₂ᵤₙ ℚ.* (y₄ₜᵤₙ ℚ.* z₄ₜᵤₙ) ∣ ≈⟨ ℚP.∣-∣-cong (ℚsolve 6 (λ a b c d e f ->
                                                                           a ℚ:* b ℚ:* c ℚ:- d ℚ:* (e ℚ:* f) ℚ:=
                                                                           (b ℚ:* c) ℚ:* (a ℚ:- d) ℚ:+ d ℚ:* (c ℚ:* (b ℚ:- e) ℚ:+ e ℚ:* (c ℚ:- f)))
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
            n : ℕ
            n = suc k₂

            x₄ᵣₛₙ : ℚᵘ
            x₄ᵣₛₙ = seq x (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n))
            
            y₄ᵣₛₙ : ℚᵘ
            y₄ᵣₛₙ = seq y (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n))

            z₂ₛₙ : ℚᵘ
            z₂ₛₙ = seq z (2 ℕ.* s ℕ.* n)

            x₂ᵤₙ : ℚᵘ
            x₂ᵤₙ = seq x (2 ℕ.* u ℕ.* n)

            y₄ₜᵤₙ : ℚᵘ
            y₄ₜᵤₙ = seq y (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))

            z₄ₜᵤₙ : ℚᵘ
            z₄ₜᵤₙ = seq z (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))

            N≤4rsn : N ℕ.≤ 2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)
            N≤4rsn = ℕP.≤-trans (ℕP.<⇒≤ N<n) (ℕP.≤-trans
                     (ℕP.m≤n*m n {4 ℕ.* r ℕ.* s} ℕP.0<1+n) (ℤP.drop‿+≤+ (ℤP.≤-reflexive (solve 3 (λ r s n ->
                     con (+ 4) :* r :* s :* n := con (+ 2) :* r :* (con (+ 2) :* s :* n))
                     _≡_.refl (+ r) (+ s) (+ n)))))

            N₁≤4rsn : N₁ ℕ.≤ 2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)
            N₁≤4rsn = ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃) N≤4rsn)

            N₁≤2un : N₁ ℕ.≤ 2 ℕ.* u ℕ.* n
            N₁≤2un = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃))
                     (ℕP.≤-trans (ℕP.<⇒≤ N<n) (ℕP.m≤n*m n {2 ℕ.* u} ℕP.0<1+n))

            part1 : ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣ ℚ.≤ + 1 / (3 ℕ.* j)
            part1 = begin
              ℚ.∣ y₄ᵣₛₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣            ≤⟨ ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣} _ (ℚP.≤-trans
                                                                               (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₂ₛₙ ∣} _ (ℚP.<⇒≤
                                                                               (canonical-greater y (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)))))
                                                                               (ℚP.*-monoʳ-≤-nonNeg {(+ K y) / 1} _ (ℚP.<⇒≤
                                                                               (canonical-greater z (2 ℕ.* s ℕ.* n))))) ⟩
              (+ (K y ℕ.* K z) / 1) ℚ.* ℚ.∣ x₄ᵣₛₙ ℚ.- x₂ᵤₙ ∣                ≤⟨ ℚP.*-monoʳ-≤-nonNeg {+ (K y ℕ.* K z) / 1} _
                                                                               (proj₂ (regular⇒cauchy x (K y ℕ.* K z ℕ.* (3 ℕ.* j)))
                                                                               (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)) (2 ℕ.* u ℕ.* n) N₁≤4rsn N₁≤2un) ⟩
              (+ (K y ℕ.* K z) / 1) ℚ.* (+ 1 / (K y ℕ.* K z ℕ.* (3 ℕ.* j))) ≈⟨ ℚ.*≡* (solve 3 (λ Ky Kz j ->
                                                                               ((Ky :* Kz) :* con (+ 1)) :* (con (+ 3) :* j) :=
                                                                               (con (+ 1) :* (con (+ 1) :* (Ky :* Kz :* (con (+ 3) :* j)))))
                                                                               _≡_.refl (+ K y) (+ K z) (+ j)) ⟩
              + 1 / (3 ℕ.* j)                                                ∎

            N₂≤4rsn : N₂ ℕ.≤ 2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)
            N₂≤4rsn = ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃) N≤4rsn)

            N≤4tun : N ℕ.≤ 2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n)
            N≤4tun = ℕP.≤-trans (ℕP.<⇒≤ N<n) (ℕP.≤-trans (ℕP.m≤n*m n {4 ℕ.* t ℕ.* u} ℕP.0<1+n)
                     (ℤP.drop‿+≤+ (ℤP.≤-reflexive (solve 3 (λ t u n ->
                     con (+ 4) :* t :* u :* n := con (+ 2) :* t :* (con (+ 2) :* u :* n))
                     _≡_.refl (+ t) (+ u) (+ n)))))

            N₂≤4tun : N₂ ℕ.≤ 2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n)
            N₂≤4tun = ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃) N≤4tun)

            part2 : ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣ ℚ.≤ + 1 / (3 ℕ.* j)
            part2 = begin
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.* (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ) ∣     ≈⟨ ℚP.≃-trans (ℚP.*-congˡ {ℚ.∣ x₂ᵤₙ ∣} (ℚP.∣p*q∣≃∣p∣*∣q∣ z₂ₛₙ (y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ)))
                                                                    (ℚP.≃-sym (ℚP.*-assoc ℚ.∣ x₂ᵤₙ ∣ ℚ.∣ z₂ₛₙ ∣ ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣)) ⟩
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ∣ ℚ.* ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣ ≤⟨ ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣} _ (ℚP.≤-trans
                                                                    (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₂ₛₙ ∣} _
                                                                    (ℚP.<⇒≤ (canonical-greater x (2 ℕ.* u ℕ.* n))))
                                                                    (ℚP.*-monoʳ-≤-nonNeg {+ K x / 1} _
                                                                    (ℚP.<⇒≤ (canonical-greater z (2 ℕ.* s ℕ.* n))))) ⟩
              (+ (K x ℕ.* K z) / 1) ℚ.* ℚ.∣ y₄ᵣₛₙ ℚ.- y₄ₜᵤₙ ∣    ≤⟨ ℚP.*-monoʳ-≤-nonNeg {+ (K x ℕ.* K z) / 1} _
                                                                    (proj₂ (regular⇒cauchy y (K x ℕ.* K z ℕ.* (3 ℕ.* j)))
                                                                    (2 ℕ.* r ℕ.* (2 ℕ.* s ℕ.* n)) (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))
                                                                    N₂≤4rsn N₂≤4tun) ⟩
              (+ (K x ℕ.* K z) / 1) ℚ.*
              (+ 1 / (K x ℕ.* K z ℕ.* (3 ℕ.* j)))                ≈⟨ ℚ.*≡* (solve 3 (λ Kx Kz j ->
                                                                    (Kx :* Kz :* con (+ 1)) :* (con (+ 3) :* j) :=
                                                                    (con (+ 1) :* (con (+ 1) :* (Kx :* Kz :* (con (+ 3) :* j)))))
                                                                    _≡_.refl (+ K x) (+ K z) (+ j)) ⟩
              + 1 / (3 ℕ.* j)                                     ∎

            N₃≤2sn : N₃ ℕ.≤ 2 ℕ.* s ℕ.* n
            N₃≤2sn = ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂) N₃)
                     (ℕP.≤-trans (ℕP.<⇒≤ N<n) (ℕP.m≤n*m n {2 ℕ.* s} ℕP.0<1+n))

            N₃≤4tun : N₃ ℕ.≤ 2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n)
            N₃≤4tun = ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂) N₃) N≤4tun

            part3 : ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣ ℚ.≤ + 1 / (3 ℕ.* j)
            part3 = begin
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ y₄ₜᵤₙ ℚ.* (z₂ₛₙ ℚ.- z₄ₜᵤₙ) ∣     ≈⟨ ℚP.≃-trans (ℚP.*-congˡ {ℚ.∣ x₂ᵤₙ ∣} (ℚP.∣p*q∣≃∣p∣*∣q∣ y₄ₜᵤₙ (z₂ₛₙ ℚ.- z₄ₜᵤₙ)))
                                                                    (ℚP.≃-sym (ℚP.*-assoc ℚ.∣ x₂ᵤₙ ∣ ℚ.∣ y₄ₜᵤₙ ∣ ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣)) ⟩
              ℚ.∣ x₂ᵤₙ ∣ ℚ.* ℚ.∣ y₄ₜᵤₙ ∣ ℚ.* ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣ ≤⟨ ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣} _ (ℚP.≤-trans
                                                                    (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₄ₜᵤₙ ∣} _
                                                                    (ℚP.<⇒≤ (canonical-greater x (2 ℕ.* u ℕ.* n))))
                                                                    (ℚP.*-monoʳ-≤-nonNeg {+ K x / 1} _
                                                                    (ℚP.<⇒≤ (canonical-greater y (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n)))))) ⟩
              (+ (K x ℕ.* K y) / 1) ℚ.* ℚ.∣ z₂ₛₙ ℚ.- z₄ₜᵤₙ ∣      ≤⟨ ℚP.*-monoʳ-≤-nonNeg {+ (K x ℕ.* K y) / 1} _
                                                                     (proj₂ (regular⇒cauchy z (K x ℕ.* K y ℕ.* (3 ℕ.* j)))
                                                                     (2 ℕ.* s ℕ.* n) (2 ℕ.* t ℕ.* (2 ℕ.* u ℕ.* n))
                                                                     N₃≤2sn N₃≤4tun) ⟩
              (+ (K x ℕ.* K y) / 1) ℚ.*
              (+ 1 / (K x ℕ.* K y ℕ.* (3 ℕ.* j)))                 ≈⟨ ℚ.*≡* (solve 3 (λ Kx Ky j ->
                                                                     (((Kx :* Ky) :* con (+ 1)) :* (con (+ 3) :* j)) :=
                                                                     (con (+ 1) :* (con (+ 1) :* (Kx :* Ky :* (con (+ 3) :* j)))))
                                                                     _≡_.refl (+ K x) (+ K y) (+ j)) ⟩
              + 1 / (3 ℕ.* j)                                      ∎

*-distribˡ-+ : _DistributesOverˡ_ _≃_ _*_ _+_ 
*-distribˡ-+ x y z = lemma1B (x * (y + z)) ((x * y) + (x * z)) lemA
  where
    lemA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> N ℕ.< n ->
           ℚ.∣ seq (x * (y + z)) n ℚ.- seq ((x * y) + (x * z)) n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    lemA (suc k₁) = N , lemB
      where
        open ℚP.≤-Reasoning
        open import Data.Integer.Solver as ℤ-Solver
        open ℤ-Solver.+-*-Solver
        open import Data.Rational.Unnormalised.Solver as ℚ-Solver
        open ℚ-Solver.+-*-Solver using ()
          renaming
            ( solve to ℚsolve
            ; _:+_ to _ℚ:+_
            ; _:-_ to _ℚ:-_
            ; _:*_ to _ℚ:*_
            ; _:=_ to _ℚ:=_
            )
        j : ℕ
        j = suc k₁

        r : ℕ
        r = K x ℕ.⊔ K (y + z)

        s : ℕ
        s = K x ℕ.⊔ K y

        t : ℕ
        t = K x ℕ.⊔ K z

        N₁ : ℕ
        N₁ = proj₁ (regular⇒cauchy x (K y ℕ.* (4 ℕ.* j)))

        N₂ : ℕ
        N₂ = proj₁ (regular⇒cauchy y (K x ℕ.* (4 ℕ.* j)))

        N₃ : ℕ
        N₃ = proj₁ (regular⇒cauchy x (K z ℕ.* (4 ℕ.* j)))

        N₄ : ℕ
        N₄ = proj₁ (regular⇒cauchy z (K x ℕ.* (4 ℕ.* j)))

        N : ℕ
        N = N₁ ℕ.⊔ N₂ ℕ.⊔ N₃ ℕ.⊔ N₄

        lemB : ∀ (n : ℕ) -> N ℕ.< n ->
               ℚ.∣ seq (x * (y + z)) n ℚ.- seq ((x * y) + (x * z)) n ∣ ℚ.≤ + 1 / j
        lemB (suc k₂) N<n = begin
          ℚ.∣ x₂ᵣₙ ℚ.* (y₄ᵣₙ ℚ.+ z₄ᵣₙ) ℚ.-
            (x₄ₛₙ ℚ.* y₄ₛₙ ℚ.+ x₄ₜₙ ℚ.* z₄ₜₙ) ∣             ≈⟨ ℚP.∣-∣-cong (ℚsolve 7 (λ a b c d e f g ->
                                                               a ℚ:* (b ℚ:+ c) ℚ:- (d ℚ:* e ℚ:+ f ℚ:* g) ℚ:=
                                                               (b ℚ:* (a ℚ:- d) ℚ:+ (d ℚ:* (b ℚ:- e)) ℚ:+
                                                               ((c ℚ:* (a ℚ:- f)) ℚ:+ (f ℚ:* (c ℚ:- g)))))
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
                                                                                                 (ℚP.<⇒≤ (canonical-greater y
                                                                                                         (2 ℕ.* (2 ℕ.* r ℕ.* n)))))
                                                                            (ℚP.*-monoʳ-≤-nonNeg {+ K y / 1} _
                                                                                                 (proj₂ (regular⇒cauchy x (K y ℕ.* (4 ℕ.* j)))
                                                                                                 (2 ℕ.* r ℕ.* n) (2 ℕ.* s ℕ.* (2 ℕ.* n))
                                                                                                 (N₁≤ N≤2rn) (N₁≤ N≤4sn))))
                                                                            (ℚP.≤-trans
                                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₄ᵣₙ ℚ.- y₄ₛₙ ∣} _
                                                                                                 (ℚP.<⇒≤ (canonical-greater x
                                                                                                         (2 ℕ.* s ℕ.* (2 ℕ.* n)))))
                                                                            (ℚP.*-monoʳ-≤-nonNeg {+ K x / 1} _
                                                                                                 (proj₂ (regular⇒cauchy y (K x ℕ.* (4 ℕ.* j)))
                                                                                                 (2 ℕ.* (2 ℕ.* r ℕ.* n)) (2 ℕ.* s ℕ.* (2 ℕ.* n))
                                                                                                 (N₂≤ N≤4rn) (N₂≤ N≤4sn)))))
                                                                (ℚP.+-mono-≤
                                                                            (ℚP.≤-trans
                                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ᵣₙ ℚ.- x₄ₜₙ ∣} _
                                                                                                 (ℚP.<⇒≤ (canonical-greater z
                                                                                                         (2 ℕ.* (2 ℕ.* r ℕ.* n)))))
                                                                            (ℚP.*-monoʳ-≤-nonNeg {+ K z / 1} _
                                                                                                  (proj₂ (regular⇒cauchy x (K z ℕ.* (4 ℕ.* j)))
                                                                                                  (2 ℕ.* r ℕ.* n) (2 ℕ.* t ℕ.* (2 ℕ.* n))
                                                                                                  (N₃≤ N≤2rn) (N₃≤ N≤4tn))))
                                                                            (ℚP.≤-trans
                                                                            (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ z₄ᵣₙ ℚ.- z₄ₜₙ ∣} _
                                                                                                 (ℚP.<⇒≤ (canonical-greater x
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

            x₂ᵣₙ : ℚᵘ
            x₂ᵣₙ = seq x (2 ℕ.* r ℕ.* n)

            x₄ₛₙ : ℚᵘ
            x₄ₛₙ = seq x (2 ℕ.* s ℕ.* (2 ℕ.* n))

            x₄ₜₙ : ℚᵘ
            x₄ₜₙ = seq x (2 ℕ.* t ℕ.* (2 ℕ.* n))

            y₄ᵣₙ : ℚᵘ
            y₄ᵣₙ = seq y (2 ℕ.* (2 ℕ.* r ℕ.* n))

            y₄ₛₙ : ℚᵘ
            y₄ₛₙ = seq y (2 ℕ.* s ℕ.* (2 ℕ.* n))

            z₄ᵣₙ : ℚᵘ
            z₄ᵣₙ = seq z (2 ℕ.* (2 ℕ.* r ℕ.* n))

            z₄ₜₙ : ℚᵘ
            z₄ₜₙ = seq z (2 ℕ.* t ℕ.* (2 ℕ.* n))

            N≤2rn : N ℕ.≤ 2 ℕ.* r ℕ.* n
            N≤2rn = ℕP.≤-trans (ℕP.<⇒≤ N<n) (ℕP.m≤n*m n {2 ℕ.* r} ℕP.0<1+n)

            N≤4sn : N ℕ.≤ 2 ℕ.* s ℕ.* (2 ℕ.* n)
            N≤4sn = ℕP.≤-trans (ℕP.<⇒≤ N<n) (ℕP.≤-trans (ℕP.m≤n*m n {2 ℕ.* s ℕ.* 2} ℕP.0<1+n)
                    (ℕP.≤-reflexive (ℕP.*-assoc (2 ℕ.* s) 2 n)))

            N≤4rn : N ℕ.≤ 2 ℕ.* (2 ℕ.* r ℕ.* n)
            N≤4rn = ℕP.≤-trans (ℕP.<⇒≤ N<n) (ℕP.≤-trans (ℕP.m≤n*m n {2 ℕ.* (2 ℕ.* r)} ℕP.0<1+n)
                    (ℕP.≤-reflexive (ℕP.*-assoc 2 (2 ℕ.* r) n)))

            N≤4tn : N ℕ.≤ 2 ℕ.* t ℕ.* (2 ℕ.* n)
            N≤4tn = ℕP.≤-trans (ℕP.<⇒≤ N<n) (ℕP.≤-trans (ℕP.m≤n*m n {2 ℕ.* t ℕ.* 2} ℕP.0<1+n)
                    (ℕP.≤-reflexive (ℕP.*-assoc (2 ℕ.* t) 2 n)))

            N₁≤_ : {m : ℕ} -> N ℕ.≤ m -> N₁ ℕ.≤ m
            N₁≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃))
                     (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄) N≤m)

            N₂≤_ : {m : ℕ} -> N ℕ.≤ m -> N₂ ℕ.≤ m
            N₂≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂) N₃))
                     (ℕP.≤-trans (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄) N≤m)

            N₃≤_ : {m : ℕ} -> N ℕ.≤ m -> N₃ ℕ.≤ m
            N₃≤ N≤m = ℕP.≤-trans (ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂) N₃) (ℕP.m≤m⊔n (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄)) N≤m

            N₄≤_ : {m : ℕ} -> N ℕ.≤ m -> N₄ ℕ.≤ m
            N₄≤ N≤m = ℕP.≤-trans (ℕP.m≤n⊔m (N₁ ℕ.⊔ N₂ ℕ.⊔ N₃) N₄) N≤m

*-distribʳ-+ : _DistributesOverʳ_ _≃_ _*_ _+_
*-distribʳ-+ x y z = ≃-trans {(y + z) * x} {x * (y + z)} {y * x + z * x} (*-comm (y + z) x)
                    (≃-trans {x * (y + z)} {x * y + x * z} {y * x + z * x} (*-distribˡ-+ x y z)
                    (+-cong {x * y} {y * x} {x * z} {z * x} (*-comm x y) (*-comm x z)))

*-distrib-+ : _DistributesOver_ _≃_ _*_ _+_
*-distrib-+ = *-distribˡ-+ , *-distribʳ-+

*-identityˡ : LeftIdentity _≃_ 1ℝ _*_
*-identityˡ x (suc k₁) = begin
  ℚ.∣ ℚ.1ℚᵘ ℚ.* seq x (2 ℕ.* k ℕ.* n) ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- seq x n) (ℚP.*-identityˡ (seq x (2 ℕ.* k ℕ.* n)))) ⟩
  ℚ.∣ seq x (2 ℕ.* k ℕ.* n) ℚ.- seq x n ∣         ≤⟨ reg x (2 ℕ.* k ℕ.* n) n ⟩
  (+ 1 / (2 ℕ.* k ℕ.* n)) ℚ.+ (+ 1 / n)           ≤⟨ ℚP.+-monoˡ-≤ (+ 1 / n) lem ⟩
  (+ 1 / n) ℚ.+ (+ 1 / n)                         ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                           (con (+ 1) :* n :+ con (+ 1) :* n) :* n := (con (+ 2) :* (n :* n)))
                                                           _≡_.refl (+ n)) ⟩
  + 2 / n                                               ∎
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver
    open +-*-Solver
    k : ℕ
    k = K 1ℝ ℕ.⊔ K x

    n : ℕ
    n = suc k₁

    lem : (+ 1 / (2 ℕ.* k ℕ.* n)) ℚ.≤ + 1 / n
    lem = *≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ (ℕP.m≤n*m n {2 ℕ.* k} ℕP.0<1+n)))

*-identityʳ : RightIdentity _≃_ 1ℝ _*_
*-identityʳ x = ≃-trans {x * 1ℝ} {1ℝ * x} {x} (*-comm x 1ℝ) (*-identityˡ x)

*-identity : Identity _≃_ 1ℝ _*_
*-identity = *-identityˡ , *-identityʳ

*-zeroˡ : LeftZero _≃_ 0ℝ _*_
*-zeroˡ x (suc k₁) = begin
  ℚ.∣ 0ℚᵘ ℚ.* seq x (2 ℕ.* k ℕ.* n) ℚ.- 0ℚᵘ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- 0ℚᵘ) (ℚP.*-zeroˡ (seq x (2 ℕ.* k ℕ.* n)))) ⟩
  0ℚᵘ                                         ≤⟨ *≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ n))) (+≤+ ℕ.z≤n)) ⟩
  + 2 / n                                      ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

    k : ℕ
    k = K 0ℝ ℕ.⊔ K x

*-zeroʳ : RightZero _≃_ 0ℝ _*_
*-zeroʳ x = ≃-trans {x * 0ℝ} {0ℝ * x} {0ℝ} (*-comm x 0ℝ) (*-zeroˡ x)

*-zero : Zero _≃_ 0ℝ _*_
*-zero = *-zeroˡ , *-zeroʳ

-‿cong : Congruent₁ _≃_ (-_)
-‿cong {x} {y} x≃y n {n≢0}  = begin
  ℚ.∣ ℚ.- seq x n ℚ.- (ℚ.- seq y n) ∣ ≈⟨ ℚP.∣-∣-cong (solve 2 (λ x y -> :- x :- (:- y) := y :- x) ℚP.≃-refl (seq x n) (seq y n)) ⟩
  ℚ.∣ seq y n ℚ.- seq x n ∣           ≤⟨ (≃-symm {x} {y} x≃y) n {n≢0} ⟩
  + 2 / n                              ∎
  where
    open ℚP.≤-Reasoning
    open import Data.Rational.Unnormalised.Solver
    open +-*-Solver

neg-involutive : Involutive _≃_ (-_)
neg-involutive x (suc k₁) = begin
  ℚ.∣ ℚ.- (ℚ.- seq x (suc k₁)) ℚ.- seq x (suc k₁) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseˡ (ℚ.- seq x (suc k₁))) ⟩
  0ℚᵘ                                               ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / (suc k₁)                                     ∎
  where
    open ℚP.≤-Reasoning
    open import Data.Rational.Unnormalised.Solver
    open +-*-Solver

neg-distrib-+ : ∀ x y -> - (x + y) ≃ (- x) + (- y)
neg-distrib-+ x y (suc k₁) = begin
  ℚ.∣ ℚ.- (seq x (2 ℕ.* n) ℚ.+ seq y (2 ℕ.* n)) ℚ.-
      (ℚ.- seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n)) ∣   ≈⟨ ℚP.∣-∣-cong (solve 2 (λ x y ->
                                                       :- (x :+ y) :- (:- x :- y) := con (0ℚᵘ)) ℚP.≃-refl
                                                       (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  0ℚᵘ                                               ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                            ∎
  where
    open ℚP.≤-Reasoning
    open import Data.Rational.Unnormalised.Solver
    open +-*-Solver
    n : ℕ
    n = suc k₁

⊔-cong : Congruent₂ _≃_ _⊔_
⊔-cong {x} {z} {y} {w} x≃z y≃w (suc k₁) = [ left , right ]′ (ℚP.≤-total (seq x n ℚ.⊔ seq y n) (seq z n ℚ.⊔ seq w n))
  where
    open ℚP.≤-Reasoning
    open import Data.Rational.Unnormalised.Solver
    open +-*-Solver
    n : ℕ
    n = suc k₁

    lem : ∀ a b c d -> a ℚ.≤ b -> ℚ.∣ b ℚ.- d ∣ ℚ.≤ + 2 / n ->
          (a ℚ.⊔ b) ℚ.- (c ℚ.⊔ d) ℚ.≤ + 2 / n
    lem a b c d a≤b hyp = begin
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
          (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n)       ≤⟨ lem (seq z n) (seq w n) (seq x n) (seq y n) hyp2 (≃-symm {y} {w} y≃w n) ⟩
          + 2 / n                                            ∎

        wn≤zn : seq w n ℚ.≤ seq z n -> ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
        wn≤zn hyp2 = begin
          ℚ.∣ (seq x n ℚ.⊔ seq y n) ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ first ⟩
          (seq z n ℚ.⊔ seq w n) ℚ.- (seq x n ℚ.⊔ seq y n)       ≈⟨ ℚP.+-cong (ℚP.⊔-comm (seq z n) (seq w n)) (ℚP.-‿cong (ℚP.⊔-comm (seq x n) (seq y n))) ⟩
          (seq w n ℚ.⊔ seq z n) ℚ.- (seq y n ℚ.⊔ seq x n)       ≤⟨ lem (seq w n) (seq z n) (seq y n) (seq x n) hyp2 (≃-symm {x} {z} x≃z n) ⟩
          + 2 / n                                                ∎

    right : seq z n ℚ.⊔ seq w n ℚ.≤ seq x n ℚ.⊔ seq y n -> ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
    right hyp1 = [ xn≤yn , yn≤xn ]′ (ℚP.≤-total (seq x n) (seq y n))
      where
        xn≤yn : seq x n ℚ.≤ seq y n -> ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
        xn≤yn hyp2 = begin
          ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
          seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n)       ≤⟨ lem (seq x n) (seq y n) (seq z n) (seq w n) hyp2 (y≃w n) ⟩
          + 2 / n                                              ∎

        yn≤xn : seq y n ℚ.≤ seq x n -> ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ℚ.≤ + 2 / n
        yn≤xn hyp2 = begin
          ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp1) ⟩
          seq x n ℚ.⊔ seq y n ℚ.- (seq z n ℚ.⊔ seq w n)       ≈⟨ ℚP.+-cong (ℚP.⊔-comm (seq x n) (seq y n)) (ℚP.-‿cong (ℚP.⊔-comm (seq z n) (seq w n))) ⟩
          seq y n ℚ.⊔ seq x n ℚ.- (seq w n ℚ.⊔ seq z n)       ≤⟨ lem (seq y n) (seq x n) (seq w n) (seq z n) hyp2 (x≃z n) ⟩
          + 2 / n                                              ∎

⊔-congˡ : LeftCongruent _≃_ _⊔_
⊔-congˡ {x} {y} {z} y≃z = ⊔-cong {x} {x} {y} {z} (≃-refl {x}) y≃z

⊔-congʳ : RightCongruent _≃_ _⊔_
⊔-congʳ {x} {y} {z} y≃z = ⊔-cong {y} {z} {x} {x} y≃z (≃-refl {x})

⊔-comm : Commutative _≃_ _⊔_
⊔-comm x y n {n≢0} = begin
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq y n ℚ.⊔ seq x n) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (seq x n ℚ.⊔ seq y n) (ℚP.-‿cong (ℚP.⊔-comm (seq y n) (seq x n)))) ⟩
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.- (seq x n ℚ.⊔ seq y n) ∣ ≤⟨ ≃-refl {x ⊔ y} n {n≢0} ⟩
  + 2 / n                                              ∎
  where
    open ℚP.≤-Reasoning

⊔-assoc : Associative _≃_ _⊔_
⊔-assoc x y z n {n≢0} = begin
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n ℚ.- (seq x n ℚ.⊔ (seq y n ℚ.⊔ seq z n)) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ (seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n)
                                                                                              (ℚP.-‿cong (ℚP.≃-sym (ℚP.⊔-assoc (seq x n) (seq y n) (seq z n))))) ⟩
  ℚ.∣ seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n ℚ.- (seq x n ℚ.⊔ seq y n ℚ.⊔ seq z n) ∣   ≤⟨ ≃-refl {x ⊔ y ⊔ z} n {n≢0} ⟩
  + 2 / n                                                                       ∎
  where
    open ℚP.≤-Reasoning

_⊓_ : (x y : ℝ) -> ℝ
x ⊓ y = - ((- x) ⊔ (- y))

⊓-cong : Congruent₂ _≃_ _⊓_
⊓-cong {x} {z} {y} {w} x≃z y≃w = -‿cong {(- x ⊔ - y)} {(- z ⊔ - w)} (⊔-cong {(- x)} {(- z)} {(- y)} {(- w)}
                                        (-‿cong {x} {z} x≃z) (-‿cong {y} {w} y≃w))

⊓-congˡ : LeftCongruent _≃_ _⊓_
⊓-congˡ {x} {y} {z} y≃z = ⊓-cong {x} {x} {y} {z} (≃-refl {x}) y≃z

⊓-congʳ : RightCongruent _≃_ _⊓_
⊓-congʳ {x} {y} {z} y≃z = ⊓-cong {y} {z} {x} {x} y≃z (≃-refl {x})

⊓-comm : Commutative _≃_ _⊓_
⊓-comm x y = -‿cong { - x ⊔ - y} { - y ⊔ - x} (⊔-comm (- x) (- y))

⊓-assoc : Associative _≃_ _⊓_
⊓-assoc x y z = -‿cong {(- (- ((- x) ⊔ (- y)))) ⊔ (- z)} {(- x) ⊔ (- (- ((- y) ⊔ (- z))))}
                (≃-trans {(- (- ((- x) ⊔ (- y))) ⊔ (- z))} {((- x) ⊔ (- y)) ⊔ (- z)} {(- x) ⊔ (- (- ((- y) ⊔ (- z))))}
                (⊔-congʳ {(- z)} {(- (- ((- x) ⊔ (- y))))} {(- x) ⊔ (- y)} (neg-involutive ((- x) ⊔ (- y))))
                (≃-trans {((- x) ⊔ (- y)) ⊔ (- z)} {(- x) ⊔ ((- y) ⊔ (- z))} {(- x) ⊔ (- (- ((- y) ⊔ (- z))))}
                (⊔-assoc (- x) (- y) (- z)) (⊔-congˡ { - x} { - y ⊔ - z} { - (- (- y ⊔ - z))}
                (≃-symm { - (- (- y ⊔ - z))} { - y ⊔ - z} (neg-involutive ((- y) ⊔ (- z)))))))

∣_∣ : ℝ -> ℝ
∣ x ∣ = x ⊔ (- x)

∣-∣-cong : Congruent₁ _≃_ ∣_∣
∣-∣-cong {x} {y} x≃y = ⊔-cong {x} {y} {(- x)} {(- y)} x≃y (-‿cong {x} {y} x≃y)

∣p∣≃p⊔-p : ∀ p -> ℚ.∣ p ∣ ℚ.≃ p ℚ.⊔ (ℚ.- p)
∣p∣≃p⊔-p p = [ left , right ]′ (ℚP.∣p∣≡p∨∣p∣≡-p p)
  where
    open ℚP.≤-Reasoning
    left : ℚ.∣ p ∣ ≡ p -> ℚ.∣ p ∣ ℚ.≃ p ℚ.⊔ (ℚ.- p)
    left hyp = begin-equality
      ℚ.∣ p ∣      ≈⟨ ℚP.≃-reflexive hyp ⟩
      p            ≈⟨ ℚP.≃-sym (ℚP.p≥q⇒p⊔q≃p (ℚP.≤-trans (p≤∣p∣ (ℚ.- p)) (ℚP.≤-reflexive (ℚP.≃-trans (ℚP.∣-p∣≃∣p∣ p) (ℚP.≃-reflexive hyp))))) ⟩
      p ℚ.⊔ (ℚ.- p) ∎

    right : ℚ.∣ p ∣ ≡ ℚ.- p -> ℚ.∣ p ∣ ℚ.≃ p ℚ.⊔ (ℚ.- p)
    right hyp = begin-equality
      ℚ.∣ p ∣      ≈⟨ ℚP.≃-reflexive hyp ⟩
      ℚ.- p        ≈⟨ ℚP.≃-sym (ℚP.p≤q⇒p⊔q≃q (ℚP.≤-trans (p≤∣p∣ p) (ℚP.≤-reflexive (ℚP.≃-reflexive hyp)))) ⟩
      p ℚ.⊔ (ℚ.- p) ∎

-- Alternate definition of absolute value defined pointwise in the real number's regular sequence
∣_∣₂ : ℝ -> ℝ
seq ∣ x ∣₂ n = ℚ.∣ seq x n ∣
reg ∣ x ∣₂ m n {m≢0} {n≢0} = begin
  ℚ.∣ ℚ.∣ seq x m ∣ ℚ.- ℚ.∣ seq x n ∣ ∣ ≤⟨ ∣∣p∣-∣q∣∣≤∣p-q∣ (seq x m) (seq x n) ⟩
  ℚ.∣ seq x m ℚ.- seq x n ∣            ≤⟨ reg x m n {m≢0} {n≢0} ⟩
  (+ 1 / m) ℚ.+ (+ 1 / n)               ∎
  where
    open ℚP.≤-Reasoning

∣x∣≃∣x∣₂ : ∀ x -> ∣ x ∣ ≃ ∣ x ∣₂
∣x∣≃∣x∣₂ x (suc k₁) = begin
  ℚ.∣ (seq x n ℚ.⊔ (ℚ.- seq x n)) ℚ.- ℚ.∣ seq x n ∣ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- ℚ.∣ seq x n ∣) (ℚP.≃-sym (∣p∣≃p⊔-p (seq x n)))) ⟩
  ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- ℚ.∣ seq x n ∣ ∣               ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ ℚ.∣ seq x n ∣) ⟩
  0ℚᵘ                                                ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                             ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

-- K(x*y)
--K∣x∣ K∣y∣
-- ∣x₁∣ + 2
∣x*y∣≃∣x∣*∣y∣ : ∀ x y -> ∣ x * y ∣ ≃ ∣ x ∣ * ∣ y ∣
∣x*y∣≃∣x∣*∣y∣ x y = ≃-trans {∣ x * y ∣} {∣ x * y ∣₂} {∣ x ∣ * ∣ y ∣}
                   (∣x∣≃∣x∣₂ (x * y))
                   (≃-trans {∣ x * y ∣₂} {∣ x ∣₂ * ∣ y ∣₂} {∣ x ∣ * ∣ y ∣}
                   (lemma1B ∣ x * y ∣₂ (∣ x ∣₂ * ∣ y ∣₂) lemA)
                   (*-cong {∣ x ∣₂} {∣ x ∣} {∣ y ∣₂} {∣ y ∣}
                   (≃-symm {∣ x ∣} {∣ x ∣₂} (∣x∣≃∣x∣₂ x)) (≃-symm {∣ y ∣} {∣ y ∣₂} (∣x∣≃∣x∣₂ y))))
  where
    lemA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> N ℕ.< n ->
           ℚ.∣ seq (∣ x * y ∣₂) n ℚ.- seq (∣ x ∣₂ * ∣ y ∣₂) n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    lemA (suc k₁) = N , lemB                                                       
      where
        j : ℕ
        j = suc k₁

        r : ℕ
        r = K x ℕ.⊔ K y

        t : ℕ
        t = K ∣ x ∣₂ ℕ.⊔ K ∣ y ∣₂

        N₁ : ℕ
        N₁ = proj₁ (regular⇒cauchy x (K y ℕ.* (2 ℕ.* j)))

        N₂ : ℕ
        N₂ = proj₁ (regular⇒cauchy y (K x ℕ.* (2 ℕ.* j)))

        N : ℕ
        N = N₁ ℕ.⊔ N₂

        lemB : ∀ (n : ℕ) -> N ℕ.< n ->
               ℚ.∣ seq (∣ x * y ∣₂) n ℚ.- seq (∣ x ∣₂ * ∣ y ∣₂) n ∣ ℚ.≤ (+ 1 / j)
        lemB (suc k₁) N<n = begin
          ℚ.∣ ℚ.∣ x₂ᵣₙ ℚ.* y₂ᵣₙ ∣ ℚ.- ℚ.∣ x₂ₜₙ ∣ ℚ.* ℚ.∣ y₂ₜₙ ∣ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congʳ ℚ.∣ x₂ᵣₙ ℚ.* y₂ᵣₙ ∣
                                                                    (ℚP.-‿cong (ℚP.≃-sym (ℚP.∣p*q∣≃∣p∣*∣q∣ x₂ₜₙ y₂ₜₙ)))) ⟩
          ℚ.∣ ℚ.∣ x₂ᵣₙ ℚ.* y₂ᵣₙ ∣ ℚ.- ℚ.∣ x₂ₜₙ ℚ.* y₂ₜₙ ∣ ∣       ≤⟨ ∣∣p∣-∣q∣∣≤∣p-q∣ (x₂ᵣₙ ℚ.* y₂ᵣₙ) (x₂ₜₙ ℚ.* y₂ₜₙ) ⟩
          ℚ.∣ x₂ᵣₙ ℚ.* y₂ᵣₙ ℚ.- x₂ₜₙ ℚ.* y₂ₜₙ ∣                   ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ x y z w ->
                                                                     x ℚ:* y ℚ:- z ℚ:* w ℚ:=
                                                                     (y ℚ:* (x ℚ:- z) ℚ:+ z ℚ:* (y ℚ:- w)))
                                                                     ℚP.≃-refl x₂ᵣₙ y₂ᵣₙ x₂ₜₙ y₂ₜₙ) ⟩
          ℚ.∣ y₂ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₂ₜₙ) ℚ.+
              x₂ₜₙ ℚ.* (y₂ᵣₙ ℚ.- y₂ₜₙ) ∣                          ≤⟨ ℚP.∣p+q∣≤∣p∣+∣q∣ (y₂ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₂ₜₙ))
                                                                                     (x₂ₜₙ ℚ.* (y₂ᵣₙ ℚ.- y₂ₜₙ)) ⟩
          ℚ.∣ y₂ᵣₙ ℚ.* (x₂ᵣₙ ℚ.- x₂ₜₙ) ∣ ℚ.+
          ℚ.∣ x₂ₜₙ ℚ.* (y₂ᵣₙ ℚ.- y₂ₜₙ) ∣                          ≈⟨ ℚP.+-cong
                                                                     (ℚP.∣p*q∣≃∣p∣*∣q∣ y₂ᵣₙ (x₂ᵣₙ ℚ.- x₂ₜₙ))
                                                                     (ℚP.∣p*q∣≃∣p∣*∣q∣ x₂ₜₙ (y₂ᵣₙ ℚ.- y₂ₜₙ)) ⟩
          ℚ.∣ y₂ᵣₙ ∣ ℚ.* ℚ.∣ x₂ᵣₙ ℚ.- x₂ₜₙ ∣ ℚ.+
          ℚ.∣ x₂ₜₙ ∣ ℚ.* ℚ.∣ y₂ᵣₙ ℚ.- y₂ₜₙ ∣                      ≤⟨ ℚP.+-mono-≤
                                                                                (ℚP.≤-trans
                                                                                (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ x₂ᵣₙ ℚ.- x₂ₜₙ ∣} _
                                                                                                      (ℚP.<⇒≤ (canonical-greater y
                                                                                                              (2 ℕ.* r ℕ.* n))))
                                                                                (ℚP.*-monoʳ-≤-nonNeg {+ K y / 1} _
                                                                                                     (proj₂ (regular⇒cauchy x (K y ℕ.* (2 ℕ.* j)))
                                                                                                     (2 ℕ.* r ℕ.* n) (2 ℕ.* t ℕ.* n)
                                                                                                     (N₁≤ (N≤2kn r)) (N₁≤ (N≤2kn t)))))
                                                                                (ℚP.≤-trans
                                                                                (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ y₂ᵣₙ ℚ.- y₂ₜₙ ∣} _
                                                                                                     (ℚP.<⇒≤ (canonical-greater x
                                                                                                              (2 ℕ.* t ℕ.* n))))
                                                                                (ℚP.*-monoʳ-≤-nonNeg {+ K x / 1} _
                                                                                                     (proj₂ (regular⇒cauchy y (K x ℕ.* (2 ℕ.* j)))
                                                                                                     (2 ℕ.* r ℕ.* n) (2 ℕ.* t ℕ.* n)
                                                                                                     (N₂≤ (N≤2kn r)) (N₂≤ (N≤2kn t))))) ⟩
          (+ K y / 1) ℚ.* (+ 1 / (K y ℕ.* (2 ℕ.* j))) ℚ.+
          (+ K x / 1) ℚ.* (+ 1 / (K x ℕ.* (2 ℕ.* j)))             ≈⟨ ℚ.*≡* (solve 3 (λ Kx Ky j ->

          -- Function for solver
          ((Ky :* con (+ 1)) :* (con (+ 1) :* (Kx :* (con (+ 2) :* j))) :+ ((Kx :* con (+ 1)) :* (con (+ 1) :* (Ky :* (con (+ 2) :* j))))) :* j :=
          con (+ 1) :* ((con (+ 1) :* (Ky :* (con (+ 2) :* j))) :* (con (+ 1) :* (Kx :* (con (+ 2) :* j)))))
          _≡_.refl (+ K x) (+ K y) (+ j)) ⟩
          
          + 1 / j                                                        ∎
          where
            open ℚP.≤-Reasoning
            open import Data.Integer.Solver as ℤ-Solver
            open ℤ-Solver.+-*-Solver
            open import Data.Rational.Unnormalised.Solver as ℚ-Solver
            open ℚ-Solver.+-*-Solver using ()
              renaming
              ( solve to ℚsolve
              ; _:+_ to _ℚ:+_
              ; _:-_ to _ℚ:-_
              ; _:*_ to _ℚ:*_
              ; _:=_ to _ℚ:=_
              )
            n : ℕ
            n = suc k₁

            x₂ᵣₙ : ℚᵘ
            x₂ᵣₙ = seq x (2 ℕ.* r ℕ.* n)

            x₂ₜₙ : ℚᵘ
            x₂ₜₙ = seq x (2 ℕ.* t ℕ.* n)

            y₂ᵣₙ : ℚᵘ
            y₂ᵣₙ = seq y (2 ℕ.* r ℕ.* n)

            y₂ₜₙ : ℚᵘ
            y₂ₜₙ = seq y (2 ℕ.* t ℕ.* n)

            N≤2kn : ∀ (k : ℕ) -> {k ≢0} -> N ℕ.≤ 2 ℕ.* k ℕ.* n
            N≤2kn (suc k₂) = ℕP.≤-trans (ℕP.<⇒≤ N<n) (ℕP.m≤n*m n {2 ℕ.* (suc k₂)} ℕP.0<1+n)

            N₁≤ : {m : ℕ} -> N ℕ.≤ m -> N₁ ℕ.≤ m
            N₁≤ N≤m = ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) N≤m

            N₂≤ : {m : ℕ} -> N ℕ.≤ m -> N₂ ℕ.≤ m
            N₂≤ N≤m = ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) N≤m

{-
A bunch of algebraic bundles from the standard library. I've followed the conventions used
in the standard library's properties file for unnormalised rationals.

Sometimes we use copatterns so we can use implicit arguments (e.g. in ≃-isEquivalence's
definition). 

It's inconvenient, but some properties of ℝ might not work without implicit arguments.
For instance, if we use ≃-trans without its implicit arguments in ≃-isEquivalence below (so
just ≃-trans instead of ≃-trans {x} {y} {z}), Agda will give a constraint error.
-}
≃-isEquivalence : IsEquivalence _≃_
IsEquivalence.refl ≃-isEquivalence {x} = ≃-refl {x}
IsEquivalence.sym ≃-isEquivalence {x} {y} = ≃-symm {x} {y}
IsEquivalence.trans ≃-isEquivalence {x} {y} {z} = ≃-trans {x} {y} {z}

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
IsMagma.isEquivalence +-isMagma = ≃-isEquivalence
IsMagma.∙-cong +-isMagma {x} {y} {z} {w} = +-cong {x} {y} {z} {w}

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
IsGroup.isMonoid +-0-isGroup = +-0-isMonoid
IsGroup.inverse +-0-isGroup = +-inverse
IsGroup.⁻¹-cong +-0-isGroup {x} {y} = -‿cong {x} {y}

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
IsMagma.isEquivalence *-isMagma = ≃-isEquivalence
IsMagma.∙-cong *-isMagma {x} {y} {z} {w} = *-cong {x} {y} {z} {w}

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

{- Predicates about sign of real number and some properties -}
Positive : Pred ℝ 0ℓ
Positive x = ∃ λ (n : ℕ) -> seq x (suc n) ℚ.> + 1 / (suc n)

-- ∀n∈ℕ( xₙ ≥ -n⁻¹)
NonNegative : Pred ℝ 0ℓ
NonNegative x = (n : ℕ) -> {n≢0 : n ≢0} -> seq x n ℚ.≥ ℚ.- ((+ 1 / n) {n≢0})

p<q⇒0<q-p : ∀ {p q} -> p ℚ.< q -> 0ℚᵘ ℚ.< q ℚ.- p
p<q⇒0<q-p {p} {q} p<q = begin-strict
  0ℚᵘ     ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ p) ⟩
  p ℚ.- p <⟨ ℚP.+-monoˡ-< (ℚ.- p) p<q ⟩
  q ℚ.- p  ∎ 
  where
    open ℚP.≤-Reasoning

-- r < Np
-- r < (Np)/1 Original version
-- r < (N/1) * p
-- r/N < p
archimedean-ℚ₂ : ∀ (p r : ℚᵘ) -> ℚ.Positive p -> ∃ λ (N : ℕ) ->
                            r ℚ.< (+ N / 1) ℚ.* p
archimedean-ℚ₂ p r p>0 = N , (begin-strict
  r                          <⟨ proj₂ (archimedean-ℚ p r p>0) ⟩
  ((+ N) ℤ.* (↥ p)) / (↧ₙ p) ≈⟨ ℚ.*≡* (cong (λ x -> (+ N) ℤ.* (↥ p) ℤ.* x) (ℤP.*-identityˡ (↧ p))) ⟩
  (+ N / 1) ℚ.* p             ∎)
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver
    open +-*-Solver
    N : ℕ
    N = proj₁ (archimedean-ℚ p r p>0)

lemma2-8-1a : ∀ x -> Positive x -> ∃ λ (N : ℕ) -> ∀ (m : ℕ) -> m ℕ.≥ suc N ->
            seq x m ℚ.≥ + 1 / (suc N) 
lemma2-8-1a x (n-1 , xₙ>1/n) = N-1 , lem
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver as ℤ-Solver
    open ℤ-Solver.+-*-Solver
    open import Data.Rational.Unnormalised.Solver as ℚ-Solver
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _ℚ:+_
        ; _:-_ to _ℚ:-_
        ; _:*_ to _ℚ:*_
        ; _:=_ to _ℚ:=_
        )
    n : ℕ
    n = suc n-1

    pos : ℚ.Positive (seq x n ℚ.- (+ 1 / n))
    pos = 0<⇒pos (seq x n ℚ.- (+ 1 / n)) (p<q⇒0<q-p xₙ>1/n)

    N-1 : ℕ
    N-1 = proj₁ (archimedean-ℚ₂ (seq x n ℚ.- (+ 1 / n)) (+ 2 / 1) pos)

    
    N : ℕ
    N = suc N-1

    part1 : + 2 / 1 ℚ.≤ (+ N / 1) ℚ.* (seq x n ℚ.- (+ 1 / n))
    part1 = begin
      + 2 / 1                                 <⟨ proj₂ (archimedean-ℚ₂ (seq x n ℚ.- (+ 1 / n)) (+ 2 / 1) pos) ⟩
      (+ N-1) / 1 ℚ.* (seq x n ℚ.- (+ 1 / n)) ≤⟨ ℚP.*-monoˡ-≤-nonNeg {seq x n ℚ.- + 1 / n}
                                                 (ℚP.positive⇒nonNegative {seq x n ℚ.- + 1 / n} pos) {+ N-1 / 1} {+ N / 1}
                                                 (*≤* (ℤP.*-monoʳ-≤-nonNeg 1 (+≤+ (ℕP.n≤1+n N-1)))) ⟩
      (+ N / 1) ℚ.* (seq x n ℚ.- (+ 1 / n))    ∎

    part2 : + 2 / N ℚ.≤ seq x n ℚ.- (+ 1 / n)
    part2 = begin
      + 2 / N                                             ≈⟨ ℚ.*≡* (sym (ℤP.*-assoc (+ 2) (+ 1) (+ N))) ⟩
      (+ 2 / 1) ℚ.* (+ 1 / N)                             ≤⟨ ℚP.*-monoˡ-≤-nonNeg _ part1 ⟩
      (+ N / 1) ℚ.* (seq x n ℚ.- (+ 1 / n)) ℚ.* (+ 1 / N) ≈⟨ ℚ.*≡* (solve 3 (λ N p q ->
                                                             ((N :* p) :* con (+ 1)) :* q := (p :* ((con (+ 1) :* q) :* N)))
                                                             _≡_.refl (+ N) (↥ (seq x n ℚ.- (+ 1 / n))) (↧ (seq x n ℚ.- (+ 1 / n)))) ⟩
      seq x n ℚ.- (+ 1 / n)                                ∎

    part3 : + 1 / N ℚ.≤ seq x n ℚ.- (+ 1 / n) ℚ.- (+ 1 / N)
    part3 = begin
      + 1 / N                             ≈⟨ ℚ.*≡* (solve 1 (λ N ->
                                             con (+ 1) :* (N :* N) := (((con (+ 2) :* N) :+ (:- con (+ 1) :* N)) :* N)) _≡_.refl (+ N)) ⟩
      (+ 2 / N) ℚ.- (+ 1 / N)             ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- (+ 1 / N)) part2 ⟩
      seq x n ℚ.- (+ 1 / n) ℚ.- (+ 1 / N)  ∎

    lem : ∀ (m : ℕ) -> m ℕ.≥ N -> seq x m ℚ.≥ + 1 / N
    lem (suc k₂) N≤m = begin
      + 1 / N                               ≤⟨ part3 ⟩
      seq x n ℚ.- (+ 1 / n) ℚ.- (+ 1 / N)   ≤⟨ ℚP.+-monoʳ-≤ (seq x n ℚ.- (+ 1 / n)) {ℚ.- (+ 1 / N)} {ℚ.- (+ 1 / m)}
                                               (ℚP.neg-mono-≤ (*≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ N≤m)))) ⟩
      seq x n ℚ.- (+ 1 / n) ℚ.- (+ 1 / m)   ≤⟨ ℚP.≤-respˡ-≃ (ℚsolve 3 (λ a b c -> a ℚ:- (b ℚ:+ c) ℚ:= a ℚ:- b ℚ:- c) ℚP.≃-refl (seq x n) (+ 1 / n) (+ 1 / m))
                                                            (ℚP.+-monoʳ-≤ (seq x n) (ℚP.neg-mono-≤ (reg x n m))) ⟩
      seq x n ℚ.- ℚ.∣ seq x n ℚ.- seq x m ∣ ≤⟨ ℚP.+-monoʳ-≤ (seq x n) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x n ℚ.- seq x m))) ⟩
      seq x n ℚ.- (seq x n ℚ.- seq x m)     ≈⟨ ℚsolve 2 (λ a b -> a ℚ:- (a ℚ:- b) ℚ:= b) ℚP.≃-refl (seq x n) (seq x m) ⟩
      seq x m                                ∎
      where
        m : ℕ
        m = suc k₂

lemma2-8-1b : ∀ (x : ℝ) ->
              (∃ λ (N-1 : ℕ) -> ∀ (m : ℕ) -> m ℕ.≥ suc N-1 -> seq x m ℚ.≥ + 1 / (suc N-1)) ->
              Positive x
lemma2-8-1b x (N-1 , proof) = N , (begin-strict
  + 1 / (suc N) <⟨ ℚ.*<* (ℤP.*-monoˡ-<-pos 0 (+<+ (ℕP.n<1+n N))) ⟩
  + 1 / N       ≤⟨ proof (suc N) (ℕ.s≤s (ℕP.n≤1+n N-1)) ⟩
  seq x (suc N)  ∎)
  where
    open ℚP.≤-Reasoning
    N : ℕ
    N = suc N-1
-- xₙ ≥ -n⁻¹
-- Nonnegative x ⇒ ∀ n ∃ Nₙ ∀ m≥Nₙ (xₘ ≥ -n⁻¹)
lemma2-8-2a : ∀ (x : ℝ) -> NonNegative x -> ∀ (n : ℕ) -> {n≢0 : n ≢0} ->
                           ∃ λ (Nₙ : ℕ) -> Nₙ ≢0 ×
                           (∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq x m ℚ.≥ ℚ.- (+ 1 / n) {n≢0})
lemma2-8-2a x x≥0 (suc k₁) = n , _ , λ {(suc m) m≥n → ℚP.≤-trans (ℚP.neg-mono-≤ (*≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ m≥n)))) (x≥0 (suc m))}
  where
    n : ℕ
    n = suc k₁

archimedean-ℚ₃ : ∀ (p : ℚᵘ) -> ∀ (r : ℤ) -> ℚ.Positive p -> ∃ λ (N-1 : ℕ) -> r / (suc N-1) ℚ.< p
archimedean-ℚ₃ p r 0<p = ℕ.pred N , (begin-strict
  r / N                         ≈⟨ ℚP.≃-reflexive (ℚP./-cong (sym (ℤP.*-identityʳ r)) (sym (ℕP.*-identityˡ N)) _ _) ⟩
  (r / 1) ℚ.* (+ 1 / N)         <⟨ ℚP.*-monoˡ-<-pos {+ 1 / N} _ {r / 1} {(+ N / 1) ℚ.* p} (ℚP.<-trans (proj₂ (archimedean-ℚ₂ p (r / 1) 0<p))
                                   (ℚP.*-monoˡ-<-pos {p} 0<p {+ (ℕ.pred N) / 1} {+ N / 1} (ℚ.*<* (ℤP.*-monoʳ-<-pos 0 (+<+ (ℕP.n<1+n (ℕ.pred N))))))) ⟩
  (+ N / 1) ℚ.* p ℚ.* (+ 1 / N) ≈⟨ ℚ.*≡* (solve 3 (λ N n d ->
                                   ((N :* n) :* con (+ 1)) :* d := (n :* (con (+ 1) :* d :* N)))
                                   _≡_.refl (+ N) (↥ p) (↧ p)) ⟩
  p                              ∎)
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver
    open +-*-Solver
    N : ℕ
    N = suc (proj₁ (archimedean-ℚ₂ p (r / 1) 0<p))

-- y - ε ≤ x
-- y ≤ x
ℚ-≤-lemma : ∀ (x y : ℚᵘ) ->
            (∀ (j : ℕ) -> {j≢0 : j ≢0} -> y ℚ.- (+ 1 / j) {j≢0} ℚ.≤ x) ->
            y ℚ.≤ x
ℚ-≤-lemma x y hyp with ℚP.<-cmp y x
...               | tri< a ¬b ¬c = ℚP.<⇒≤ a
...               | tri≈ ¬a b ¬c = ℚP.≤-reflexive b
...               | tri> ¬a ¬b c = ⊥-elim (ℚP.<⇒≱ lem (hyp N))
  where
    open ℚP.≤-Reasoning
    open import Data.Rational.Unnormalised.Solver
    open +-*-Solver
    N : ℕ
    N = suc (proj₁ (archimedean-ℚ₃ (y ℚ.- x) (+ 1) (0<⇒pos (y ℚ.- x) (p<q⇒0<q-p c))))

    lem : x ℚ.< y ℚ.- (+ 1 / N)
    lem = begin-strict
      x                             ≈⟨ solve 2 (λ a b -> a := a :+ b :- b) ℚP.≃-refl x (+ 1 / N) ⟩
      x ℚ.+ (+ 1 / N) ℚ.- (+ 1 / N) <⟨ ℚP.+-monoˡ-< (ℚ.- (+ 1 / N))
                                       (ℚP.+-monoʳ-< x (proj₂ (archimedean-ℚ₃ (y ℚ.- x) (+ 1) (0<⇒pos (y ℚ.- x) (p<q⇒0<q-p c))))) ⟩
      x ℚ.+ (y ℚ.- x) ℚ.- (+ 1 / N) ≈⟨ solve 3 (λ a b c -> a :+ (b :- a) :- c := b :- c) ℚP.≃-refl x y (+ 1 / N) ⟩
      y ℚ.- (+ 1 / N)                ∎

{-
Proof of ̄if direction of Lemma 2.8.2:
  Let j∈ℤ⁺, let n = 2j, and let m = max{Nₙ, 2j}. Let k∈ℕ. We must show 
that xₖ ≥ -k⁻¹. We have:
              xₖ = xₘ - (xₘ - xₖ)
                 ≥ xₘ - ∣xₘ - xₖ∣ 
                 ≥ -n⁻¹ - ∣xₘ - xₖ∣   by assumption since m ≥ Nₙ
                 ≥ -n⁻¹ - (m⁻¹ + k⁻¹) by regularity of x
                 = -k⁻¹ - (m⁻¹ + n⁻¹)
                 ≥ -k⁻¹ - ((2j)⁻¹ + (2j)⁻¹)   since m ≥ 2j and n = 2j
                 = -k⁻¹ - 1/j.
Thus, for all j∈ℤ⁺, we have
                    xₖ ≥ -k⁻¹ - 1/j. 
Hence xₖ ≥ -k⁻¹, and we are done.                                      □                                     
-}
lemma2-8-2b : ∀ (x : ℝ) -> (∀ (n : ℕ) -> {n≢0 : n ≢0} ->
                           ∃ λ (Nₙ : ℕ) -> Nₙ ≢0 ×
                           (∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq x m ℚ.≥ ℚ.- (+ 1 / n) {n≢0})) ->
                           NonNegative x
lemma2-8-2b x hyp K {K≢0} = lemB K {K≢0} (lemA K {K≢0})
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver as ℤ-Solver
    open ℤ-Solver.+-*-Solver
    open import Data.Rational.Unnormalised.Solver as ℚ-Solver
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _ℚ:+_
        ; _:-_ to _ℚ:-_
        ; _:*_ to _ℚ:*_
        ; :-_ to ℚ:-_
        ; _:=_ to _ℚ:=_
        )

    lemA : ∀ (k : ℕ) -> {k≢0 : k ≢0} -> ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
           seq x k ℚ.≥ ℚ.- (+ 1 / k) {k≢0} ℚ.- (+ 1 / j) {j≢0}
    lemA (suc k₁) (suc k₂) = begin
      ℚ.- (+ 1 / k) ℚ.- (+ 1 / j)                 ≈⟨ ℚP.+-congʳ (ℚ.- (+ 1 / k)) {ℚ.- (+ 1 / j)} {ℚ.- ((+ 1 / (2 ℕ.* j)) ℚ.+ (+ 1 / (2 ℕ.* j)))}
                                                     (ℚP.-‿cong (ℚ.*≡* (solve 1 (λ j ->
                                                     con (+ 1) :* (con (+ 2) :* j :* (con (+ 2) :* j)) :=
                                                     ((con (+ 1) :* (con (+ 2) :* j) :+ con (+ 1) :* (con (+ 2) :* j)) :* j))
                                                     _≡_.refl (+ j)))) ⟩
      ℚ.- (+ 1 / k) ℚ.- ((+ 1 / n) ℚ.+ (+ 1 / n)) ≤⟨ ℚP.+-monoʳ-≤ (ℚ.- (+ 1 / k)) {ℚ.- ((+ 1 / n) ℚ.+ (+ 1 / n))} {ℚ.- ((+ 1 / m) ℚ.+ (+ 1 / n))}
                                                     (ℚP.neg-mono-≤ {(+ 1 / m) ℚ.+ (+ 1 / n)} {(+ 1 / n) ℚ.+ (+ 1 / n)}
                                                     (ℚP.+-monoˡ-≤ (+ 1 / n) {+ 1 / m} {+ 1 / n} (*≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ (ℕP.m≤n⊔m (suc Nₙ) n)))))) ⟩
      ℚ.- (+ 1 / k) ℚ.- ((+ 1 / m) ℚ.+ (+ 1 / n)) ≈⟨ ℚsolve 3 (λ x y z ->
                                                     ℚ:- x ℚ:- (y ℚ:+ z) ℚ:= ℚ:- z ℚ:- (y ℚ:+ x))
                                                     ℚP.≃-refl (+ 1 / k) (+ 1 / m) (+ 1 / n) ⟩
      ℚ.- (+ 1 / n) ℚ.- ((+ 1 / m) ℚ.+ (+ 1 / k)) ≤⟨ ℚP.+-mono-≤ (proj₂ (proj₂ (hyp n)) m (ℕP.≤-trans (ℕP.n≤1+n Nₙ) (ℕP.m≤m⊔n (suc Nₙ) n)))
                                                                 (ℚP.neg-mono-≤ (reg x m k)) ⟩
      seq x m ℚ.- ℚ.∣ seq x m ℚ.- seq x k ∣       ≤⟨ ℚP.+-monoʳ-≤ (seq x m) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x m ℚ.- seq x k))) ⟩
      seq x m ℚ.- (seq x m ℚ.- seq x k)           ≈⟨ ℚsolve 2 (λ x y -> x ℚ:- (x ℚ:- y) ℚ:= y) ℚP.≃-refl (seq x m) (seq x k) ⟩
      seq x k                                         ∎
      where
        k : ℕ
        k = suc k₁

        j : ℕ
        j = suc k₂

        n : ℕ
        n = 2 ℕ.* j

        Nₙ : ℕ
        Nₙ = proj₁ (hyp n)

        m : ℕ
        m = (suc Nₙ) ℕ.⊔ 2 ℕ.* j

    lemB : ∀ (k : ℕ) -> {k≢0 : k ≢0} -> (∀ (j : ℕ) -> {j≢0 : j ≢0} ->
           seq x k ℚ.≥ ℚ.- (+ 1 / k) {k≢0} ℚ.- (+ 1 / j) {j≢0}) ->
           seq x k ℚ.≥ ℚ.- (+ 1 / k) {k≢0}
    lemB (suc k₁) = ℚ-≤-lemma (seq x (suc k₁)) (ℚ.- (+ 1 / (suc k₁)))

{-
Proposition:
  If x is positive and x ≃ y, then y is positive.
Proof
  Since x is positive, there is N₁∈ℕ such that xₘ ≥ N₁⁻¹ for all m ≥ N.
Since x ≃ y, there is N₂∈ℕ such that, for all m > N₂, we have 
∣ xₘ - yₘ ∣ ≤ (2N₁)⁻¹. Let N = max{N₁, N₂} and let m ≥ 2N. Then N₁ ≤ N, so
N⁻¹ ≤ N₁⁻¹. We have:
yₘ ≥ xₘ - ∣ xₘ - yₘ ∣
   ≥ N₁⁻¹ - (2N₁)⁻¹
   = (2N₁)⁻¹
   ≥ (2N)⁻¹.
Thus yₘ ≥ (2N)⁻¹ for all m ≥ 2N. Hence y is positive.                   □
-}
pos-cong : ∀ x y -> x ≃ y -> Positive x -> Positive y
pos-cong x y x≃y posx = lemma2-8-1b y (ℕ.pred (2 ℕ.* N) , lemA)
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver as ℤ-Solver
    open ℤ-Solver.+-*-Solver
    open import Data.Rational.Unnormalised.Solver as ℚ-Solver
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:-_ to _ℚ:-_
        ; _:=_ to _ℚ:=_
        )
    N₁ : ℕ
    N₁ = suc (proj₁ (lemma2-8-1a x posx))

    N₂ : ℕ
    N₂ = proj₁ (lemma1A x y x≃y (2 ℕ.* N₁))

    N : ℕ
    N = N₁ ℕ.⊔ N₂

    lemA : ∀ (m : ℕ) -> m ℕ.≥ 2 ℕ.* N -> seq y m ℚ.≥ + 1 / (2 ℕ.* N)
    lemA m m≥2N = begin
      + 1 / (2 ℕ.* N)                       ≤⟨ *≤* (ℤP.*-monoˡ-≤-nonNeg 1 (ℤP.*-monoˡ-≤-nonNeg 2 (+≤+ (ℕP.m≤m⊔n N₁ N₂)))) ⟩
      + 1 / (2 ℕ.* N₁)                      ≈⟨ ℚ.*≡* (solve 1 (λ N₁ ->
                                               con (+ 1) :* (N₁ :* (con (+ 2) :* N₁)) :=
                                               (con (+ 1) :* (con (+ 2) :* N₁) :+ (:- con (+ 1)) :* N₁) :* (con (+ 2) :* N₁))
                                               _≡_.refl (+ N₁)) ⟩
      (+ 1 / N₁) ℚ.- (+ 1 / (2 ℕ.* N₁))     ≤⟨ ℚP.+-mono-≤
                                               (proj₂ (lemma2-8-1a x posx) m (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.<⇒≤ N<m)))
                                               (ℚP.neg-mono-≤ (proj₂ (lemma1A x y x≃y (2 ℕ.* N₁)) m
                                               (ℕP.<-transʳ (ℕP.m≤n⊔m N₁ N₂) N<m))) ⟩
      seq x m ℚ.- ℚ.∣ seq x m ℚ.- seq y m ∣ ≤⟨ ℚP.+-monoʳ-≤ (seq x m) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x m ℚ.- seq y m))) ⟩
      seq x m ℚ.- (seq x m ℚ.- seq y m)     ≈⟨ ℚsolve 2 (λ xₘ yₘ -> xₘ ℚ:- (xₘ ℚ:- yₘ) ℚ:= yₘ) ℚP.≃-refl (seq x m) (seq y m) ⟩
      seq y m                                ∎
        where
          N<m : N ℕ.< m
          N<m = ℕP.<-transˡ (ℕP.<-transˡ (ℕP.m<n+m N {N} ℕP.0<1+n)
                (ℤP.drop‿+≤+ (ℤP.≤-reflexive (solve 1 (λ N -> N :+ N := con (+ 2) :* N) _≡_.refl (+ N))))) m≥2N

{-
Let x be a positive real number. By Lemma 2.8.1, there is N∈ℕ such that
                           xₘ ≥ N⁻¹      (m ≥ N).
Let n∈ℕ and let Nₙ = N. Then:
              -n⁻¹ < 0
                   < N⁻¹
                   ≤ xₘ
for all m ≥ Nₙ. Hence x is nonnegative by Lemma 2.8.2.                □
-}
pos⇒nonNeg : ∀ x -> Positive x -> NonNegative x
pos⇒nonNeg x posx = lemma2-8-2b x lemA
  where
    open ℚP.≤-Reasoning
    N : ℕ
    N = suc (proj₁ (lemma2-8-1a x posx))

    lemA : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ∃ λ (Nₙ : ℕ) ->
          Nₙ ≢0 × ∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq x m ℚ.≥ ℚ.- (+ 1 / n) {n≢0}
    lemA (suc k₁) = N , _ , lemB
      where
        n : ℕ
        n = suc k₁

        test : ℚ.Negative (ℚ.- (+ 1 / n))
        test = _

        lemB : ∀ (m : ℕ) -> m ℕ.≥ N -> seq x m ℚ.≥ ℚ.- (+ 1 / n)
        lemB m m≥N = begin
          ℚ.- (+ 1 / n) <⟨ ℚP.negative⁻¹ _ ⟩
          0ℚᵘ           <⟨ ℚP.positive⁻¹ _ ⟩
          + 1 / N       ≤⟨ proj₂ (lemma2-8-1a x posx) m m≥N ⟩
          seq x m        ∎

{-
Proposition:
  If x and y are positive, then so is x + y.
Proof:
  By Lemma 2.8.1, there is N₁∈ℕ such that m ≥ N₁ implies xₘ ≥ N₂⁻¹. Similarly,
there is N₂∈ℕ such that m ≥ N₂ implies yₘ ≥ N₂⁻¹. Define N = max{N₁, N₂}, and
let m ≥ N. We have:
(x + y)ₘ = x₂ₘ + y₂ₘ
         ≥ N₁⁻¹ + N₂⁻¹
         ≥ N⁻¹ + N⁻¹
         ≥ N⁻¹.
Thus (x + y)ₘ ≥ N⁻¹ for all m ≥ N. By Lemma 2.8.1, x + y is positive.         □
-}
posx,y⇒posx+y : ∀ x y -> Positive x -> Positive y -> Positive (x + y)
posx,y⇒posx+y x y posx posy = lemma2-8-1b (x + y) (ℕ.pred N , lem)
  where
    open ℚP.≤-Reasoning
    N₁ : ℕ
    N₁ = suc (proj₁ (lemma2-8-1a x posx))

    N₂ : ℕ
    N₂ = suc (proj₁ (lemma2-8-1a y posy))

    N : ℕ
    N = N₁ ℕ.⊔ N₂

    lem : ∀ (m : ℕ) -> m ℕ.≥ N -> seq (x + y) m ℚ.≥ + 1 / N
    lem m m≥N = begin
      + 1 / N                             ≤⟨ ℚP.p≤p+q {+ 1 / N} {+ 1 / N} _ ⟩
      (+ 1 / N) ℚ.+ (+ 1 / N)             ≤⟨ ℚP.+-mono-≤ {+ 1 / N} {+ 1 / N₁} {+ 1 / N} {+ 1 / N₂}
                                             (*≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ (ℕP.m≤m⊔n N₁ N₂))))
                                             (*≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ (ℕP.m≤n⊔m N₁ N₂)))) ⟩
      (+ 1 / N₁) ℚ.+ (+ 1 / N₂)           ≤⟨ ℚP.+-mono-≤ {+ 1 / N₁} {seq x (2 ℕ.* m)} {+ 1 / N₂} {seq y (2 ℕ.* m)}
                                             (proj₂ (lemma2-8-1a x posx) (2 ℕ.* m)
                                             (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.≤-trans m≥N (ℕP.m≤n*m m {2} ℕP.0<1+n))))
                                             (proj₂ (lemma2-8-1a y posy) (2 ℕ.* m)
                                             (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.≤-trans m≥N (ℕP.m≤n*m m {2} ℕP.0<1+n)))) ⟩
      seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m)  ∎

nonNegx,y⇒nonNegx+y : ∀ x y -> NonNegative x -> NonNegative y -> NonNegative (x + y)
nonNegx,y⇒nonNegx+y x y nonx nony = lemma2-8-2b (x + y) lemA
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver
    open +-*-Solver
    lemA : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ∃ λ (Nₙ : ℕ) -> Nₙ ≢0 × ∀ (m : ℕ) -> m ℕ.≥ Nₙ ->
          seq (x + y) m ℚ.≥ ℚ.- (+ 1 / n) {n≢0}
    lemA (suc k₁) = N , _ , lemB
      where
        n : ℕ
        n = suc k₁

        Nx : ℕ
        Nx = proj₁ (lemma2-8-2a x nonx (2 ℕ.* n))

        Ny : ℕ
        Ny = proj₁ (lemma2-8-2a y nony (2 ℕ.* n))

        N : ℕ
        N = Nx ℕ.⊔ Ny

        lemB : ∀ (m : ℕ) -> m ℕ.≥ N -> seq (x + y) m ℚ.≥ ℚ.- (+ 1 / n)
        lemB m m≥N = begin
          ℚ.- (+ 1 / n)                               ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                         (:- con (+ 1)) :* (con (+ 2) :* n :* (con (+ 2) :* n)) :=
                                                         (((:- con (+ 1)) :* (con (+ 2) :* n) :+ ((:- con (+ 1)) :* (con (+ 2) :* n))) :* n))
                                                         _≡_.refl (+ n)) ⟩
          ℚ.- (+ 1 / (2 ℕ.* n)) ℚ.- (+ 1 / (2 ℕ.* n)) ≤⟨ ℚP.+-mono-≤
                                                         (proj₂ (proj₂ (lemma2-8-2a x nonx (2 ℕ.* n))) (2 ℕ.* m)
                                                                (ℕP.≤-trans (ℕP.m≤m⊔n Nx Ny) (ℕP.≤-trans m≥N (ℕP.m≤n*m m {2} ℕP.0<1+n))))
                                                         (proj₂ (proj₂ (lemma2-8-2a y nony (2 ℕ.* n))) (2 ℕ.* m)
                                                                (ℕP.≤-trans (ℕP.m≤n⊔m Nx Ny) (ℕP.≤-trans m≥N (ℕP.m≤n*m m {2} ℕP.0<1+n)))) ⟩
          seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m)          ∎

{-
Suppose x≃y and x is nonnegative. WTS y is nonnegative. Then, for each n∈ℕ, there is
Nₙ∈ℕ such that m≥Nₙ implies xₘ ≥ -n⁻¹. Thus there is N₁∈ℕ such that m ≥ N₁ implies
xₘ ≥ -(2n)⁻¹. Since x ≃ y, there is N₂∈ℕ such that m ≥ N₂ implies ∣xₘ - yₘ∣ ≤ (2n)⁻¹.
Let N = max{N₁, N₂} and let m ≥ N. We have:
yₘ ≥ xₘ - ∣xₘ - yₘ∣
   ≥ -(2n)⁻¹ -  (2n)⁻¹
   = -n⁻¹,
so yₘ ≥ -n⁻¹ for all m ≥ N. Thus y is nonnegative.                                □
-}

nonNeg-cong : ∀ x y -> x ≃ y -> NonNegative x -> NonNegative y
nonNeg-cong x y x≃y nonx = lemma2-8-2b y lemA
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver as ℤ-Solver
    open ℤ-Solver.+-*-Solver
    open import Data.Rational.Unnormalised.Solver as ℚ-Solver
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:+_ to _ℚ:+_
        ; _:-_ to _ℚ:-_
        ; _:=_ to _ℚ:=_
        )

    lemA : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ∃ λ (Nₙ : ℕ) -> Nₙ ≢0 ×
           ∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq y m ℚ.≥ ℚ.- (+ 1 / n)
    lemA (suc k₁) = N , _ , lemB
      where
        n : ℕ
        n = suc k₁
        
        N₁ : ℕ
        N₁ = proj₁ (lemma2-8-2a x nonx (2 ℕ.* n))

        N₂ : ℕ
        N₂ = proj₁ (lemma1A x y x≃y (2 ℕ.* n))

        N : ℕ
        N = suc (N₁ ℕ.⊔ N₂)

        lemB : ∀ (m : ℕ) -> m ℕ.≥ N -> seq y m ℚ.≥ ℚ.- (+ 1 / n)
        lemB m m≥N = begin
          ℚ.- (+ 1 / n)                               ≈⟨ ℚ.*≡* (solve 1 (λ n ->
                                                         (:- con (+ 1)) :* (con (+ 2) :* n :* (con (+ 2) :* n)) :=
                                                         (((:- con (+ 1)) :* (con (+ 2) :* n) :+ ((:- con (+ 1)) :* (con (+ 2) :* n))) :* n))
                                                         _≡_.refl (+ n)) ⟩
          ℚ.- (+ 1 / (2 ℕ.* n)) ℚ.- (+ 1 / (2 ℕ.* n)) ≤⟨ ℚP.+-mono-≤
                                                         (proj₂ (proj₂ (lemma2-8-2a x nonx (2 ℕ.* n))) m
                                                         (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.≤-trans (ℕP.n≤1+n (N₁ ℕ.⊔ N₂)) m≥N)))
                                                         (ℚP.neg-mono-≤ (proj₂ (lemma1A x y x≃y (2 ℕ.* n)) m (ℕP.<-transʳ (ℕP.m≤n⊔m N₁ N₂) m≥N))) ⟩
          seq x m ℚ.- ℚ.∣ seq x m ℚ.- seq y m ∣       ≤⟨ ℚP.+-monoʳ-≤ (seq x m) (ℚP.neg-mono-≤ (p≤∣p∣ (seq x m ℚ.- seq y m))) ⟩
          seq x m ℚ.- (seq x m ℚ.- seq y m)           ≈⟨ ℚsolve 2 (λ x y -> x ℚ:- (x ℚ:- y) ℚ:= y) ℚP.≃-refl (seq x m) (seq y m) ⟩
          seq y m                                      ∎

{-
Proposition:
  If x is positive and y is nonnegative, then x + y is positive.
Proof:
  Since x is positive, there is an N₁∈ℕ such that xₘ ≥ N₁⁻¹ for all m ≥ N₁. Since y is
nonnegative, there is N₂∈ℕ such that, for all m ≥ N₂, we have yₘ ≥ -(2N₁)⁻¹. Let N = 2max{N₁, N₂}.
Let m ≥ N ≥ N₁, N₂. We have:
(x + y)ₘ  = x₂ₘ + y₂ₘ
          ≥ N₁⁻¹ - (2N₁)⁻¹
          = (2N₁)⁻¹.
          ≥ N⁻¹.
Thus (x + y)ₘ ≥ N⁻¹ for all m ≥ N. By Lemma 2.8.1, x + y is positive.                           □
-}
posx∧nonNegy⇒posx+y : ∀ x y -> Positive x -> NonNegative y -> Positive (x + y)
posx∧nonNegy⇒posx+y x y posx nony = lemma2-8-1b (x + y) (ℕ.pred N , lem)
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver
    open +-*-Solver
    N₁ : ℕ
    N₁ = suc (proj₁ (lemma2-8-1a x posx))

    N₂ : ℕ
    N₂ = proj₁ (lemma2-8-2a y nony (2 ℕ.* N₁))

    N : ℕ
    N = 2 ℕ.* (N₁ ℕ.⊔ N₂)

    lem : ∀ (m : ℕ) -> m ℕ.≥ N -> seq (x + y) m ℚ.≥ + 1 / N
    lem m m≥N = begin
      + 1 / N                             ≤⟨ *≤* (ℤP.*-monoˡ-≤-nonNeg 1 (ℤP.*-monoˡ-≤-nonNeg 2 (+≤+ (ℕP.m≤m⊔n N₁ N₂)))) ⟩
      + 1 / (2 ℕ.* N₁)                    ≈⟨ ℚ.*≡* (solve 1 (λ N₁ ->
                                             con (+ 1) :* (N₁ :* (con (+ 2) :* N₁)) :=
                                             (con (+ 1) :* (con (+ 2) :* N₁) :+ (:- con (+ 1)) :* N₁) :* (con (+ 2) :* N₁))
                                             _≡_.refl (+ N₁)) ⟩
      (+ 1 / N₁) ℚ.- (+ 1 / (2 ℕ.* N₁))   ≤⟨ ℚP.+-mono-≤ (proj₂ (lemma2-8-1a x posx) (2 ℕ.* m)
                                             (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) (ℕP.≤-trans (ℕP.m≤n*m (N₁ ℕ.⊔ N₂) {2} ℕP.0<1+n)
                                             (ℕP.≤-trans m≥N (ℕP.m≤n*m m {2} ℕP.0<1+n)))))
                                             (proj₂ (proj₂ (lemma2-8-2a y nony (2 ℕ.* N₁))) (2 ℕ.* m)
                                             (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) (ℕP.≤-trans (ℕP.m≤n*m (N₁ ℕ.⊔ N₂) {2} ℕP.0<1+n)
                                             (ℕP.≤-trans m≥N (ℕP.m≤n*m m {2} ℕP.0<1+n))))) ⟩
      seq x (2 ℕ.* m) ℚ.+ seq y (2 ℕ.* m)  ∎

∣x∣nonNeg : ∀ x -> NonNegative ∣ x ∣
∣x∣nonNeg x = nonNeg-cong ∣ x ∣₂ ∣ x ∣ (≃-symm {∣ x ∣} {∣ x ∣₂} (∣x∣≃∣x∣₂ x)) λ {(suc k₁) -> ℚP.≤-trans (ℚP.nonPositive⁻¹ _) (ℚP.0≤∣p∣ (seq x (suc k₁)))}

{-
Module for chain of equality reasoning on ℝ
-}
module ≃-Reasoning where
  open import Relation.Binary.Reasoning.Setoid ≃-setoid
    public

{-
Proposition:
  If x is nonnegative, then ∣x∣ = x.
Proof:
  Let j∈ℕ. Since x is nonnegative, there is N∈ℕ such that
                         xₘ ≥ -(2j)⁻¹         (m ≥ N).
Let m ≥ N. Then -2xₘ ≤ j⁻¹. Either xₘ ≥ 0 or xₘ < 0.
Case 1: Suppose xₘ ≥ 0. Then:
     ∣∣xₘ∣ - xₘ∣ = ∣xₘ∣ - xₘ
                = xₘ - xₘ
                = 0
                ≤ j⁻¹

Case 2: Suppose xₘ < 0. Then:
     ∣∣xₘ∣ - xₘ∣ = ∣xₘ∣ - xₘ
                = -xₘ - xₘ
                = -2xₘ
                ≤ j⁻¹.
Thus ∣∣xₘ∣ - xₘ∣ ≤ j⁻¹ for all m ≥ N. By Lemma 1, ∣x∣ = x. □
-}
nonNegx⇒∣x∣₂≃x : ∀ x -> NonNegative x -> ∣ x ∣₂ ≃ x
nonNegx⇒∣x∣₂≃x x nonx = lemma1B ∣ x ∣₂ x lemA
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver
    open +-*-Solver
    lemA : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> N ℕ.< n ->
          ℚ.∣ seq ∣ x ∣₂ n ℚ.- seq x n ∣ ℚ.≤ (+ 1 / j) {j≢0}
    lemA (suc k₁) = N , lemB
      where
        j : ℕ
        j = suc k₁

        N : ℕ
        N = proj₁ (lemma2-8-2a x nonx (2 ℕ.* j))

        lemB : ∀ (n : ℕ) -> N ℕ.< n -> ℚ.∣ seq ∣ x ∣₂ n ℚ.- seq x n ∣ ℚ.≤ + 1 / j
        lemB (suc k₂) N<n = [ left , right ]′ (ℚP.≤-total (seq x n) 0ℚᵘ)
          where
            n : ℕ
            n = suc k₂

            -xₙ≤1/2j : ℚ.- seq x n ℚ.≤ + 1 / (2 ℕ.* j)
            -xₙ≤1/2j = begin
              ℚ.- seq x n                 ≤⟨ ℚP.neg-mono-≤ (proj₂ (proj₂ (lemma2-8-2a x nonx (2 ℕ.* j))) n (ℕP.<⇒≤ N<n)) ⟩
              ℚ.- (ℚ.- (+ 1 / (2 ℕ.* j))) ≈⟨ ℚP.neg-involutive (+ 1 / (2 ℕ.* j)) ⟩
              + 1 / (2 ℕ.* j)              ∎

            left : seq x n ℚ.≤ 0ℚᵘ -> ℚ.∣ seq ∣ x ∣₂ n ℚ.- seq x n ∣ ℚ.≤ + 1 / j
            left hyp = begin
              ℚ.∣ seq ∣ x ∣₂ n ℚ.- seq x n ∣          ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p (p≤∣p∣ (seq x n))) ⟩
              ℚ.∣ seq x n ∣ ℚ.- seq x n               ≈⟨ ℚP.+-congˡ (ℚ.- seq x n) (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (seq x n))) ⟩
              ℚ.∣ ℚ.- seq x n ∣ ℚ.- seq x n           ≈⟨ ℚP.+-congˡ (ℚ.- seq x n) (ℚP.0≤p⇒∣p∣≃p (ℚP.neg-mono-≤ hyp)) ⟩
              ℚ.- seq x n ℚ.- seq x n                 ≤⟨ ℚP.+-mono-≤ -xₙ≤1/2j -xₙ≤1/2j ⟩
              (+ 1 / (2 ℕ.* j)) ℚ.+ (+ 1 / (2 ℕ.* j)) ≈⟨ ℚ.*≡* (solve 1 (λ j ->
                                                         (con (+ 1) :* (con (+ 2) :* j) :+ con (+ 1) :* (con (+ 2) :* j)) :* j :=
                                                         (con (+ 1) :* (con (+ 2) :* j :* (con (+ 2) :* j)))) _≡_.refl (+ j)) ⟩
              + 1 / j                                  ∎

            right : 0ℚᵘ ℚ.≤ seq x n -> ℚ.∣ seq ∣ x ∣₂ n ℚ.- seq x n ∣ ℚ.≤ + 1 / j
            right hyp = begin
              ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- seq x n ∣  ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p (p≤∣p∣ (seq x n))) ⟩
              ℚ.∣ seq x n ∣ ℚ.- seq x n       ≈⟨ ℚP.+-congˡ (ℚ.- seq x n) (ℚP.0≤p⇒∣p∣≃p hyp) ⟩
              seq x n ℚ.- seq x n             ≈⟨ ℚP.+-inverseʳ (seq x n) ⟩
              0ℚᵘ                             ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
              + 1 / j                          ∎
     
nonNegx⇒∣x∣≃x : ∀ x -> NonNegative x -> ∣ x ∣ ≃ x
nonNegx⇒∣x∣≃x x nonx = ≃-trans {∣ x ∣} {∣ x ∣₂} {x} (∣x∣≃∣x∣₂ x) (nonNegx⇒∣x∣₂≃x x nonx)

{-
Proposition:
  If x and y are nonnegative, then so is x * y.
Proof:
  Since x and y are nonnegative, we have x = ∣x∣ and y = ∣y∣. Then x*y = ∣x∣*∣y∣ = ∣x*y∣, which is nonnegative. □
-}
nonNegx,y⇒nonNegx*y : ∀ x y -> NonNegative x -> NonNegative y -> NonNegative (x * y)
nonNegx,y⇒nonNegx*y x y nonx nony = nonNeg-cong ∣ x * y ∣ (x * y) lem (∣x∣nonNeg (x * y))
  where
    open ≃-Reasoning
    lem : ∣ x * y ∣ ≃ x * y
    lem = begin
      ∣ x * y ∣     ≈⟨ ∣x*y∣≃∣x∣*∣y∣ x y ⟩
      ∣ x ∣ * ∣ y ∣ ≈⟨ *-cong {∣ x ∣} {x} {∣ y ∣} {y} (nonNegx⇒∣x∣≃x x nonx) (nonNegx⇒∣x∣≃x y nony) ⟩
      x * y          ∎
      
{-
Proposition:
  If x and y are positive, then so is x * y.
Proof:
  By Lemma 2.8.1, there exists N₁,N₂∈ℕ such that
                    xₘ ≥ N₁⁻¹                (m ≥ N₁), and
                    yₘ ≥ N₂⁻¹                (m ≥ N₂).
Let N = max{N₁, N₂} and let m ≥ N². We have:
           x₂ₖₘy₂ₖₘ ≥ N₁⁻¹N₂⁻¹
                    ≥ N⁻¹ * N⁻¹
                    = (N²)⁻¹,
so x₂ₖₘy₂ₖₘ ≥ (N²)⁻¹ for all m ≥ N². By Lemma 2.8.1, x * y is
positive.                                                   □

-}
posx,y⇒posx*y : ∀ x y -> Positive x -> Positive y -> Positive (x * y)
posx,y⇒posx*y x y posx posy = lemma2-8-1b (x * y) (ℕ.pred (N ℕ.* N) , lem)
  where
    open ℚP.≤-Reasoning
    k : ℕ
    k = K x ℕ.⊔ K y

    N₁ : ℕ
    N₁ = suc (proj₁ (lemma2-8-1a x posx))

    N₂ : ℕ
    N₂ = suc (proj₁ (lemma2-8-1a y posy))

    N : ℕ
    N = N₁ ℕ.⊔ N₂

    lem : ∀ (m : ℕ) -> m ℕ.≥ N ℕ.* N -> seq (x * y) m ℚ.≥ + 1 / (N ℕ.* N)
    lem m m≥N² = begin
      + 1 / (N ℕ.* N)                                 ≡⟨ _≡_.refl ⟩
      (+ 1 / N) ℚ.* (+ 1 / N)                         ≤⟨ ℚP.≤-trans
                                                         (ℚP.*-monoˡ-≤-nonNeg {+ 1 / N} _ {+ 1 / N} {+ 1 / N₁}
                                                         (*≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ (ℕP.m≤m⊔n N₁ N₂)))))
                                                         (ℚP.*-monoʳ-≤-nonNeg {+ 1 / N₁} _ {+ 1 / N} {+ 1 / N₂}
                                                         (*≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ (ℕP.m≤n⊔m N₁ N₂))))) ⟩
      (+ 1 / N₁) ℚ.* (+ 1 / N₂)                       ≤⟨ ℚP.≤-trans
                                                         (ℚP.*-monoˡ-≤-nonNeg {+ 1 / N₂} _ {+ 1 / N₁} {seq x (2 ℕ.* k ℕ.* m)}
                                                         (proj₂ (lemma2-8-1a x posx) (2 ℕ.* k ℕ.* m)
                                                         (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) N≤2km)))
                                                         (ℚP.*-monoʳ-≤-pos {seq x (2 ℕ.* k ℕ.* m)} posx₂ₖₘ {+ 1 / N₂}
                                                         {seq y (2 ℕ.* k ℕ.* m)}
                                                         (proj₂ (lemma2-8-1a y posy) (2 ℕ.* k ℕ.* m)
                                                         (ℕP.≤-trans (ℕP.m≤n⊔m N₁ N₂) N≤2km))) ⟩
      seq x (2 ℕ.* k ℕ.* m) ℚ.* seq y (2 ℕ.* k ℕ.* m)  ∎
        where
          N≤2km : N ℕ.≤ 2 ℕ.* k ℕ.* m
          N≤2km = ℕP.≤-trans (ℕP.m≤n*m N {N} ℕP.0<1+n) (ℕP.≤-trans m≥N² (ℕP.m≤n*m m {2 ℕ.* k} ℕP.0<1+n))

          posx₂ₖₘ : ℚ.Positive (seq x (2 ℕ.* k ℕ.* m))
          posx₂ₖₘ = 0<⇒pos (seq x (2 ℕ.* k ℕ.* m)) (ℚP.<-≤-trans {0ℚᵘ} {+ 1 / N₁} {seq x (2 ℕ.* k ℕ.* m)}
                    (ℚP.positive⁻¹ _) (proj₂ (lemma2-8-1a x posx) (2 ℕ.* k ℕ.* m) (ℕP.≤-trans (ℕP.m≤m⊔n N₁ N₂) N≤2km)))

{-
Proposition:
  If x is positive and y is any real number, then max{x, y} is positive.
Proof:
  Since x is positive, there is N∈ℕ such that m ≥ N implies xₘ ≥ N⁻¹. Let
m ≥ N. We have:
(x ⊔ y)ₘ = xₘ ⊔ yₘ
         ≥ xₘ 
         ≥ N⁻¹.
-}
posx⇒posx⊔y : ∀ x y -> Positive x -> Positive (x ⊔ y)
posx⇒posx⊔y x y posx = lemma2-8-1b (x ⊔ y) (ℕ.pred N , lem)
  where
    open ℚP.≤-Reasoning
    N : ℕ
    N = suc (proj₁ (lemma2-8-1a x posx))

    lem : ∀ (m : ℕ) -> m ℕ.≥ N -> seq (x ⊔ y) m ℚ.≥ + 1 / N
    lem m m≥N = begin
      + 1 / N             ≤⟨ proj₂ (lemma2-8-1a x posx) m m≥N ⟩
      seq x m             ≤⟨ ℚP.p≤p⊔q (seq x m) (seq y m) ⟩
      seq x m ℚ.⊔ seq y m  ∎

{-
Proposition:
  If x is nonnegative and y is any real number, then max{x, y} is nonnegative.
Proof:
  Since x is nonnegative, for each n∈ℕ there is Nₙ∈ℕ such that xₘ ≥ -n⁻¹ for all
m ≥ Nₙ. Let m ≥ Nₙ. Then:
(x ⊔ y)ₘ = xₘ ⊔ yₘ
         ≥ xₘ
         ≥ -n⁻¹.
-}
nonNegx⇒nonNegx⊔y : ∀ x y -> NonNegative x -> NonNegative (x ⊔ y)
nonNegx⇒nonNegx⊔y x y nonx = lemma2-8-2b (x ⊔ y) lemA
  where
    open ℚP.≤-Reasoning
    lemA : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ∃ λ (Nₙ : ℕ) -> Nₙ ≢0 ×
           ∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq (x ⊔ y) m ℚ.≥ ℚ.- (+ 1 / n) {n≢0}
    lemA n {n≢0} = Nₙ , proj₁ (proj₂ (lemma2-8-2a x nonx n {n≢0})) , lemB
      where
        Nₙ : ℕ
        Nₙ = proj₁ (lemma2-8-2a x nonx n {n≢0})

        lemB : ∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq (x ⊔ y) m ℚ.≥ ℚ.- (+ 1 / n) {n≢0}
        lemB m m≥Nₙ = begin
          ℚ.- (+ 1 / n) {n≢0} ≤⟨ proj₂ (proj₂ (lemma2-8-2a x nonx n {n≢0})) m m≥Nₙ ⟩
          seq x m             ≤⟨ ℚP.p≤p⊔q (seq x m) (seq y m) ⟩
          seq x m ℚ.⊔ seq y m  ∎

_⊓₂_ : (x y : ℝ) -> ℝ
seq (x ⊓₂ y) m = seq x m ℚ.⊓ seq y m
reg (x ⊓₂ y) (suc k₁) (suc k₂) = begin
  ℚ.∣ (xₘ ℚ.⊓ yₘ) ℚ.- (xₙ ℚ.⊓ yₙ) ∣           ≈⟨ ℚP.∣-∣-cong (ℚP.+-cong
                                                (ℚP.⊓-cong (ℚP.≃-sym (ℚP.neg-involutive xₘ)) (ℚP.≃-sym (ℚP.neg-involutive yₘ)))
                                                (ℚP.-‿cong (ℚP.⊓-cong (ℚP.≃-sym (ℚP.neg-involutive xₙ)) (ℚP.≃-sym (ℚP.neg-involutive yₙ))))) ⟩
  ℚ.∣ ((ℚ.- (ℚ.- xₘ)) ℚ.⊓ (ℚ.- (ℚ.- yₘ))) ℚ.-
      ((ℚ.- (ℚ.- xₙ)) ℚ.⊓ (ℚ.- (ℚ.- yₙ))) ∣   ≈⟨ ℚP.∣-∣-cong (ℚP.+-cong
                                                 (ℚP.≃-sym (ℚP.neg-distrib-⊔-⊓ (ℚ.- xₘ) (ℚ.- yₘ)))
                                                 (ℚP.-‿cong (ℚP.≃-sym (ℚP.neg-distrib-⊔-⊓ (ℚ.- xₙ) (ℚ.- yₙ))))) ⟩
  ℚ.∣ ℚ.- ((ℚ.- xₘ) ℚ.⊔ (ℚ.- yₘ)) ℚ.-
      (ℚ.- ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ))) ∣         ≤⟨ reg (x ⊓ y) m n ⟩
  (+ 1 / m) ℚ.+ (+ 1 / n)                      ∎
  where
    open ℚP.≤-Reasoning
    m : ℕ
    m = suc k₁

    n : ℕ
    n = suc k₂
  
    xₘ : ℚᵘ
    xₘ = seq x m

    xₙ : ℚᵘ
    xₙ = seq x n

    yₘ : ℚᵘ
    yₘ = seq y m

    yₙ : ℚᵘ
    yₙ = seq y n

x⊓y≃x⊓₂y : ∀ x y -> x ⊓ y ≃ x ⊓₂ y
x⊓y≃x⊓₂y x y (suc k₁) = begin
  ℚ.∣ (ℚ.- ((ℚ.- xₙ) ℚ.⊔ (ℚ.- yₙ))) ℚ.- (xₙ ℚ.⊓ yₙ) ∣       ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- (xₙ ℚ.⊓ yₙ))
                                                                          (ℚP.neg-distrib-⊔-⊓ (ℚ.- xₙ) (ℚ.- yₙ))) ⟩
  ℚ.∣ ((ℚ.- (ℚ.- xₙ)) ℚ.⊓ (ℚ.- (ℚ.- yₙ))) ℚ.- (xₙ ℚ.⊓ yₙ) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- (xₙ ℚ.⊓ yₙ))
                                                                          (ℚP.⊓-cong (ℚP.neg-involutive xₙ) (ℚP.neg-involutive yₙ))) ⟩
  ℚ.∣ (xₙ ℚ.⊓ yₙ) ℚ.- (xₙ ℚ.⊓ yₙ) ∣                         ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (xₙ ℚ.⊓ yₙ)) ⟩
  0ℚᵘ                                                       ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                                    ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

    xₙ : ℚᵘ
    xₙ = seq x n

    yₙ : ℚᵘ
    yₙ = seq y n

{-
Proposition:
  If x and y are nonnegative, then so is min{x, y}.
Proof:
  Since x and y are nonnegative, for each n∈ℕ there is Nₙx, Nₙy∈ℕ such that
                             xₘ ≥ -n⁻¹       (m ≥ Nₙx), and
                             yₘ ≥ -n⁻¹       (m ≥ Nₙy).
Let Nₙ = max{Nₙx, Nₙy}, and let m ≥ Nₙ. Suppose, without loss of generality, that
xₘ ⊓ yₘ = xₘ. Then we have:
(x ⊓ y)ₘ = xₘ ⊓ yₘ
         = xₘ
         ≥ -n⁻¹.
         
-}
nonNegx,y⇒nonNegx⊓y : ∀ x y -> NonNegative x -> NonNegative y -> NonNegative (x ⊓ y)
nonNegx,y⇒nonNegx⊓y x y nonx nony = nonNeg-cong (x ⊓₂ y) (x ⊓ y) (≃-symm {x ⊓ y} {x ⊓₂ y} (x⊓y≃x⊓₂y x y))
                                    (lemma2-8-2b (x ⊓₂ y) lemA)
  where
    open ℚP.≤-Reasoning
    lemA : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ∃ λ (Nₙ : ℕ) -> Nₙ ≢0 ×
           (∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq (x ⊓₂ y) m ℚ.≥ ℚ.- (+ 1 / n) {n≢0})
    lemA (suc k₁) = Nₙ , _ , lemB
      where
        n : ℕ
        n = suc k₁

        Nₙx : ℕ
        Nₙx = proj₁ (lemma2-8-2a x nonx n)

        Nₙy : ℕ
        Nₙy = proj₁ (lemma2-8-2a y nony n)
        
        Nₙ : ℕ
        Nₙ = Nₙx ℕ.⊔ Nₙy

        lemB : ∀ (m : ℕ) -> m ℕ.≥ Nₙ -> seq (x ⊓₂ y) m ℚ.≥ ℚ.- (+ 1 / n)
        lemB m m≥Nₙ = [ left , right ]′ (ℚP.≤-total (seq x m) (seq y m))
          where
            left : seq x m ℚ.≤ seq y m -> seq (x ⊓₂ y) m ℚ.≥ ℚ.- (+ 1 / n)
            left hyp = begin
              ℚ.- (+ 1 / n)       ≤⟨ proj₂ (proj₂ (lemma2-8-2a x nonx n)) m
                                     (ℕP.≤-trans (ℕP.m≤m⊔n Nₙx Nₙy) m≥Nₙ) ⟩
              seq x m             ≈⟨ ℚP.≃-sym (ℚP.p≤q⇒p⊓q≃p hyp) ⟩
              seq x m ℚ.⊓ seq y m   ∎

            right : seq y m ℚ.≤ seq x m -> seq (x ⊓₂ y) m ℚ.≥ ℚ.- (+ 1 / n)
            right hyp = begin
              ℚ.- (+ 1 / n)       ≤⟨ proj₂ (proj₂ (lemma2-8-2a y nony n)) m
                                     (ℕP.≤-trans (ℕP.m≤n⊔m Nₙx Nₙy) m≥Nₙ) ⟩
                  seq y m             ≈⟨ ℚP.≃-sym (ℚP.p≥q⇒p⊓q≃q hyp) ⟩
              seq x m ℚ.⊓ seq y m  ∎

{-
Proposition:
  If x and y are positive, then so is min{x, y}.
Proof:
  Since x and y are positive, there are Nx, Ny∈ℕ such that
                      xₘ ≥ Nx⁻¹         (m ≥ Nx), and
                      yₘ ≥ Ny⁻¹         (m ≥ Ny).
Let N = max{Nx, Ny}, and let m ≥ N. Suppose, without loss of generality, that
xₘ ⊓ yₘ = xₘ. We have:
(x ⊓ y)ₘ = xₘ ⊓ yₘ
         = xₘ
         ≥ Nx⁻¹
         ≥ N⁻¹.
-}

posx,y⇒posx⊓y : ∀ x y -> Positive x -> Positive y -> Positive (x ⊓ y)
posx,y⇒posx⊓y x y posx posy = pos-cong (x ⊓₂ y) (x ⊓ y) (≃-symm {x ⊓ y} {x ⊓₂ y} (x⊓y≃x⊓₂y x y))
                              (lemma2-8-1b (x ⊓₂ y) (ℕ.pred N , lem))
  where
    open ℚP.≤-Reasoning
    Nx : ℕ
    Nx = suc (proj₁ (lemma2-8-1a x posx))

    Ny : ℕ
    Ny = suc (proj₁ (lemma2-8-1a y posy))

    N : ℕ
    N = Nx ℕ.⊔ Ny

    lem : ∀ (m : ℕ) -> m ℕ.≥ N -> seq (x ⊓₂ y) m ℚ.≥ + 1 / N
    lem m m≥N = [ left , right ]′ (ℚP.≤-total (seq x m) (seq y m))
      where
        left : seq x m ℚ.≤ seq y m -> seq (x ⊓₂ y) m ℚ.≥ + 1 / N
        left hyp = begin
          + 1 / N             ≤⟨ *≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ (ℕP.m≤m⊔n Nx Ny))) ⟩
          + 1 / Nx            ≤⟨ proj₂ (lemma2-8-1a x posx) m (ℕP.≤-trans (ℕP.m≤m⊔n Nx Ny) m≥N) ⟩
          seq x m             ≈⟨ ℚP.≃-sym (ℚP.p≤q⇒p⊓q≃p hyp) ⟩
          seq x m ℚ.⊓ seq y m   ∎

        right : seq y m ℚ.≤ seq x m -> seq (x ⊓₂ y) m ℚ.≥ + 1 / N
        right hyp = begin
          + 1 / N             ≤⟨ *≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ (ℕP.m≤n⊔m Nx Ny))) ⟩
          + 1 / Ny            ≤⟨ proj₂ (lemma2-8-1a y posy) m (ℕP.≤-trans (ℕP.m≤n⊔m Nx Ny) m≥N) ⟩
          seq y m             ≈⟨ ℚP.≃-sym (ℚP.p≥q⇒p⊓q≃q hyp) ⟩
          seq x m ℚ.⊓ seq y m   ∎

infix 4 _<_ _>_ _≤_ _≥_

_<_ : Rel ℝ 0ℓ
x < y = Positive (y - x)

_>_ : Rel ℝ 0ℓ
x > y = y < x

_≤_ : Rel ℝ 0ℓ
x ≤ y = NonNegative (y - x)

--data _≤_ : Rel ℝ 0ℓ where
--  ⋆≤⋆ : ∀ x y -> NonNegative (y - x) -> x ≤ y

_≥_ : Rel ℝ 0ℓ
x ≥ y = y ≤ x

Negative : Pred ℝ 0ℓ
Negative x = Positive (- x)

<⇒≤ : _<_ ⇒ _≤_
<⇒≤ {x} {y} x<y = pos⇒nonNeg (y - x) x<y

<-≤-trans : Trans _<_ _≤_ _<_
<-≤-trans {x} {y} {z} x<y y≤z = pos-cong (y - x + (z - y)) (z - x) lem (posx∧nonNegy⇒posx+y (y - x) (z - y) x<y y≤z)
  where
    open ≃-Reasoning
    lem : (y - x) + (z - y) ≃ z - x
    lem = begin
      (y - x) + (z - y)     ≈⟨ +-comm (y - x) (z - y) ⟩
      (z - y) + (y - x)     ≈⟨ +-assoc z (- y) (y - x) ⟩
      z + ((- y) + (y - x)) ≈⟨ +-congʳ z {(- y) + (y - x)} {(- y + y) - x} (≃-symm {(- y + y) - x} {(- y) + (y - x)} (+-assoc (- y) y (- x))) ⟩
      z + ((- y + y) - x)   ≈⟨ +-congʳ z {(- y + y) - x} {0ℝ - x} (+-congˡ (- x) {(- y + y)} {0ℝ} (+-inverseˡ y)) ⟩
      z + (0ℝ - x)          ≈⟨ +-congʳ z {0ℝ - x} {(- x)} (+-identityˡ (- x)) ⟩
      z - x                  ∎

≤-<-trans : Trans _≤_ _<_ _<_
≤-<-trans {x} {y} {z} x≤y y<z = pos-cong ((z - y) + (y - x)) (z - x) lem (posx∧nonNegy⇒posx+y (z - y) (y - x) y<z x≤y)
  where
    open ≃-Reasoning
    lem : (z - y) + (y - x) ≃ z - x
    lem = begin
      (z - y) + (y - x)   ≈⟨ +-assoc z (- y) (y - x) ⟩
      z + (- y + (y - x)) ≈⟨ +-congʳ z {(- y) + (y - x)} {(- y + y) - x} (≃-symm {(- y + y) - x} {(- y) + (y - x)} (+-assoc (- y) y (- x))) ⟩
      z + ((- y + y) - x) ≈⟨ +-congʳ z {(- y + y) - x} {0ℝ - x} (+-congˡ (- x) {(- y + y)} {0ℝ} (+-inverseˡ y)) ⟩
      z + (0ℝ - x)        ≈⟨ +-congʳ z {0ℝ - x} {(- x)} (+-identityˡ (- x)) ⟩
      z - x                ∎
      
<-trans : Transitive _<_
<-trans {x} {y} {z} = ≤-<-trans {x} {y} {z} ∘ <⇒≤ {x} {y}

≤-trans : Transitive _≤_
≤-trans {x} {y} {z} x≤y y≤z = nonNeg-cong (z - y + (y - x)) (z - x) lem (nonNegx,y⇒nonNegx+y (z - y) (y - x) y≤z x≤y)
  where
    open ≃-Reasoning
    lem : (z - y) + (y - x) ≃ z - x
    lem = begin
      (z - y) + (y - x)   ≈⟨ +-assoc z (- y) (y - x) ⟩
      z + (- y + (y - x)) ≈⟨ +-congʳ z {(- y) + (y - x)} {(- y + y) - x} (≃-symm {(- y + y) - x} {(- y) + (y - x)} (+-assoc (- y) y (- x))) ⟩
      z + ((- y + y) - x) ≈⟨ +-congʳ z {(- y + y) - x} {0ℝ - x} (+-congˡ (- x) {(- y + y)} {0ℝ} (+-inverseˡ y)) ⟩
      z + (0ℝ - x)        ≈⟨ +-congʳ z {0ℝ - x} {(- x)} (+-identityˡ (- x)) ⟩
      z - x                ∎

nonNeg0 : NonNegative 0ℝ
nonNeg0 (suc k₁) = ℚP.<⇒≤ (ℚP.negative⁻¹ _)

nonNeg-refl : ∀ x -> NonNegative (x - x)
nonNeg-refl x = nonNeg-cong 0ℝ (x - x) (≃-symm {x - x} {0ℝ} (+-inverseʳ x)) nonNeg0

+-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
+-mono-≤ {x} {z} {y} {t} x≤z y≤t = nonNeg-cong ((z - x) + (t - y)) ((z + t) - (x + y)) lem (nonNegx,y⇒nonNegx+y (z - x) (t - y) x≤z y≤t)
  where
    open ≃-Reasoning
    lem : (z - x) + (t - y) ≃ (z + t) - (x + y)
    lem = begin
      (z - x) + (t - y)     ≈⟨ +-congʳ (z - x) {t - y} { - y + t} (+-comm t (- y)) ⟩
      (z - x) + (- y + t)   ≈⟨ +-assoc z (- x) (- y + t) ⟩
      z + (- x + (- y + t)) ≈⟨ ≃-symm {z + ((- x + - y) + t)} {z + (- x + (- y + t))}
                               (+-congʳ z { - x + - y + t} { - x + (- y + t)} (+-assoc (- x) (- y) t)) ⟩
      z + ((- x + - y) + t) ≈⟨ +-congʳ z { - x + - y + t} {t + (- x + - y)} (+-comm (- x + - y) t) ⟩
      z + (t + (- x + - y)) ≈⟨ ≃-symm {(z + t) + (- x + - y)} {z + (t + (- x + - y))} (+-assoc z t (- x + - y)) ⟩
      (z + t) + (- x + - y) ≈⟨ +-congʳ (z + t) { - x + - y} { - (x + y)} (≃-symm { - (x + y)} { - x + - y} (neg-distrib-+ x y)) ⟩
      (z + t) - (x + y)      ∎

+-monoʳ-≤ : ∀ (x : ℝ) -> (_+_ x) Preserves _≤_ ⟶ _≤_
+-monoʳ-≤ x {y} {z} y≤z = +-mono-≤ {x} {x} {y} {z} (nonNeg-refl x) y≤z

+-monoˡ-≤ : ∀ (x : ℝ) -> (_+ x) Preserves _≤_ ⟶ _≤_
+-monoˡ-≤ x {y} {z} y≤z = +-mono-≤ {y} {z} {x} {x} y≤z (nonNeg-refl x)

+-mono-< : _+_ Preserves₂ _<_ ⟶ _<_ ⟶ _<_
+-mono-< {x} {z} {y} {t} x<z y<t = pos-cong ((z - x) + (t - y)) ((z + t) - (x + y)) lem (posx,y⇒posx+y (z - x) (t - y) x<z y<t)
  where
    open ≃-Reasoning
    lem : (z - x) + (t - y) ≃ (z + t) - (x + y)
    lem = begin
      (z - x) + (t - y)     ≈⟨ +-congʳ (z - x) {t - y} { - y + t} (+-comm t (- y)) ⟩
      (z - x) + (- y + t)   ≈⟨ +-assoc z (- x) (- y + t) ⟩
      z + (- x + (- y + t)) ≈⟨ ≃-symm {z + ((- x + - y) + t)} {z + (- x + (- y + t))}
                               (+-congʳ z { - x + - y + t} { - x + (- y + t)} (+-assoc (- x) (- y) t)) ⟩
      z + ((- x + - y) + t) ≈⟨ +-congʳ z { - x + - y + t} {t + (- x + - y)} (+-comm (- x + - y) t) ⟩
      z + (t + (- x + - y)) ≈⟨ ≃-symm {(z + t) + (- x + - y)} {z + (t + (- x + - y))} (+-assoc z t (- x + - y)) ⟩
      (z + t) + (- x + - y) ≈⟨ +-congʳ (z + t) { - x + - y} { - (x + y)} (≃-symm { - (x + y)} { - x + - y} (neg-distrib-+ x y)) ⟩
      (z + t) - (x + y)      ∎

neg-distribˡ-* : ∀ x y -> - (x * y) ≃ - x * y
neg-distribˡ-* x y = begin
  - (x * y)                       ≈⟨ ≃-trans { - (x * y)} { - (x * y) + 0ℝ} { - (x * y) + 0ℝ * y}
                                     (≃-symm { - (x * y) + 0ℝ} { - (x * y)} (+-identityʳ (- (x * y))))
                                     (+-congʳ (- (x * y)) {0ℝ} {0ℝ * y} (≃-symm {0ℝ * y} {0ℝ} (*-zeroˡ y))) ⟩
  - (x * y) + 0ℝ * y              ≈⟨ +-congʳ (- (x * y)) {0ℝ * y} {(x - x) * y} (*-congʳ {y} {0ℝ} {x - x} (≃-symm {x - x} {0ℝ} (+-inverseʳ x))) ⟩
  - (x * y) + (x - x) * y         ≈⟨ +-congʳ (- (x * y)) {(x - x) * y} {x * y + (- x) * y} (*-distribʳ-+ y x (- x)) ⟩
  - (x * y) + (x * y + (- x) * y) ≈⟨ ≃-symm { - (x * y) + x * y + - x * y} { - (x * y) + (x * y + - x * y)}
                                     (+-assoc (- (x * y)) (x * y) ((- x) * y)) ⟩
  - (x * y) + x * y + (- x) * y   ≈⟨ +-congˡ (- x * y) { - (x * y) + x * y} {0ℝ} (+-inverseˡ (x * y)) ⟩
  0ℝ + (- x) * y                  ≈⟨ +-identityˡ ((- x) * y) ⟩
  (- x) * y                        ∎
  where
    open ≃-Reasoning

neg-distribʳ-* : ∀ x y -> - (x * y) ≃ x * (- y)
neg-distribʳ-* x y = begin
  - (x * y) ≈⟨ -‿cong {x * y} {y * x} (*-comm x y) ⟩
  - (y * x) ≈⟨ neg-distribˡ-* y x ⟩
  - y * x   ≈⟨ *-comm (- y) x ⟩
  x * (- y)  ∎
  where
    open ≃-Reasoning

≤-reflexive : _≃_ ⇒ _≤_
≤-reflexive {x} {y} x≃y = nonNeg-cong (x - x) (y - x) (+-congˡ (- x) {x} {y} x≃y) (nonNeg-refl x)

≤-refl : Reflexive _≤_
≤-refl {x} = ≤-reflexive {x} {x} (≃-refl {x})

≤-isPreorder : IsPreorder _≃_ _≤_
IsPreorder.isEquivalence ≤-isPreorder = ≃-isEquivalence
IsPreorder.reflexive ≤-isPreorder {x} {y} x≃y = ≤-reflexive {x} {y} x≃y
IsPreorder.trans ≤-isPreorder {x} {y} {z} = ≤-trans {x} {y} {z}

<-respʳ-≃ : _<_ Respectsʳ _≃_
<-respʳ-≃ {x} {y} {z} y≃z x<y = <-≤-trans {x} {y} {z} x<y (≤-reflexive {y} {z} y≃z)

<-respˡ-≃ : _<_ Respectsˡ _≃_
<-respˡ-≃ {x} {y} {z} y≃z y<x = ≤-<-trans {z} {y} {x} (≤-reflexive {z} {y} (≃-symm {y} {z} y≃z)) y<x

<-resp-≃ : _<_ Respects₂ _≃_
<-resp-≃ = (λ {x} {y} {z} -> <-respʳ-≃ {x} {y} {z}) , λ {x} {y} {z} -> <-respˡ-≃ {x} {y} {z}

{-
Same issue as with ≃-refl. I need to specify the arguments in order to avoid the constraint error,
hence the lambdas.
-}

module ≤-Reasoning where
  open import Relation.Binary.Reasoning.Base.Triple
    ≤-isPreorder
    (λ {x} {y} {z} -> <-trans {x} {y} {z})
    <-resp-≃
    (λ {x} {y} -> <⇒≤ {x} {y})
    (λ {x} {y} {z} -> <-≤-trans {x} {y} {z})
    (λ {x} {y} {z} -> ≤-<-trans {x} {y} {z})
    public

*-monoʳ-≤-nonNeg : ∀ x y z -> x ≤ z -> NonNegative y -> x * y ≤ z * y
*-monoʳ-≤-nonNeg x y z x≤z nony = nonNeg-cong ((z - x) * y) (z * y - x * y) lem (nonNegx,y⇒nonNegx*y (z - x) y x≤z nony)
  where
    open ≃-Reasoning
    lem : (z - x) * y ≃ z * y - x * y
    lem = begin
      (z - x) * y        ≈⟨ *-distribʳ-+ y z (- x) ⟩
      z * y + (- x) * y  ≈⟨ +-congʳ (z * y) { - x * y} { - (x * y)} (≃-symm { - (x * y)} { - x * y} (neg-distribˡ-* x y)) ⟩
      z * y - x * y       ∎

*-monoˡ-≤-nonNeg : ∀ x y z -> x ≤ z -> NonNegative y -> y * x ≤ y * z
*-monoˡ-≤-nonNeg x y z x≤z nony = begin
  y * x ≈⟨ *-comm y x ⟩
  x * y ≤⟨ *-monoʳ-≤-nonNeg x y z x≤z nony ⟩
  z * y ≈⟨ *-comm z y ⟩
  y * z  ∎
  where
    open ≤-Reasoning

*-monoʳ-<-pos : ∀ {y} -> Positive y -> (_*_ y) Preserves _<_ ⟶ _<_
*-monoʳ-<-pos {y} posy {x} {z} x<z = pos-cong (y * (z - x)) (y * z - y * x) lem (posx,y⇒posx*y y (z - x) posy x<z)
  where
    open ≃-Reasoning
    lem : y * (z - x) ≃ y * z - y * x
    lem = begin
      y * (z - x)       ≈⟨ *-distribˡ-+ y z (- x) ⟩
      y * z + y * (- x) ≈⟨ +-congʳ (y * z) {y * (- x)} { - (y * x)} (≃-symm { - (y * x)} {y * (- x)} (neg-distribʳ-* y x)) ⟩
      y * z - y * x      ∎

*-monoˡ-<-pos : ∀ {y} -> Positive y -> (_* y) Preserves _<_ ⟶ _<_
*-monoˡ-<-pos {y} posy {x} {z} x<z = begin-strict
  x * y ≈⟨ *-comm x y ⟩
  y * x <⟨ *-monoʳ-<-pos {y} posy {x} {z} x<z ⟩
  y * z ≈⟨ *-comm y z ⟩
  z * y  ∎
  where
    open ≤-Reasoning

neg-mono-< : -_ Preserves _<_ ⟶ _>_
neg-mono-< {x} {y} x<y = pos-cong (y - x) (- x - (- y)) lem x<y
  where
    open ≃-Reasoning
    lem : y - x ≃ - x - (- y)
    lem = begin
      y - x       ≈⟨ +-congˡ (- x) {y} { - (- y)} (≃-symm { - (- y)} {y} (neg-involutive y)) ⟩
      - (- y) - x ≈⟨ +-comm (- (- y)) (- x) ⟩
      - x - (- y)  ∎

neg-mono-≤ : -_ Preserves _≤_ ⟶ _≥_
neg-mono-≤ {x} {y} x≤y = nonNeg-cong (y - x) (- x - (- y)) lem x≤y
  where
    open ≃-Reasoning
    lem : y - x ≃ - x - (- y)
    lem = begin
      y - x       ≈⟨ +-congˡ (- x) {y} { - (- y)} (≃-symm { - (- y)} {y} (neg-involutive y)) ⟩
      - (- y) - x ≈⟨ +-comm (- (- y)) (- x) ⟩
      - x - (- y)  ∎

x≤x⊔y : ∀ x y -> x ≤ x ⊔ y
x≤x⊔y x y (suc k₁) = begin
  ℚ.- (+ 1 / n)                                           ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
  0ℚᵘ                                                     ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ (seq x (2 ℕ.* n))) ⟩
  seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)                     ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- seq x (2 ℕ.* n)) (ℚP.p≤p⊔q (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
  seq x (2 ℕ.* n) ℚ.⊔ seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)  ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

x≤y⊔x : ∀ x y -> x ≤ y ⊔ x
x≤y⊔x x y = begin
  x     ≤⟨ x≤x⊔y x y ⟩
  x ⊔ y ≈⟨ ⊔-comm x y ⟩
  y ⊔ x  ∎
  where
    open ≤-Reasoning

x⊓y≤x : ∀ x y -> x ⊓ y ≤ x
x⊓y≤x x y = nonNeg-cong (x - (x ⊓₂ y)) (x - (x ⊓ y)) lemA lemB
  where
    open ℚP.≤-Reasoning
    lemA : x - (x ⊓₂ y) ≃ x - (x ⊓ y)
    lemA = +-congʳ x { - (x ⊓₂ y)} { - (x ⊓ y)} (-‿cong {x ⊓₂ y} {x ⊓ y}
           (≃-symm {x ⊓ y} {x ⊓₂ y} (x⊓y≃x⊓₂y x y)))

    lemB : x ⊓₂ y ≤ x
    lemB (suc k₁) = begin
      ℚ.- (+ 1 / n)                             ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
      0ℚᵘ                                       ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ (seq x (2 ℕ.* n))) ⟩ 
      seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)       ≤⟨ ℚP.+-monoʳ-≤ (seq x (2 ℕ.* n)) (ℚP.neg-mono-≤ (ℚP.p⊓q≤p (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)))) ⟩
      seq x (2 ℕ.* n) ℚ.- seq (x ⊓₂ y) (2 ℕ.* n) ∎
      where
        n : ℕ
        n = suc k₁

x⊓y≤y : ∀ x y -> x ⊓ y ≤ y
x⊓y≤y x y = begin
  x ⊓ y ≈⟨ ⊓-comm x y ⟩
  y ⊓ x ≤⟨ x⊓y≤x y x ⟩
  y      ∎
  where
    open ≤-Reasoning

{-
Proposition:
  ≤ is antisymmetric.
Proof:
Since y - x and x - y are nonnegative, for all n∈ℕ, we have
                              y₂ₙ - x₂ₙ ≥ -n⁻¹          (1), and
                              x₂ₙ - y₂ₙ ≥ -n⁻¹          (2)
Let n∈ℕ. Either ∣x₂ₙ - y₂ₙ∣ = x₂ₙ - y₂ₙ or ∣x₂ₙ - y₂ₙ∣ = y₂ₙ - x₂ₙ.
Case 1: We have: 
∣x₂ₙ - y₂ₙ∣ = x₂ₙ - y₂ₙ
            ≤ n⁻¹      by (1)
            ≤ 2n⁻¹.
Case 2: Similar.
Thus x - y ≃ 0. Hence x ≃ y.                                    □
-}
≤-antisym : Antisymmetric _≃_ _≤_
≤-antisym {x} {y} x≤y y≤x = ≃-symm {y} {x} lemB
  where
    lemA : x - y ≃ 0ℝ
    lemA (suc k₁) = begin
      ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ℚ.- 0ℚᵘ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-identityʳ (seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n))) ⟩
      ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣         ≤⟨ [ left , right ]′ (ℚP.≤-total (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n))) ⟩
      + 2 / n                                            ∎
      where
        open ℚP.≤-Reasoning
        open import Data.Rational.Unnormalised.Solver
        open +-*-Solver
        n : ℕ
        n = suc k₁

        left : seq x (2 ℕ.* n) ℚ.≤ seq y (2 ℕ.* n) -> ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ℚ.≤ + 2 / n
        left hyp = begin
          ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.∣-p∣≃∣p∣ (seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n))))
                                                       (ℚP.0≤p⇒∣p∣≃p (ℚP.neg-mono-≤ (ℚP.p≤q⇒p-q≤0 hyp))) ⟩
          ℚ.- (seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n)) ≤⟨ ℚP.≤-respʳ-≃ (ℚP.neg-involutive (+ 1 / n)) (ℚP.neg-mono-≤ (y≤x n)) ⟩
          + 1 / n                                   ≤⟨ *≤* (ℤP.*-monoʳ-≤-nonNeg n {+ 1} {+ 2} (+≤+ (ℕ.s≤s ℕ.z≤n))) ⟩
          + 2 / n                                    ∎

        right : seq y (2 ℕ.* n) ℚ.≤ seq x (2 ℕ.* n) -> ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ℚ.≤ + 2 / n
        right hyp = begin
          ℚ.∣ seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n) ∣ ≈⟨ ℚP.0≤p⇒∣p∣≃p (ℚP.p≤q⇒0≤q-p hyp) ⟩
          seq x (2 ℕ.* n) ℚ.- seq y (2 ℕ.* n)       ≈⟨ solve 2 (λ x y -> x :- y := :- (y :- x)) ℚP.≃-refl (seq x (2 ℕ.* n)) (seq y (2 ℕ.* n)) ⟩
          ℚ.- (seq y (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)) ≤⟨ ℚP.≤-respʳ-≃ (ℚP.neg-involutive (+ 1 / n)) (ℚP.neg-mono-≤ (x≤y n)) ⟩
          + 1 / n                                   ≤⟨ *≤* (ℤP.*-monoʳ-≤-nonNeg n {+ 1} {+ 2} (+≤+ (ℕ.s≤s ℕ.z≤n))) ⟩
          + 2 / n                                    ∎

    lemB : y ≃ x
    lemB = begin
      y             ≈⟨ ≃-symm {y + 0ℝ} {y} (+-identityʳ y) ⟩
      y + 0ℝ        ≈⟨ +-congʳ y {0ℝ} {x - y} (≃-symm {x - y} {0ℝ} lemA) ⟩
      y + (x - y)   ≈⟨ +-congʳ y {x - y} { - y + x} (+-comm x (- y)) ⟩
      y + (- y + x) ≈⟨ ≃-symm {y - y + x} {y + (- y + x)} (+-assoc y (- y) x) ⟩
      y - y + x     ≈⟨ +-congˡ x {y - y} {0ℝ} (+-inverseʳ y) ⟩
      0ℝ + x        ≈⟨ +-identityˡ x ⟩
      x              ∎
      where
        open ≃-Reasoning

0≤∣x∣ : ∀ x -> 0ℝ ≤ ∣ x ∣
0≤∣x∣ x = nonNeg-cong ∣ x ∣ (∣ x ∣ - 0ℝ) (≃-symm {∣ x ∣ - 0ℝ} {∣ x ∣} (+-identityʳ ∣ x ∣)) (∣x∣nonNeg x)

∣x+y∣₂≤∣x∣₂+∣y∣₂ : ∀ x y -> ∣ x + y ∣₂ ≤ ∣ x ∣₂ + ∣ y ∣₂
∣x+y∣₂≤∣x∣₂+∣y∣₂ x y (suc k₁) = begin
  ℚ.- (+ 1 / n)                        ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
  0ℚᵘ                                  ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ (∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣)) ⟩
  ∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣ ℚ.- (∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣) ≤⟨ ℚP.+-monoʳ-≤ (∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣)
                                          (ℚP.neg-mono-≤ (ℚP.∣p+q∣≤∣p∣+∣q∣ (seq x (2 ℕ.* (2 ℕ.* n))) (seq y (2 ℕ.* (2 ℕ.* n))))) ⟩
  ∣x₄ₙ∣ ℚ.+ ∣y₄ₙ∣ ℚ.- ∣x₄ₙ+y₄ₙ∣          ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

    ∣x₄ₙ∣ : ℚᵘ
    ∣x₄ₙ∣ = ℚ.∣ seq x (2 ℕ.* (2 ℕ.* n)) ∣

    ∣y₄ₙ∣ : ℚᵘ
    ∣y₄ₙ∣ = ℚ.∣ seq y (2 ℕ.* (2 ℕ.* n)) ∣

    ∣x₄ₙ+y₄ₙ∣ : ℚᵘ
    ∣x₄ₙ+y₄ₙ∣ = ℚ.∣ seq x (2 ℕ.* (2 ℕ.* n)) ℚ.+ seq y (2 ℕ.* (2 ℕ.* n)) ∣

∣x+y∣≤∣x∣+∣y∣ : ∀ x y -> ∣ x + y ∣ ≤ ∣ x ∣ + ∣ y ∣
∣x+y∣≤∣x∣+∣y∣ x y = begin
  ∣ x + y ∣       ≈⟨ ∣x∣≃∣x∣₂ (x + y) ⟩
  ∣ x + y ∣₂      ≤⟨ ∣x+y∣₂≤∣x∣₂+∣y∣₂ x y ⟩
  ∣ x ∣₂ + ∣ y ∣₂ ≈⟨ +-cong {∣ x ∣₂} {∣ x ∣} {∣ y ∣₂} {∣ y ∣}
                     (≃-symm {∣ x ∣} {∣ x ∣₂} (∣x∣≃∣x∣₂ x))
                     (≃-symm {∣ y ∣} {∣ y ∣₂} (∣x∣≃∣x∣₂ y)) ⟩
  ∣ x ∣ + ∣ y ∣    ∎
  where
    open ≤-Reasoning

_≄_ : Rel ℝ 0ℓ
x ≄ y = x < y ⊎ y < x

x≤∣x∣ : ∀ x -> x ≤ ∣ x ∣
x≤∣x∣ x (suc k₁) = begin
  ℚ.- (+ 1 / n)                           ≤⟨ ℚP.nonPositive⁻¹ _ ⟩
  0ℚᵘ                                     ≈⟨ ℚP.≃-sym (ℚP.+-inverseʳ (seq x (2 ℕ.* n))) ⟩
  seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)     ≤⟨ ℚP.+-monoˡ-≤ (ℚ.- seq x (2 ℕ.* n)) (ℚP.p≤p⊔q (seq x (2 ℕ.* n)) (ℚ.- seq x (2 ℕ.* n))) ⟩
  seq ∣ x ∣ (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)   ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

∣-x∣₂≃∣x∣₂ : ∀ x -> ∣ - x ∣₂ ≃ ∣ x ∣₂
∣-x∣₂≃∣x∣₂ x (suc k₁) = begin
  ℚ.∣ ℚ.∣ ℚ.- seq x n ∣ ℚ.- ℚ.∣ seq x n ∣ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ (ℚ.- ℚ.∣ seq x n ∣) (ℚP.∣-p∣≃∣p∣ (seq x n))) ⟩
  ℚ.∣ ℚ.∣ seq x n ∣ ℚ.- ℚ.∣ seq x n ∣ ∣     ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ ℚ.∣ seq x n ∣) ⟩
  0ℚᵘ                                      ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  + 2 / n                                   ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

    test : seq ∣ - x ∣₂ n ℚ.≃ ℚ.∣ ℚ.- seq x n ∣
    test = ℚP.≃-refl

∣-x∣≃∣x∣ : ∀ x -> ∣ - x ∣ ≃ ∣ x ∣
∣-x∣≃∣x∣ x = begin
  ∣ - x ∣  ≈⟨ ∣x∣≃∣x∣₂ (- x) ⟩
  ∣ - x ∣₂ ≈⟨ ∣-x∣₂≃∣x∣₂ x ⟩
  ∣ x ∣₂   ≈⟨ ≃-symm {∣ x ∣} {∣ x ∣₂} (∣x∣≃∣x∣₂ x) ⟩
  ∣ x ∣     ∎
  where
    open ≃-Reasoning

0<x⇒posx : ∀ x -> 0ℝ < x -> Positive x
0<x⇒posx x 0<x = pos-cong (x - 0ℝ) x (+-identityʳ x) 0<x

posx⇒0<x : ∀ x -> Positive x -> 0ℝ < x
posx⇒0<x x posx = pos-cong x (x - 0ℝ) (≃-symm {x - 0ℝ} {x} (+-identityʳ x)) posx

x≄0⇒0<∣x∣ : ∀ x -> x ≄ 0ℝ -> 0ℝ < ∣ x ∣
x≄0⇒0<∣x∣ x x≄0 = [ left , right ]′ x≄0
  where
    open ≤-Reasoning
    left : x < 0ℝ -> 0ℝ < ∣ x ∣
    left hyp = begin-strict
      0ℝ      <⟨ neg-mono-< {x} {0ℝ} hyp ⟩
      - x     ≤⟨ x≤∣x∣ (- x) ⟩
      ∣ - x ∣ ≈⟨ ∣-x∣≃∣x∣ x ⟩
      ∣ x ∣    ∎

    right : 0ℝ < x -> 0ℝ < ∣ x ∣
    right hyp = begin-strict
      0ℝ    <⟨ hyp ⟩
      x     ≤⟨ x≤∣x∣ x ⟩
      ∣ x ∣   ∎

x≄0⇒pos∣x∣ : ∀ x -> x ≄ 0ℝ -> Positive ∣ x ∣
x≄0⇒pos∣x∣ x x≄0 = 0<x⇒posx ∣ x ∣ (x≄0⇒0<∣x∣ x x≄0)

x≄0⇒pos∣x∣₂ : ∀ x -> x ≄ 0ℝ -> Positive ∣ x ∣₂
x≄0⇒pos∣x∣₂ x x≄0 = pos-cong ∣ x ∣ ∣ x ∣₂ (∣x∣≃∣x∣₂ x) (x≄0⇒pos∣x∣ x x≄0)

{-
Using abstract versions of previous results for better performance.
For instance, using lemma2-8-1a directly can be very slow.
-}
abstract
  fastℕ<?ℕ : Decidable ℕ._<_
  fastℕ<?ℕ = ℕP._<?_

  fast2-8-1a : ∀ x -> Positive x -> ∃ λ (N : ℕ) -> ∀ (m : ℕ) -> m ℕ.≥ suc N ->
                seq x m ℚ.≥ + 1 / (suc N)
  fast2-8-1a = lemma2-8-1a

ℚ≠-helper : ∀ p -> p ℚ.> 0ℚᵘ ⊎ p ℚ.< 0ℚᵘ -> p ℚ.≠ 0ℚᵘ
ℚ≠-helper p hyp1 hyp2 = [ left , right ]′ hyp1
  where
    left : ¬ (p ℚ.> 0ℚᵘ)
    left hyp = ℚP.<-irrefl (ℚP.≃-sym hyp2) hyp

    right : ¬ (p ℚ.< 0ℚᵘ)
    right hyp = ℚP.<-irrefl hyp2 hyp

{-
For the sake of performance, we define an alternative version of the inverse given
by Bishop.
-}

Nₐ : (x : ℝ) -> {x≄0 : x ≄ 0ℝ} ->  ℕ
Nₐ x {x≄0} = suc (proj₁ (fast2-8-1a ∣ x ∣₂ (x≄0⇒pos∣x∣₂ x x≄0)))

not0-helper : ∀ (x : ℝ) -> {x≄0 : x ≄ 0ℝ} -> ∀ (n : ℕ) ->
               ℤ.∣ ↥ (seq x ((n ℕ.+ (Nₐ x {x≄0})) ℕ.* ((Nₐ x {x≄0}) ℕ.* (Nₐ x {x≄0})))) ∣ ≢0
not0-helper x {x≄0} n = ℚP.p≄0⇒∣↥p∣≢0 xₛ (ℚ≠-helper xₛ ([ left , right ]′ (ℚP.∣p∣≡p∨∣p∣≡-p xₛ)))
  where
    open ℚP.≤-Reasoning
    N : ℕ
    N = Nₐ x {x≄0}

    xₛ : ℚᵘ
    xₛ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))

    0<∣xₛ∣ : 0ℚᵘ ℚ.< ℚ.∣ xₛ ∣
    0<∣xₛ∣ = begin-strict
      0ℚᵘ     <⟨ ℚP.positive⁻¹ _ ⟩
      + 1 / N ≤⟨ proj₂ (fast2-8-1a ∣ x ∣₂ (x≄0⇒pos∣x∣₂ x x≄0)) ((n ℕ.+ N) ℕ.* (N ℕ.* N))
                 (ℕP.≤-trans (ℕP.m≤n*m N {N} ℕP.0<1+n) (ℕP.m≤n*m (N ℕ.* N) {n ℕ.+ N} (subst (0 ℕ.<_) (ℕP.+-comm N n) ℕP.0<1+n))) ⟩
      ℚ.∣ xₛ ∣  ∎

    left : ℚ.∣ xₛ ∣ ≡ xₛ -> xₛ ℚ.> 0ℚᵘ ⊎ xₛ ℚ.< 0ℚᵘ
    left hyp = inj₁ (begin-strict
      0ℚᵘ      <⟨ 0<∣xₛ∣ ⟩
      ℚ.∣ xₛ ∣ ≡⟨ hyp ⟩
      xₛ        ∎)

    right : ℚ.∣ xₛ ∣ ≡ ℚ.- xₛ -> xₛ ℚ.> 0ℚᵘ ⊎ xₛ ℚ.< 0ℚᵘ
    right hyp = inj₂ (begin-strict
      xₛ            ≈⟨ ℚP.≃-sym (ℚP.neg-involutive xₛ) ⟩
      ℚ.- (ℚ.- xₛ)  ≡⟨ cong ℚ.-_ (sym hyp) ⟩
      ℚ.- ℚ.∣ xₛ ∣  <⟨ ℚP.neg-mono-< 0<∣xₛ∣ ⟩
      0ℚᵘ            ∎)

{-
Strangely enough, this function is EXTREMELY slow. It pretty much does not compute. But proving an instance of it in
the definition of multiplicative inverse is very fast. Not sure why.
-}

-- ∣xₘ∣ ≥ N⁻¹
{-
abstract
  inverse-helper : ∀ (x : ℝ) -> {x≄0 : x ≄ 0ℝ} -> ∀ (n : ℕ) -> {n≢0 : n ≢0} ->
                   ℚ.∣ (ℚ.1/ seq x ((n ℕ.+ (Nₐ x {x≄0})) ℕ.* ((Nₐ x {x≄0}) ℕ.* (Nₐ x {x≄0})))) {not0-helper x {x≄0} n} ∣ ℚ.≤ + (Nₐ x {x≄0}) / 1
  inverse-helper x {x≄0} (suc k₁) = begin
    ℚ.∣ xₛ⁻¹ ∣ ≈⟨ {!N!} {-{!ℚP.≃-trans (ℚP.≃-sym (ℚP.*-identityʳ ℚ.∣ xₛ⁻¹ ∣))
                  (ℚP.*-congˡ {ℚ.∣ xₛ⁻¹ ∣} (ℚP.≃-sym (ℚP.*-inverseʳ (+ 1 / N))))!}-} ⟩
    ℚ.∣ xₛ⁻¹ ∣ ℚ.* ((+ 1 / N) ℚ.* (+ N / 1)) ≤⟨ {!!} ⟩
    + N / 1                                   ∎
    where
      open ℚP.≤-Reasoning
      n : ℕ
      n = suc k₁

      N : ℕ
      N = Nₐ x {x≄0}

      xₛ : ℚᵘ
      xₛ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))

      xₛ≢0 : ℤ.∣ ↥ xₛ ∣ ≢0
      xₛ≢0 = not0-helper x {x≄0} n

      xₛ⁻¹ : ℚᵘ
      xₛ⁻¹ = (ℚ.1/ seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))) {xₛ≢0}

      helper : ℚ.∣ xₛ⁻¹ ∣ ℚ.* ℚ.∣ xₛ ∣ ℚ.≃ ℚ.1ℚᵘ
      helper = begin-equality
        ℚ.∣ xₛ⁻¹ ∣ ℚ.* ℚ.∣ xₛ ∣ ≈⟨ ℚP.≃-sym (ℚP.∣p*q∣≃∣p∣*∣q∣ xₛ⁻¹ xₛ) ⟩
        ℚ.∣ xₛ⁻¹ ℚ.* xₛ ∣       ≈⟨ ℚP.∣-∣-cong (ℚP.*-inverseˡ xₛ {xₛ≢0}) ⟩
        ℚ.1ℚᵘ                    ∎-}


{-
∣x∣ > 0 
∣xₘ∣ ≥ N⁻¹  (m ≥ N)
x ≄ 0
x⁻¹ = (x (N³))⁻¹     if n < N
      (x (n * N²))⁻¹ else

x⁻¹ = (x ((n + N) * N²))⁻¹

x⁻¹ n with n <? N

-}
_⁻¹ : (x : ℝ) -> {x≄0 : x ≄ 0ℝ} -> ℝ
seq ((x ⁻¹) {x≄0}) n = (ℚ.1/ xₛ) {not0-helper x {x≄0} n}
  where
    open ℚP.≤-Reasoning
    N : ℕ
    N = Nₐ x {x≄0}

    xₛ : ℚᵘ
    xₛ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))
reg ((x ⁻¹) {x≄0}) (suc k₁) (suc k₂) = begin
  ℚ.∣ yₘ ℚ.- yₙ ∣                                 ≈⟨ ℚP.∣-∣-cong (ℚP.+-cong
                                                     (ℚP.≃-trans (ℚP.≃-sym (ℚP.*-identityʳ yₘ)) (ℚP.*-congˡ {yₘ} (ℚP.≃-sym (ℚP.*-inverseˡ xₙ {xₖ≢0 n}))))
                                                     (ℚP.-‿cong (ℚP.≃-trans (ℚP.≃-sym (ℚP.*-identityʳ yₙ)) (ℚP.*-congˡ {yₙ} (ℚP.≃-sym (ℚP.*-inverseˡ xₘ {xₖ≢0 m})))))) ⟩
  ℚ.∣ yₘ ℚ.* (yₙ ℚ.* xₙ) ℚ.- yₙ ℚ.* (yₘ ℚ.* xₘ) ∣ ≈⟨ ℚP.∣-∣-cong (ℚsolve 4 (λ xₘ xₙ yₘ yₙ ->
                                                     yₘ ℚ:* (yₙ ℚ:* xₙ) ℚ:- yₙ ℚ:* (yₘ ℚ:* xₘ) ℚ:= yₘ ℚ:* yₙ ℚ:* (xₙ ℚ:- xₘ))
                                                     ℚP.≃-refl xₘ xₙ yₘ yₙ) ⟩
  ℚ.∣ yₘ ℚ.* yₙ ℚ.* (xₙ ℚ.- xₘ) ∣                 ≈⟨ ℚP.∣p*q∣≃∣p∣*∣q∣ (yₘ ℚ.* yₙ) (xₙ ℚ.- xₘ) ⟩
  ℚ.∣ yₘ ℚ.* yₙ ∣ ℚ.* ℚ.∣ xₙ ℚ.- xₘ ∣             ≤⟨ ℚP.≤-trans
                                                     (ℚP.*-monoʳ-≤-nonNeg {ℚ.∣ yₘ ℚ.* yₙ ∣} _ (reg x ((n ℕ.+ N) ℕ.* (N ℕ.* N)) ((m ℕ.+ N) ℕ.* (N ℕ.* N))))
                                                     (ℚP.*-monoˡ-≤-nonNeg {+ 1 / ((n ℕ.+ N) ℕ.* (N ℕ.* N)) ℚ.+ + 1 / ((m ℕ.+ N) ℕ.* (N ℕ.* N))} _ ∣yₘ*yₙ∣≤N²) ⟩
  (+ N / 1) ℚ.* (+ N / 1) ℚ.*
  ((+ 1 / ((n ℕ.+ N) ℕ.* (N ℕ.* N))) ℚ.+
   (+ 1 / ((m ℕ.+ N) ℕ.* (N ℕ.* N))))             ≈⟨ ℚ.*≡* (solve 3 (λ m n N ->

  -- Function and details for solver
  ((N :* N) :* ((con (+ 1) :* ((m :+ N) :* (N :* N))) :+ (con (+ 1) :* ((n :+ N) :* (N :* N))))) :* ((m :+ N) :* (n :+ N)) :=
  (con (+ 1) :* (n :+ N) :+ con (+ 1) :* (m :+ N)) :* (con (+ 1) :* con (+ 1) :* (((n :+ N) :* (N :* N)) :* ((m :+ N) :* (N :* N)))))
   _≡_.refl (+ m) (+ n) (+ N)) ⟩

  (+ 1 / (m ℕ.+ N)) ℚ.+ (+ 1 / (n ℕ.+ N))         ≤⟨ ℚP.+-mono-≤ {+ 1 / (m ℕ.+ N)} {+ 1 / m} {+ 1 / (n ℕ.+ N)} {+ 1 / n}
                                                     (*≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ (ℕP.m≤m+n m N))))
                                                     (*≤* (ℤP.*-monoˡ-≤-nonNeg 1 (+≤+ (ℕP.m≤m+n n N)))) ⟩
  (+ 1 / m) ℚ.+ (+ 1 / n)                          ∎
  where
    open ℚP.≤-Reasoning
    open import Data.Integer.Solver as ℤ-Solver
    open ℤ-Solver.+-*-Solver
    open import Data.Rational.Unnormalised.Solver as ℚ-Solver
    open ℚ-Solver.+-*-Solver using ()
      renaming
        ( solve to ℚsolve
        ; _:-_ to _ℚ:-_
        ; _:*_ to _ℚ:*_
        ; _:=_ to _ℚ:=_
        )
    N : ℕ
    N = Nₐ x {x≄0}

    m : ℕ
    m = suc k₁

    n : ℕ
    n = suc k₂

    xₘ : ℚᵘ
    xₘ = seq x ((m ℕ.+ N) ℕ.* (N ℕ.* N))

    xₙ : ℚᵘ
    xₙ = seq x ((n ℕ.+ N) ℕ.* (N ℕ.* N))

    xₖ≢0 : ∀ (k : ℕ) -> ℤ.∣ ↥ seq x ((k ℕ.+ N) ℕ.* (N ℕ.* N)) ∣ ≢0
    xₖ≢0 k = not0-helper x {x≄0} k

    yₘ : ℚᵘ
    yₘ = (ℚ.1/ xₘ) {xₖ≢0 m}

    yₙ : ℚᵘ
    yₙ = (ℚ.1/ xₙ) {xₖ≢0 n}

    
    ∣yₖ∣≤N : ∀ (k : ℕ) -> ℚ.∣ (ℚ.1/ (seq x ((k ℕ.+ N) ℕ.* (N ℕ.* N)))) {not0-helper x {x≄0} k} ∣ ℚ.≤ + N / 1
    ∣yₖ∣≤N k = begin
      ℚ.∣ yₖ ∣ ≈⟨ ℚP.≃-trans (ℚP.≃-sym (ℚP.*-identityʳ ℚ.∣ yₖ ∣)) (ℚP.*-congˡ {ℚ.∣ yₖ ∣} (ℚP.≃-sym (ℚP.*-inverseʳ (+ 1 / N)))) ⟩
      ℚ.∣ yₖ ∣ ℚ.* ((+ 1 / N) ℚ.* (+ N / 1)) ≤⟨ ℚP.*-monoʳ-≤-nonNeg {ℚ.∣ yₖ ∣} _ (ℚP.*-monoˡ-≤-nonNeg {+ N / 1} _
                                                (proj₂ (fast2-8-1a ∣ x ∣₂ (x≄0⇒pos∣x∣₂ x x≄0)) ((k ℕ.+ N) ℕ.* (N ℕ.* N))
                                                (ℕP.≤-trans (ℕP.m≤m*n N {N} ℕP.0<1+n)
                                                (ℕP.m≤n*m (N ℕ.* N) {k ℕ.+ N} (subst (0 ℕ.<_) (ℕP.+-comm N k) ℕP.0<1+n))))) ⟩
      ℚ.∣ yₖ ∣ ℚ.* (ℚ.∣ xₖ ∣ ℚ.* (+ N / 1))  ≈⟨ ℚP.≃-trans
                                                (ℚP.≃-sym (ℚP.*-assoc ℚ.∣ yₖ ∣ ℚ.∣ xₖ ∣ (+ N / 1)))
                                                (ℚP.≃-sym (ℚP.*-congʳ {+ N / 1} (ℚP.∣p*q∣≃∣p∣*∣q∣ yₖ xₖ))) ⟩
      ℚ.∣ yₖ ℚ.* xₖ ∣ ℚ.* (+ N / 1)          ≈⟨ ℚP.≃-trans
                                                (ℚP.*-congʳ {+ N / 1} (ℚP.∣-∣-cong (ℚP.*-inverseˡ xₖ {xₖ≢0 k})))
                                                (ℚP.*-identityˡ (+ N / 1)) ⟩
      + N / 1                                 ∎
      where
        xₖ : ℚᵘ
        xₖ = seq x ((k ℕ.+ N) ℕ.* (N ℕ.* N))

        yₖ : ℚᵘ
        yₖ = (ℚ.1/ xₖ) {not0-helper x {x≄0} k}

    ∣yₘ*yₙ∣≤N² : ℚ.∣ yₘ ℚ.* yₙ ∣ ℚ.≤ (+ N / 1) ℚ.* (+ N / 1)
    ∣yₘ*yₙ∣≤N² = begin
      ℚ.∣ yₘ ℚ.* yₙ ∣          ≈⟨ ℚP.∣p*q∣≃∣p∣*∣q∣ yₘ yₙ ⟩
      ℚ.∣ yₘ ∣ ℚ.* ℚ.∣ yₙ ∣    ≤⟨ ℚP.≤-trans
                                  (ℚP.*-monoˡ-≤-nonNeg {ℚ.∣ yₙ ∣} _ (∣yₖ∣≤N m))
                                  (ℚP.*-monoʳ-≤-nonNeg {+ N / 1} _ (∣yₖ∣≤N n)) ⟩
      (+ N / 1) ℚ.* (+ N / 1)   ∎


{-
DISCUSSION POINTS ON THE POSSIBILITY OF THE ℝ SOLVER
----------------------------------------------------------------------------------------------------------------------------------------------------------------
Obviously, we want the ring solver to work on ℝ. It would be extremely tedious to prove any interesting result later on without the ring
solver. But there are some problems, at least right now, preventing it from working.

First, note that the ring solvers generally use rings with decidable equality. But it actually CAN work without decidable equality. The
equality can be so weak that it's not even slightly weakly decidable. As proof of concept, see the example below. 
-}

{-
sadDec : ∀ (x y : ℚᵘ) -> Maybe (x ℚ.≃ y)
sadDec x y = nothing

module ℚ-Sad-+-*-Solver =
  Solver ℚP.+-*-rawRing (ACR.fromCommutativeRing ℚP.+-*-commutativeRing) (ACR.-raw-almostCommutative⟶ (ACR.fromCommutativeRing ℚP.+-*-commutativeRing)) sadDec

testing₁ : ∀ (x y z : ℚᵘ) -> ℚ.1ℚᵘ ℚ.* (x ℚ.+ y ℚ.- z ℚ.+ 0ℚᵘ) ℚ.≃ y ℚ.- (ℚ.- x ℚ.+ z)
testing₁ x y z = solve 3 (λ x y z -> con ℚ.1ℚᵘ :* (x :+ y :- z :+ con 0ℚᵘ) := y :- (:- x :+ z)) ℚP.≃-refl x y z
  where
    open ℚ-Sad-+-*-Solver
-}

{- However, the same solution will NOT work on ℝ, at least for now, as shown below.-}
{-
≃-weaklyDec : ∀ x y -> Maybe (x ≃ y)
≃-weaklyDec x y = nothing

module ℝ-+-*-Solver =
  Solver +-*-rawRing (ACR.fromCommutativeRing +-*-commutativeRing) (ACR.-raw-almostCommutative⟶ (ACR.fromCommutativeRing +-*-commutativeRing)) ≃-weaklyDec

testing₂ : ∀ x y z -> 1ℝ * (x + y - z + 0ℝ) ≃ y - (- x + z)
testing₂ x y z = ?
  where
    open ℝ-+-*-Solver
-}
{-
The problem is ≃-refl. For some reason, it's incapable of determining implicit arguments, even in trivial cases. For instance, 0ℝ ≃ 0ℝ must be proved using
≃-refl {0ℝ}. Excluding the implicit argument results in a constraint error, as shown below.-}

{-sad0ℝ₁ : 0ℝ ≃ 0ℝ
sad0ℝ₁ = ≃-refl

sad0ℝ₂ : 0ℝ ≃ 0ℝ
sad0ℝ₂ = ≃-refl {0ℝ}
-}

{- From the constraint error, I thought it was a problem with the definition of regularity in the definition of ℝ. In particular, the issue could be
the implicit m ≢0 and n ≢0 arguments. But modifying the definition so that there are NO implicit arguments still doesn't work. I am unsure what the cause is.

So, how do we let ℝ's solver work with reflexivity proofs? Here are some proposed attempts:

(1) Prove the ring equality at the sequence level instead. This means, to prove that (x + y) - z ≃ y - (z - x), for instance, we prove it by definition of ≃
instead of by using the various ring properties of ℝ. So our proof would need to be of the form 
            ∣ (x₄ₘ + y₄ₘ - z₂ₘ) - (y₂ₘ - (z₄ₘ - x₄ₘ)) ∣ ≤ 2m⁻¹       (m∈ℤ⁺)
and we would use the ℚ ring solver to assist with it. This could be shorter, in some instances, than applying a bunch of ring properties of ℝ. But it most likely
becomes intractable when we get more difficult equalities and, for instance, when the ring equality includes multiplication (since the canonical bounds would
interfere). 

(2) Prove the ring equality for ALL rings and then apply it to ℝ. It seems to work, as shown below in testing₃, but it's very tedious and seems prone to fail.

(3) The final option I've come up with is to wait for the next Agda release, which looks to be right around the corner. I've had this "constraints that seem
trivial but Agda won't solve" issue a few times now, and it was solved by an update twice (the other time there was an easy function I could make to fix it. 
That doesn't seem to be the case here).
-}
{-
testing₃ : ∀ x y z -> x + y + z ≃ y + (z + x)
testing₃ = lem (+-*-commutativeRing)
  where
    open CommutativeRing using (Carrier; 0#; 1#; _≈_)
      renaming
        ( _+_ to _R+_
        ; _-_ to _R-_
        ; _*_ to _R*_
        ; -_  to R-_
        )
    {-
      The notation is a bit ugly, but this says
      x + y - z + 0 = 1 * (y - (z - x)).
    -}
    lem : ∀ (R : CommutativeRing 0ℓ 0ℓ) -> ∀ (x y z : Carrier R) ->
          (_≈_ R) ((_R+_ R) ((_R+_ R) x y) z)
                  ((_R+_ R) y ((_R+_ R) z x))
    lem R x y z = solve 3 (λ x y z ->
                  x :+ y :+ z := y :+ (z :+ x))
                  R-refl x y z
      where
        R-weaklyDec : ∀ x y -> Maybe ((R ≈ x) y)
        R-weaklyDec x y = nothing

        rawRing : RawRing 0ℓ 0ℓ
        rawRing = {!!}

        R-refl : Reflexive (_≈_ R)
        R-refl = {!!}

        module R-Solver =
          Solver rawRing (ACR.fromCommutativeRing R) (ACR.-raw-almostCommutative⟶ (ACR.fromCommutativeRing R)) R-weaklyDec

        open R-Solver

UPDATE
It seems (3) won't fix the problem. I tried the newest developmental release as of June 7th, 2021, and it didn't work.
Solution (2) might be promising if I can make some sort of function that says something for general rings R like
"If ϕᴿ(x₁,...,xₙ) = ψᴿ(x₁,...,xₙ) for all xᵢ∈R and for all rings R, then ϕ̂(x₁,...,xₙ) = ψ(x₁,...,xₙ) for all xᵢ∈ℝ.
That might save me the trouble of declaring a general ring solver and whatnot over and over again. Not sure if this
is possible, though.
-}

{-
If ϕ(x) = ψ(x) for all x∈R for all rings R, then ϕ(x) = ψ(x) for all x∈ℝ."
-}

{-
open CommutativeRing {{...}} using (Carrier; 0#; 1#; _≈_)
      renaming
        ( _+_ to _R+_
        ; _-_ to _R-_
        ; _*_ to _R*_
        ; -_  to R-_
        )
-}
-- This function and its counterparts are probably useless since we'd have to prove the
-- middle section anyway, which we could then directly apply in our proof instead of wasting our
-- time with this function.
{-solveMe : (ϕ ψ : (R : CommutativeRing 0ℓ 0ℓ) -> (x y z : Carrier) -> Carrier R) ->  
        (∀ (R : CommutativeRing 0ℓ 0ℓ) -> ∀ (x y z : Carrier R) -> (_≈_ R) (ϕ R x y z) (ψ R x y z)) ->
          ∀ (x y z : ℝ) -> ϕ +-*-commutativeRing x y z ≃ ψ +-*-commutativeRing x y z
solveMe ϕ ψ hyp x y z = hyp +-*-commutativeRing x y z-}

{-
R-Solver : CommutativeRing 0ℓ 0ℓ -> {!!}
R-Solver R = {!+-*-Solver!}
  where
    module +-*-Solver = Solver {!!} {!!} {!!} {!!}
    open +-*-Solver

test : ∀ {{R : CommutativeRing 0ℓ 0ℓ}} -> ∀ (x y : Carrier) -> x R+ y ≈ (y R+ x)
test x y = {!!}
  where
    module +-*-Solver = Solver {!!} {!!} {!!} {!!}
-}

0test : 0ℝ ≃ - 0ℝ
0test = ≃-refl {0ℝ}

data _≃'_ : Rel ℝ 0ℓ where
  *≃* : ∀ {x y : ℝ} -> (∀ (n : ℕ) -> {n≢0 : n ≢0} -> ℚ.∣ seq x n ℚ.- seq y n ∣ ℚ.≤ (+ 2 / n) {n≢0}) -> x ≃' y

≃'-refl : Reflexive _≃'_
≃'-refl {x} = *≃* λ { (suc k₁) → let n = suc k₁ in begin
  ℚ.∣ seq x n ℚ.- seq x n ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (seq x n)) ⟩
  0ℚᵘ                       ≤⟨ ℚP.∣p∣≃p⇒0≤p ℚP.≃-refl ⟩
  + 2 / n                    ∎}
  where open ℚP.≤-Reasoning 

test0 : ∀ p -> - (p ⋆) ≃ (ℚ.- p) ⋆
test0 p = ≃-refl { - (p ⋆)}

test3 : 0ℝ ≃ - 0ℝ
test3 = ≃-refl {0ℝ}

test2 : seq 0ℝ ≡ seq (- 0ℝ)
test2 = _≡_.refl

test4 : reg 0ℝ ≡ reg (- 0ℝ)
test4 = {!refl!}

alpha : ¬ (0ℝ ≡ - 0ℝ)
alpha hyp = {!!}

gamma : 0ℝ ≃ - 0ℝ -> 0ℝ ≡ - 0ℝ
gamma 0≃-0 = {!!}

test1 : ∀ p -> (- (p ⋆)) ≃' ((ℚ.- p) ⋆)
test1 p = {!≃'-refl {(ℚ.- p) ⋆}!}
