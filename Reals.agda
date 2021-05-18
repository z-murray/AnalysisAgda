{-# OPTIONS --without-K --safe #-}

open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; +0; +[1+_]; -[1+_]; +<+; +≤+)
open import Data.Integer.Properties as ℤP using (*-identityˡ)
open import Data.Integer.DivMod as ℤD
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Nat.Properties as ℕP using (≤-step)
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

{-
p/q
p = r + tq   0 ≤ r < q
p/q = (r + tq) / q = r/q + t r < q so
p/q = r/q + t < 1 + t
p/q = r/q + t

p/q < 1 + t
p/q < m < 1 + t
-> p < qm < q + qt
-> r + qt < qm < q + qt
-> r < qm - qt < q
-> r/q < m-t < 1
-> 0 < m-t < 1

p/q = (r + tq)/q = r/q + t < 1 + t
p/q < 1 + t
p/q < m < 1 + t
p < qm < q + qt
r + qt < qm < q + qt
r < qm - qt < q
r/q < m - t < 1
0 < m - t < 1
-}
{-least : ∀ (p : ℚᵘ) -> ∃ λ (K : ℤ) ->
        p ℚ.< (K / 1) × (∀ (n : ℤ) -> p ℚ.< (n / 1) -> K ℤ.≤ n)
least (mkℚᵘ p q-1) = (+ 1) ℤ.+ t , < (λ x -> {!!}) , {!!} > {!!}
  where
    q : ℕ
    q = suc q-1

    r : ℕ
    r = p modℕ q

    t : ℤ
    t = p divℕ q

K_ : ℝ -> ℤ
K x with least (ℚ.∣ seq x 1 ∣ ℚ.+ ((+ 2) / 1))
... | N , res = N-}

{-
p/q = (r + tq)/q
    = r/q + t
    < 1 + t
-}
antidensity-ℤ : ¬(∃ λ (n : ℤ) -> + 0 ℤ.< n × n ℤ.< + 1)
antidensity-ℤ (+[1+ n ] , +<+ m<n , +<+ (ℕ.s≤s ()))

least : ∀ (p : ℚᵘ) -> ∃ λ (K : ℤ) ->
        p ℚ.< (K / 1) × (∀ (n : ℤ) -> p ℚ.< (n / 1) -> K ℤ.≤ n)
least (mkℚᵘ p q-1) = (+ 1) ℤ.+ t , {!!} ,′ {!!}
  where
    q : ℕ
    q = suc q-1

    r : ℕ
    r = p modℕ q

    t : ℤ
    t = p divℕ q

    least-property : ∀ (n : ℤ) -> p / q ℚ.< n / 1 -> + 1 ℤ.+ t ℤ.≤ n
    least-property n p/q<n with + 1 ℤ.+ t ℤP.≤? n
    ... | .Bool.true because ofʸ P = P
    ... | .Bool.false because ofⁿ ¬P = ⊥-elim (antidensity-ℤ (n ℤ.- t , 0<n-t ,′ n-t<1))
      where
      0<n-t : + 0 ℤ.< n ℤ.- t
      0<n-t = ℤP.*-cancelʳ-<-nonNeg q (ℤP.≤-<-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ q))) part3)
        
        where
        open ℤP.≤-Reasoning
        open import Data.Integer.Solver
        open +-*-Solver
        part1 : (+ r) ℤ.+ t ℤ.* (+ q) ℤ.< n ℤ.* (+ q)
        part1 = begin-strict --ℤP.≤-<-trans (ℤP.≤-reflexive (sym (ℤP.*-identityʳ p))) (ℚP.drop-*<* p/q<n)
          (+ r) ℤ.+ t ℤ.* (+ q) ≡⟨ trans (sym (a≡a%ℕn+[a/ℕn]*n p q)) (sym (ℤP.*-identityʳ p)) ⟩
          p ℤ.* (+ 1)           <⟨ ℚP.drop-*<* p/q<n ⟩
          n ℤ.* (+ q) ∎

        part2 : (+ r) ℤ.< (n ℤ.- t) ℤ.* (+ q)
        part2 = begin-strict
          + r ≡⟨ solve 2 (λ r t -> r := r :+ t :- t) _≡_.refl (+ r) (t ℤ.* (+ q)) ⟩
          (+ r) ℤ.+ t ℤ.* (+ q) ℤ.- t ℤ.* (+ q) <⟨ ℤP.+-monoˡ-< (ℤ.- (t ℤ.* + q)) part1 ⟩
          n ℤ.* (+ q) ℤ.- t ℤ.* (+ q) ≡⟨ solve 3 (λ n q t -> n :* q :- t :* q := (n :- t) :* q) _≡_.refl n (+ q) t ⟩
          (n ℤ.- t) ℤ.* (+ q) ∎

        part3 : + 0 ℤ.< (n ℤ.- t) ℤ.* (+ q)
        part3 = ℤP.≤-<-trans (+≤+ ℕ.z≤n) part2

      n-t<1 : n ℤ.- t ℤ.< + 1
      n-t<1 = begin-strict {!!}
        where
          open ℤP.≤-Reasoning


infixl 6 _+_ _⊔_
infix 8 -_

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

{-
xₘ ≥ xₙ : 
∣ (xₘ ⊔ yₘ) - (xₙ ⊔ yₙ) ∣

∣ (xₘ ⊔ yₘ) - (xₙ ⊔ yₙ) ∣ = (xₘ ⊔ yₘ) - (xₙ ⊔ yₙ)
xₘ ⊔ yₘ = xₘ (xₘ ≥ yₘ)
  (xₘ ⊔ yₘ) - (xₙ ⊔ yₙ) = xₘ - (xₙ ⊔ yₙ)
                       ≤ xₘ - xₙ
                       ≤ ...

∣ (xm ⊔ ym) - (xn ⊔ yn) ∣ = (xm ⊔ ym) - (xn ⊔ yn)
                         ≤ (xm ⊔ ym) - xn
(a ⊔ b) - (c ⊔ d) ≤ a - c
                  = ∣a - c∣

                       
-}

p≃q⇒-p≃-q : ∀ (p q : ℚᵘ) -> p ℚ.≃ q -> ℚ.- p ℚ.≃ ℚ.- q
p≃q⇒-p≃-q p q p≃q = ℚP.p-q≃0⇒p≃q (ℚ.- p) (ℚ.- q) (ℚP.≃-trans (ℚP.+-comm (ℚ.- p) (ℚ.- (ℚ.- q)))
                                                 (ℚP.≃-trans (ℚP.+-congˡ (ℚ.- p) (ℚP.neg-involutive q))
                                                 (ℚP.p≃q⇒p-q≃0 q p (ℚP.≃-sym p≃q))))

p≤∣p∣ : ∀ (p : ℚᵘ) -> p ℚ.≤ ℚ.∣ p ∣
p≤∣p∣ (mkℚᵘ (+_ n) q-1) = ℚP.≤-refl
p≤∣p∣ (mkℚᵘ (-[1+_] n) q-1) = *≤* ℤ.-≤+

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

_* : ℚᵘ -> ℝ
seq (p *) n = p
reg (p *) (suc m) (suc n) = begin
  ℚ.∣ p ℚ.- p ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.p≃q⇒p-q≃0 p p ℚP.≃-refl) ⟩
  0ℚᵘ ≤⟨ ℚP.nonNegative⁻¹ _ ⟩
  ((+ 1) / (suc m)) ℚ.+ ((+ 1) / (suc n)) ∎
  where
    open ℚP.≤-Reasoning

+-comm : ∀ (x y : ℝ) -> x + y ≃ y + x
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

+-assoc : ∀ (x y z : ℝ) -> (x + y) + z ≃ x + (y + z)
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
0ℝ = 0ℚᵘ *

+-identityˡ : ∀ (x : ℝ) -> 0ℝ + x ≃ x
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

+-identityʳ : ∀ (x : ℝ) -> x + 0ℝ ≃ x
+-identityʳ x = ≃-trans {x + 0ℝ} {0ℝ + x} {x} (+-comm x 0ℝ) (+-identityˡ x)

+-inverseʳ : ∀ x -> x - x ≃ 0ℝ
+-inverseʳ x (suc k₁) = begin
  ℚ.∣ (seq x (2 ℕ.* n) ℚ.- seq x (2 ℕ.* n)) ℚ.+ 0ℚᵘ ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-congˡ 0ℚᵘ (ℚP.+-inverseʳ (seq x (2 ℕ.* n)))) ⟩
  0ℚᵘ                                                 ≤⟨ *≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ n))) (+≤+ ℕ.z≤n)) ⟩
  + 2 / n                                              ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁

+-inverseˡ : ∀ x -> (- x) + x ≃ 0ℝ
+-inverseˡ x = ≃-trans {(- x) + x} {x - x} {0ℝ} (+-comm (- x) x) (+-inverseʳ x)

ℚ*-distrib-+ : ∀ (p r : ℚᵘ) -> (p ℚ.+ r) * ≃ p * + r *
ℚ*-distrib-+ (mkℚᵘ p q-1) (mkℚᵘ u v-1) (suc k₁) = begin
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

ℚ*-distrib-neg : ∀ (p : ℚᵘ) -> (ℚ.- p) * ≃ - (p *)
ℚ*-distrib-neg p (suc k₁) = begin
  ℚ.∣ ℚ.- p ℚ.- (ℚ.- p) ∣ ≈⟨ ℚP.∣-∣-cong (ℚP.+-inverseʳ (ℚ.- p)) ⟩
  0ℚᵘ                     ≤⟨ *≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-zeroˡ (+ n))) (+≤+ ℕ.z≤n)) ⟩
  (+ 2) / n                ∎
  where
    open ℚP.≤-Reasoning
    n : ℕ
    n = suc k₁
