{-# OPTIONS --without-K --safe #-}

open import Data.Bool.Base using (Bool; if_then_else_)
open import Data.Integer.Base as ℤ
  using (ℤ; +_; +0; +[1+_]; -[1+_]; +<+; +≤+; -_)
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
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; mkℚᵘ; _-_; _≤_; _≢0; _+_; *≤*; _/_; 0ℚᵘ; ∣_∣; _<_; ↥_; ↧_; ↧ₙ_)
open import Data.Rational.Unnormalised.Properties as ℚP
open import Algebra.Bundles
open import Algebra.Structures
open import Data.Empty

open ℚᵘ

record ℝ : Set where
  constructor mkℝ
  field
    -- No n≢0 condition for seq
    seq : ℕ -> ℚᵘ
    reg : ∀ (m n : ℕ) -> {m≢0 : m ≢0} -> {n≢0 : n ≢0} ->
          ∣ seq m - seq n ∣ ≤ ((+ 1) / m) {m≢0} + ((+ 1) / n) {n≢0}


   {-
     |xn - xm| ≤ 1/m + 1/n
   -}
    {- Old reg :
    2n   2n != 0
    
    2n+1
    x₂n
    n = zero
    n = suc m
    reg : ∀ (m n : ℕ) -> ∣ seq (suc m) - seq (suc n) ∣ ≤ ((+ 1) / (suc m)) + ((+ 1) / (suc n))
    -}

open ℝ

_≃_ : Rel ℝ 0ℓ
x ≃ y = ∀ (n : ℕ) -> {n≢0 : n ≢0} ->
        ∣ seq x n - seq y n ∣ ≤ ((+ 2) / n) {n≢0}

-- mkℚᵘ (+ 1) n-1 
-- Note the "suc n" input
-- (+ 1) / n = mkℚᵘ (+ 1) n-1
-- _ / _ : ℤ -> (n : ℕ) -> {n ≢0}
--  / (suc m) = mkℚᵘ ? m
-- (+ 1) / n = mkℚᵘ (+ 1) (pred n)
-- numerator ((+ 1) / n)
-- ((+ 1) / n) * ((+ 3) / m) =
-- 
ℝ-Refl : Reflexive _≃_
ℝ-Refl {x} (suc n) {n≢0} = lem ∣ mySeq - mySeq ∣ 0ℚᵘ (mkℚᵘ (+ 2) n) (∣-∣-cong (+-inverseʳ mySeq)) (∣p∣≃p⇒0≤p ≃-refl)
  where
    mySeq : ℚᵘ
    mySeq = seq x (suc n)

    lem : ∀ (p q r : ℚᵘ) -> p ℚ.≃ q -> q ≤ r -> p ≤ r
    lem p q r p≃q q≤r = ≤-respˡ-≃ (≃-sym p≃q) q≤r

ℝ-Symm : Symmetric _≃_
ℝ-Symm {x} {y} x≃y (suc n) {n≢0} = ≤-respˡ-≃ (≃-sym lemE) (x≃y (suc n) {n≢0})
  where
    lemA : ℚ.- (seq y (suc n) - seq x (suc n)) ℚ.≃ ℚ.- seq y (suc n) - (ℚ.- seq x (suc n))
    lemA = ≃-reflexive (neg-distrib-+ (seq y (suc n)) (ℚ.- seq x (suc n)))

    lemB : ℚ.- seq y (suc n) - (ℚ.- seq x (suc n)) ℚ.≃ ℚ.- seq y (suc n) + seq x (suc n)
    lemB = +-congʳ (ℚ.- seq y (suc n)) (neg-involutive (seq x (suc n)))

    lemC : ℚ.- seq y (suc n) + seq x (suc n) ℚ.≃ seq x (suc n) - seq y (suc n)
    lemC = +-comm (ℚ.- seq y (suc n)) (seq x (suc n))

    lemD : ℚ.- (seq y (suc n) - seq x (suc n)) ℚ.≃ seq x (suc n) - seq y (suc n)
    lemD = ≃-trans (≃-trans lemA lemB) lemC

    lemE : ∣ seq y (suc n) - seq x (suc n) ∣ ℚ.≃ ∣ seq x (suc n) - seq y (suc n) ∣
    lemE = ≃-trans (≃-sym (∣-p∣≃∣p∣ (seq y (suc n) - seq x (suc n)))) (∣-∣-cong lemD)

lemma1A : ∀ (x y : ℝ) -> x ≃ y -> ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
          ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> N ℕ.< n ->
          ∣ seq x n - seq y n ∣ ≤ ((+ 1) / j) {j≢0}
lemma1A x y x≃y (suc j) {j≢0} = 2 ℕ.* (suc j) ,
        λ { (suc n) N<n → ≤-trans (x≃y (suc n)) (*≤* (+≤+ (ℕP.<⇒≤ (subst (ℕ._<_ (2 ℕ.* (suc j))) (cong suc (sym (ℕP.+-identityʳ n))) N<n))))}

{-

Suppose that, for all j in ℕ, there is N in ℕ such that n≥N implies
              ∣ xₙ - yₙ ∣ ≤ 1/j.
For all m in ℕ such that m ≥ max{j, N}, we have:
∣ xₙ - yₙ ∣ ≤ ∣ xₙ - xₘ ∣ + ∣ xₘ - yₘ ∣ + ∣ yₘ - yₙ ∣
            ≤ (1/n) + (1/m) + (1/j) + (1/n + 1/m)
            = (2/n) + (2/m) + (1/j)
            ≤ (2/n) + (2/m) + (1/j)
            = (2/n) + (3/j).
Then ∣ xₙ - yₙ ∣ ≤ (2/n) + (3/j) for all j in ℕ.

-}

{-
Theorem (Archimedean Property of ℚ):
(i)  For every rational number r, there is a natural number N such that r < N.
(ii) For every rational number r > 0, there is a natural number N such that 1/N < r.
Proof:
(i) Let (p/q)∈ℚ. Either p=q, p>q, or p<q.
  Case 1: Suppose p=q. Then p/q = 1, and 1 < 2.
  Case 2: Suppose p>q. By the division algorithm on ℤ, p = qr + t for some r, t in ℤ such that
          0 ≤ ∣t∣ < ∣q∣. Then p/q = (qr+t)/q = t/q + qr/q = t/q + r. Since ∣t∣ < ∣q∣, we have
          t/q < 1. Then p/q < 1 + r ≤ 1 + ∣r∣, where 1 + ∣r∣ is in ℕ.
  Case 3: Suppose p<q. Then p/q < 1.
In each case, we have found a natural number N such that p/q < N. Hence (i) holds.
(ii) Follows immediately from (i).                                                           □

-}

-- This is an older version of the Archimedean property. There's a more powerful one below
-- all of this.
abstract
  help : ∀ (p q : ℤ) -> ∀ (r : ℕ) -> {r≢0 : r ≢0} -> ((p ℤ.+ q) / r) {r≢0} ℚ.≃ (p / r) {r≢0}  + (q / r) {r≢0}
  help p q (suc r) = ℚ.*≡* (trans (sym (ℤP.*-assoc (p ℤ.+ q) (+ (suc r)) (+ (suc r)))) (cong (λ x → x ℤ.* + suc r) (ℤP.*-distribʳ-+ (+ (suc r)) p q)))

  no-0-divisors : ∀ (m n : ℕ) -> m ≢0 -> n ≢0 -> m ℕ.* n ≢0
  no-0-divisors (suc m) (suc n) m≢0 n≢0 with (suc m) ℕ.* (suc n) ℕ.≟ 0
  ...                                   | res = _

  -- EXTREMELY slow when ℚ.*≡* is used to prove it. No idea why.
  ℚ-CollapseR : ∀ (p : ℤ) -> ∀ (q r : ℕ) -> {q≢0 : q ≢0} -> {r≢0 : r ≢0} ->
              ((p ℤ.* (+ q)) / (r ℕ.* q)) {no-0-divisors r q r≢0 q≢0} ℚ.≃ (p / r) {r≢0}
  ℚ-CollapseR p (suc q) (suc r) = ℚ.*≡* (trans (ℤP.*-assoc p (+ (suc q)) (+ (suc r))) (cong (λ x -> p ℤ.* x) (ℤP.*-comm (+ (suc q)) (+ (suc r)))))

  ℚ-CollapseL : ∀ (p q r : ℕ) -> {p≢0 : p ≢0} -> {q≢0 : q ≢0} -> {r≢0 : r ≢0} ->
              (((+ p) ℤ.* (+ q)) / (p ℕ.* r)) {no-0-divisors p r p≢0 r≢0} ℚ.≃ ((+ q) / r) {r≢0} 
  ℚ-CollapseL (suc p) (suc q) (suc r) = ℚ.*≡* (trans (cong (λ x -> x ℤ.* (+ (suc r))) (ℤP.*-comm (+ (suc p)) (+ (suc q)))) (ℤP.*-assoc (+ (suc q)) (+ (suc p)) (+ (suc r))))

  m≤∣m∣ : ∀ (m : ℤ) -> m ℤ.≤ + ℤ.∣ m ∣
  m≤∣m∣ (+_ n) = ℤP.≤-reflexive _≡_.refl
  m≤∣m∣ (-[1+_] n) = ℤ.-≤+

  archimedean-ℚi : ∀ (r : ℚᵘ) -> ∃ λ (N : ℕ) -> r < (+ N) / 1
  archimedean-ℚi (mkℚᵘ p q-1) = 1 ℕ.+ ℤ.∣ t ∣ , ≤-<-trans (≤-reflexive part1) (≤-<-trans (≤-reflexive part2) (≤-<-trans (≤-reflexive part3)
                                            (≤-<-trans (≤-reflexive part4) part8)))
                 where
                 q : ℕ
                 q = suc (q-1)

                 r : ℕ
                 r = p modℕ q

                 t : ℤ
                 t = p divℕ q

                 part1 : p / q ℚ.≃ ((+ r) ℤ.+ (t ℤ.* (+ q))) / q
                 part1 = ≃-reflexive (/-cong (a≡a%ℕn+[a/ℕn]*n p q) _≡_.refl _ _)

                 part2 : ((+ r) ℤ.+ (t ℤ.* (+ q))) / q ℚ.≃ ((+ r) / q) + ((t ℤ.* (+ q)) / q)
                 part2 = help (+ r) (t ℤ.* (+ q)) q

                 part3 : ((+ r) / q) + ((t ℤ.* (+ q)) / q) ℚ.≃ ((+ r) / q) + ((t ℤ.* (+ q)) / (1 ℕ.* q))
                 part3 = ≃-reflexive (cong (λ x -> ((+ r) / q) + x) (/-cong {t ℤ.* (+ q)} {q} {t ℤ.* (+ q)} {1 ℕ.* q} _≡_.refl (sym (ℕP.*-identityˡ q)) _ _))

                 --Very slow. The source is ℚ-CollapseR.
                 part4 : ((+ r) / q) + ((t ℤ.* (+ q)) / (1 ℕ.* q)) ℚ.≃ ((+ r) / q) + (t / 1)
                 part4 = +-congʳ ((+ r) / q) (ℚ-CollapseR t q 1)

                 part5 : ((+ r) / q) + (t / 1) < ((+ q) / q) + (t / 1)
                 part5 = +-monoˡ-< (t / 1) {+ r / q} {+ q / q} (_<_.*<* (ℤP.*-monoʳ-<-pos q-1 {+ r} {+ q} (+<+ (n%ℕd<d p q))))

                 part6 : ((+ r) / q) + (t / 1) < ((+ 1) / 1) + (t / 1)
                 part6 = <-respʳ-≃ (+-congˡ (t / 1) {(+ q) / q} {(+ 1) / 1} (ℚ.*≡* (trans (ℤP.*-identityʳ (+ q)) (sym (ℤP.*-identityˡ (+ q)))))) part5

                 part7a : t ℤ.* (+ 1) ℤ.≤ (+ ℤ.∣ t ∣) ℤ.* (+ 1)
                 part7a = ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-identityʳ t)) (ℤP.≤-trans (m≤∣m∣ t) (ℤP.≤-reflexive (sym (ℤP.*-identityʳ (+ ℤ.∣ t ∣)))))

                 --Very slow for some reason, not sure why.
                 part7 : ((+ r) / q) + (t / 1) < ((+ 1) / 1) + ((+ ℤ.∣ t ∣) / 1)
                 part7 = <-≤-trans part6 (+-monoʳ-≤ ((+ 1) / 1) {t / 1} {(+ ℤ.∣ t ∣) / 1} (*≤* part7a))

                 part8 : ((+ r) / q) + (t / 1) < ((+ 1) ℤ.+ (+ ℤ.∣ t ∣)) / 1
                 part8 = <-≤-trans part7 (≤-reflexive (≃-sym (help (+ 1) (+ ℤ.∣ t ∣) 1)))

-- This proof taken from a private submodule in the standard library properties for unnormalized rationals
pos⇒≢0 : ∀ p → ℚ.Positive p → ℤ.∣ ↥ p ∣ ≢0
pos⇒≢0 p p>0 = fromWitnessFalse (contraposition ℤP.∣n∣≡0⇒n≡0 (≢-sym (ℤP.<⇒≢ (ℤP.positive⁻¹ p>0))))

0<⇒pos : ∀ p -> 0ℚᵘ < p -> ℚ.Positive p
0<⇒pos p p>0 = ℚ.positive p>0

-- New (and complete) Archimedean property.
-- Abstract due to possible performance issues.
-- p > 0, r
-- r < np

{-
 p/q > 0, u/v
 qu = pvt + r

 u/v < n(p/q)
 uq < npv
 uq = (pv)t + r    r < pv
    < (pv)t + pv
    = pv(t + 1)
    ≤ pv ∣t+1∣

-}
abstract
  complete-archimedean-ℚ : ∀ (p r : ℚᵘ) -> ℚ.Positive p -> ∃ λ (N : ℕ) -> r < ((+ N) ℤ.* (↥ p)) / (↧ₙ p)
  complete-archimedean-ℚ (mkℚᵘ (+ p) q-1) (mkℚᵘ u v-1) p/q>0 = ℤ.∣ (+ 1) ℤ.+ t ∣ , part9
    where
      q : ℕ
      q = suc q-1

      v : ℕ
      v = suc v-1

      p≢0 : False (p ℕ.≟ 0)
      p≢0 = pos⇒≢0 ((+ p) / q) p/q>0

      pv≢0 : p ℕ.* v ≢0
      pv≢0 = no-0-divisors p v p≢0 _

      r : ℕ
      r = (((+ q) ℤ.* u) modℕ (p ℕ.* v)) {pv≢0}

      t : ℤ
      t = (((+ q) ℤ.* u) divℕ (p ℕ.* v)) {pv≢0}

      part1 : u ℤ.* (+ q) ≡ (+ r) ℤ.+ (t ℤ.* (+ (p ℕ.* v)))
      part1 = trans (ℤP.*-comm u (+ q)) (a≡a%ℕn+[a/ℕn]*n ((+ q) ℤ.* u) (p ℕ.* v))

      part2 : (+ r) ℤ.+ (t ℤ.* (+ (p ℕ.* v))) ℤ.< (+ (p ℕ.* v)) ℤ.+ (t ℤ.* (+ (p ℕ.* v)))
      part2 = ℤP.+-monoˡ-< (t ℤ.* (+ (p ℕ.* v))) (+<+ (n%d<d ((+ q) ℤ.* u) (+ (p ℕ.* v))))

      part3 : (+ (p ℕ.* v)) ℤ.+ (t ℤ.* (+ (p ℕ.* v))) ≡ ((+ 1) ℤ.* (+ (p ℕ.* v))) ℤ.+ (t ℤ.* (+ (p ℕ.* v)))
      part3 = cong (λ x -> x ℤ.+ (t ℤ.* (+ (p ℕ.* v)))) (sym (ℤP.*-identityˡ (+ (p ℕ.* v))))

      part4 : ((+ 1) ℤ.* (+ (p ℕ.* v))) ℤ.+ (t ℤ.* (+ (p ℕ.* v))) ≡ ((+ 1) ℤ.+ t) ℤ.* (+ (p ℕ.* v))
      part4 = sym (ℤP.*-distribʳ-+ (+ (p ℕ.* v)) (+ 1) t)

      part5 : ((+ 1) ℤ.+ t) ℤ.* (+ (p ℕ.* v)) ℤ.≤ (+ ℤ.∣ (+ 1) ℤ.+ t ∣) ℤ.* (+ (p ℕ.* v))
      part5 = ℤP.*-monoʳ-≤-nonNeg (p ℕ.* v) (m≤∣m∣ ((+ 1) ℤ.+ t))

      part6 : u ℤ.* (+ q) ℤ.< ((+ 1) ℤ.+ t) ℤ.* (+ (p ℕ.* v))
      part6 = ℤP.≤-<-trans (ℤP.≤-reflexive part1) (ℤP.<-≤-trans part2 (ℤP.≤-reflexive (trans part3 part4)))

      part7 : (+ ℤ.∣ (+ 1) ℤ.+ t ∣) ℤ.* (+ (p ℕ.* v)) ℤ.≤ (+ ℤ.∣ (+ 1) ℤ.+ t ∣) ℤ.* ((+ p) ℤ.* (+ v))
      part7 = ℤP.≤-reflexive (cong (λ x -> (+ ℤ.∣ (+ 1) ℤ.+ t ∣) ℤ.* x) (sym (ℤP.pos-distrib-* p v)))

      part8 : ((+ 1) ℤ.+ t) ℤ.* (+ (p ℕ.* v)) ℤ.≤ (+ ℤ.∣ (+ 1) ℤ.+ t ∣) ℤ.* ((+ p) ℤ.* (+ v))
      part8 = ℤP.≤-trans part5 part7

      part9 : u / v < ((+ ℤ.∣ (+ 1) ℤ.+ t ∣) ℤ.* (+ p)) / q
      part9 = _<_.*<* (ℤP.<-≤-trans (ℤP.<-≤-trans part6 part8) (ℤP.≤-reflexive (sym (ℤP.*-assoc (+ ℤ.∣ (+ 1) ℤ.+ t ∣) (+ p) (+ v)))))
    
{-
The following theorem is useless as of right now, but it's been left it here for future reference.
Theorem (Density of ℚ in itself):
  For all rational numbers p, r such that p < r, there is a rational number q such that
p < q < r.
Proof:
  Let p,r∈ℚ such that p < r. Then r - p > 0. By the Archimedean Property of ℚ, there exists N∈ℕ
such that r - p > 1/N. Then p < p + 1/N < r, where p + 1/N is rational, so we are done.      □
-}
{-
density-of-ℚ-in-ℚ : ∀ (p r : ℚᵘ) -> p < r -> ∃ λ (q : ℚᵘ) ->
                    p < q
density-of-ℚ-in-ℚ p r p<r = {!!} , {!!}
-}

{-
∣ xn - yn ∣ ≤ (2/n) + (3/j) for all j in N
⇒ ∣ xn - yn ∣ ≤ 2/n
Proof:
  Suppose, towards contradiction, that ∣ xn - yn ∣ > 2/n. Then
                           0 < ∣ xn - yn ∣ - 2/n.
By the Archimedean Property, there is N∈ℕ such that 
                           3 < N*(∣ xn - yn ∣ - 2/n).
We then get
                           3/N < ∣ xn - yn ∣ - 2/n,
or, equivalently,
                     2/n + 3/N < ∣ xn - yn ∣
for some N∈ℕ. But this contradicts our assumption that gives
                   ∣ xn - yn ∣ ≤ 2/n + 3/N.
Hence ∣ xn - yn ∣ ≤ 2/n.                                            □
-}
alternate : ∀ (p : ℚᵘ) -> ∀ (N : ℕ) -> ((+ N) ℤ.* (↥ p)) / (↧ₙ p) ℚ.≃ ((+ N) / 1) ℚ.* p
alternate p N = ℚ.*≡* (cong (λ x -> ((+ N) ℤ.* (↥ p)) ℤ.* x) (ℤP.*-identityˡ (↧ p)))

get0ℚᵘ : ∀ (n : ℕ) -> {n≢0 : n ≢0} -> ((+ 0) / n) {n≢0} ℚ.≃ 0ℚᵘ
get0ℚᵘ (suc n) = ℚ.*≡* (trans (ℤP.*-zeroˡ (+ 1)) (sym (ℤP.*-zeroˡ (+ (suc n)))))

lemma1B : ∀ (x y : ℝ) -> (∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∃ λ (N : ℕ) ->
          ∀ (n : ℕ) -> N ℕ.< n ->
          ∣ seq x n - seq y n ∣ ≤ ((+ 1) / j) {j≢0}) -> x ≃ y
lemma1B x y hyp (suc n) = lemA lemB
  where
    ∣xn-yn∣ : ℚᵘ
    ∣xn-yn∣ = ∣ seq x (suc n) - seq y (suc n) ∣

    2/n : ℚᵘ
    2/n = (+ 2) / (suc n)
    
    lemA : (∀ (j : ℕ) -> {j≢0 : j ≢0} ->
          ∣ seq x (suc n) - seq y (suc n) ∣ ≤ ((+ 2) / (suc n)) + ((+ 3) / j) {j≢0}) ->
          ∣ seq x (suc n) - seq y (suc n) ∣ ≤ ((+ 2) / (suc n))
    -- Trichotomy of ℚ.
    -- Note that the only hard case is the case by contradiction.
    -- These proofs aren't hard. Their implementation is really long though because of all
    -- of the algebraic manipulations, e.g. proving that
    -- xₙ - yₙ = (xₙ - zₙ) + (zₙ - yₙ). 
    lemA hyp with <-cmp ∣ seq x (suc n) - seq y (suc n) ∣ ((+ 2) / (suc n))
    ... | tri< a ¬b ¬c = <⇒≤ a
    ... | tri≈ ¬a b ¬c = ≤-reflexive b
    ... | tri> ¬a ¬b c with complete-archimedean-ℚ (∣xn-yn∣ - 2/n) ((+ 3) / 1) isPos
      where
        0<res : 0ℚᵘ < ∣xn-yn∣ - 2/n
        0<res = <-respˡ-≃ (+-inverseʳ 2/n) (+-monoˡ-< (ℚ.- 2/n) c)

        isPos : ℚ.Positive (∣xn-yn∣ - 2/n)
        isPos = ℚ.positive 0<res

    ... | 0 , 3<Nres = ⊥-elim (<-asym 3<Nres (<-respˡ-≃ (≃-sym (get0ℚᵘ _)) (positive⁻¹ {(+ 3) / 1} _)))
    ... | suc M , 3<Nres = ⊥-elim (<-irrefl ≃-refl (<-≤-trans part4 (hyp N)))
      where
        N : ℕ
        N = suc M

        part1 : (+ 3) / 1 < ((+ N) / 1) ℚ.* (∣xn-yn∣ - 2/n)
        part1 = <-respʳ-≃ (alternate (∣xn-yn∣ - 2/n) N) 3<Nres

        part2a : ((+ 1) / N) ℚ.* ((+ N) / 1) ℚ.≃ ℚ.1ℚᵘ
        part2a = ℚ.*≡* (trans (ℤP.*-identityʳ ((+ 1) ℤ.* (+ N))) (sym (trans (ℤP.*-identityˡ ((+ N) ℤ.* (+ 1))) (ℤP.*-comm (+ N) (+ 1)))))

        part2b : ((+ 1) / N) ℚ.* (((+ N) / 1) ℚ.* (∣xn-yn∣ - 2/n)) ℚ.≃ ∣xn-yn∣ - 2/n
        part2b = ≃-trans (≃-sym (*-assoc ((+ 1) / N) ((+ N) / 1) (∣xn-yn∣ - 2/n)))
                 (≃-trans (*-congʳ part2a) (ℚP.*-identityˡ (∣xn-yn∣ - 2/n)))

        part2 : ((+ 1) / N) ℚ.* ((+ 3) / 1) < ∣xn-yn∣ - 2/n
        part2 = <-respʳ-≃ part2b (*-monoʳ-<-pos {(+ 1) / N} _ part1)

        part3a : ((+ 1) / N) ℚ.* ((+ 3) / 1) ℚ.≃ (+ 3) / N
        part3a = ℚ.*≡* (trans (cong (λ x -> x ℤ.* (+ N)) (ℤP.*-identityˡ (+ 3))) (cong (λ x -> (+ 3) ℤ.* x) (sym (ℤP.*-identityʳ (+ N)))))
  
        part3 : (+ 3) / N < ∣xn-yn∣ - 2/n
        part3 = <-respˡ-≃ part3a part2

        part4 : 2/n + ((+ 3) / N) < ∣xn-yn∣
        part4 = <-respˡ-≃ (+-comm ((+ 3) / N) 2/n) (<-respʳ-≃ (≃-trans (+-congʳ ∣xn-yn∣ (+-inverseʳ 2/n)) (+-identityʳ ∣xn-yn∣))
                (<-respʳ-≃ (+-assoc ∣xn-yn∣ (ℚ.- 2/n) 2/n) (+-monoˡ-< 2/n part3)))

        part5 : ∣xn-yn∣ ≤ 2/n + ((+ 3) / N)
        part5 = hyp N

    lemB : ∀ (j : ℕ) -> {j≢0 : j ≢0} -> ∣xn-yn∣ ≤ 2/n + ((+ 3) / j) {j≢0}
    lemB (suc j) with hyp (suc j)
    ... | N , proof = ≤-trans part1 (≤-trans part2 part3)
      where
        m : ℕ
        m = (suc N) ℕ.⊔ (suc j)

        xn=xn-xm+xm : seq x (suc n) ℚ.≃ (seq x (suc n) - seq x m) + seq x m
        xn=xn-xm+xm = ≃-trans (≃-sym (+-identityʳ (seq x (suc n))))
                     (≃-trans (+-congʳ (seq x (suc n)) (≃-sym (+-inverseˡ (seq x m))))
                     (≃-sym (+-assoc (seq x (suc n)) (ℚ.- seq x m) (seq x m))))

        -yn=-ym+ym-yn : ℚ.- seq y (suc n) ℚ.≃ (ℚ.- seq y m) + (seq y m - seq y (suc n))
        -yn=-ym+ym-yn = ≃-trans (≃-sym (+-identityˡ (ℚ.- seq y (suc n))))
                        (≃-trans (+-congˡ (ℚ.- seq y (suc n)) (≃-sym (+-inverseˡ (seq y m))))
                        (+-assoc (ℚ.- seq y m) (seq y m) (ℚ.- seq y (suc n))))

        xn+yn : seq x (suc n) - seq y (suc n) ℚ.≃
                ((seq x (suc n) - seq x m) + (seq x m - seq y m)) + (seq y m - seq y (suc n))
        xn+yn = ≃-trans (+-congˡ (ℚ.- seq y (suc n)) xn=xn-xm+xm)
                (≃-trans (+-congʳ ((seq x (suc n) - seq x m) + seq x m) -yn=-ym+ym-yn)
                (≃-trans (≃-sym (+-assoc ((seq x (suc n) - seq x m) + seq x m) (ℚ.- seq y m) (seq y m - seq y (suc n))))
                (+-congˡ (seq y m - seq y (suc n)) (+-assoc (seq x (suc n) - seq x m) (seq x m) (ℚ.- seq y m)))))

        part1 : ∣ seq x (suc n) - seq y (suc n) ∣ ≤
                ∣ seq x (suc n) - seq x m ∣ + ∣ seq x m - seq y m ∣ + ∣ seq y m - seq y (suc n) ∣
        part1 = ≤-respˡ-≃ (∣-∣-cong (≃-sym xn+yn)) (≤-trans (∣p+q∣≤∣p∣+∣q∣ ((seq x (suc n) - seq x m) + (seq x m - seq y m)) (seq y m - seq y (suc n)))
                                                   (+-monoˡ-≤ ∣ seq y m - seq y (suc n) ∣ (∣p+q∣≤∣p∣+∣q∣ (seq x (suc n) - seq x m) (seq x m - seq y m))))

        part2 : ∣ seq x (suc n) - seq x m ∣ + ∣ seq x m - seq y m ∣ + ∣ seq y m - seq y (suc n) ∣ ≤
                (((+ 1) / (suc n)) + ((+ 1) / m)) + ((+ 1) / (suc j)) + (((+ 1) / m) + ((+ 1) / (suc n)))
        part2 = ≤-trans (≤-trans
                        (+-monoˡ-≤ ∣ seq y m - seq y (suc n) ∣ (+-monoˡ-≤ ∣ seq x m - seq y m ∣ (reg x (suc n) m)))
                        (+-monoˡ-≤ ∣ seq y m - seq y (suc n) ∣ (+-monoʳ-≤ (((+ 1) / (suc n)) + ((+ 1) / m))
                                           (proof m (ℕP.m≤m⊔n (suc N) (suc j))))))
                        (+-monoʳ-≤ ((((+ 1) / (suc n)) + ((+ 1) / m)) + ((+ 1) / (suc j))) (reg y m (suc n)))

        1/m≤1/j : ((+ 1) / m) ≤ (+ 1) / (suc j)
        1/m≤1/j = *≤* (ℤP.≤-trans (ℤP.≤-reflexive (ℤP.*-identityˡ (+ (suc j))))
                      (ℤP.≤-trans (+≤+ (ℕP.m≤n⊔m (suc N) (suc j)))
                      (ℤP.≤-reflexive (sym (ℤP.*-identityˡ (+ m))))))

        part3 : (((+ 1) / (suc n)) + ((+ 1) / m)) + ((+ 1) / (suc j)) + (((+ 1) / m) + ((+ 1) / (suc n))) ≤
                ((+ 2) / (suc n)) + ((+ 3) / (suc j))
        part3 = ≤-trans (+-monoʳ-≤ ((((+ 1) / (suc n)) + ((+ 1) / m)) + ((+ 1) / (suc j))) (+-monoˡ-≤ ((+ 1) / (suc n)) 1/m≤1/j))
                (≤-trans (+-monoˡ-≤ (((+ 1) / (suc j)) + ((+ 1) / (suc n))) (+-monoˡ-≤ ((+ 1) / (suc j)) (+-monoʳ-≤ ((+ 1) / (suc n)) 1/m≤1/j)))
                (≤-respˡ-≃ (+-congˡ (+ 1 / suc j + + 1 / suc n) (≃-sym (+-assoc ((+ 1) / (suc n)) ((+ 1) / (suc j)) ((+ 1) / (suc j)))))
                (≤-respˡ-≃ (+-congˡ (((+ 1) / (suc j)) + ((+ 1) / (suc n))) (+-congʳ ((+ 1) / (suc n)) (help (+ 1) (+ 1) (suc j))))
                (≤-respˡ-≃ (≃-sym (+-assoc ((+ 1) / (suc n)) ((+ 2) / (suc j)) (((+ 1) / (suc j)) + ((+ 1) / (suc n)))))
                (≤-respˡ-≃ (+-congʳ ((+ 1) / (suc n)) (+-assoc ((+ 2) / (suc j)) ((+ 1) / (suc j)) ((+ 1) / (suc n))))
                (≤-respˡ-≃ (+-congʳ ((+ 1) / (suc n)) (+-congˡ ((+ 1) / (suc n)) (help (+ 2) (+ 1) (suc j))))
                (≤-respˡ-≃ (+-comm (((+ 3) / (suc j)) + ((+ 1) / (suc n))) ((+ 1) / (suc n)))
                (≤-respˡ-≃ (≃-sym (+-assoc ((+ 3) / (suc j)) ((+ 1) / (suc n)) ((+ 1) / (suc n))))
                (≤-respˡ-≃ (+-congʳ ((+ 3) / (suc j)) (help (+ 1) (+ 1) (suc n)))
                (≤-reflexive (+-comm ((+ 3) / (suc j)) ((+ 2) / (suc n)))))))))))))

{-
(This proof is constructive for transitivity. Just need to deal
with implementation or finding a simpler proof.)
|xn - zn| ≤? 2/n
Let j∈ℕ. WTS there is N∈ℕ s.t.
                 |xn - zn| ≤ 1/j         (n≥N).
We can then apply lemma1B to get x ≃ z. 

By lemma1A, there is N₁∈ℕ s.t. 
                 |xn - yn| ≤ 1/2j         (n≥N₁).
Similarly, there is N₂∈N s.t.
                 |yn - zn| ≤ 1/2j         (n≥N₂).
Let N = max{N₁, N₂}. Then
                 |xn - yn| ≤ 1/2j         (n≥N), and
                 |yn - zn| ≤ 1/2j         (n≥N).
We have:
|xn - zn| = |xn - yn + yn - zn|
          ≤ |xn - yn| + |yn - zn| by triangle inequality
          ≤ 1/2j + 1/2j
          = 1/j
for all n≥N. Hence we are done.                       □

This proof's length is absurd because of algebraic
manipulations... Not sure of an alternative, simpler way of
proving this.
-}

ℝ-Trans : Transitive _≃_
ℝ-Trans {x} {y} {z} x≃y y≃z = lemma1B x z lem
  where
    lem : ∀ (j : ℕ) -> {j≢0 : j ≢0} ->
          ∃ λ (N : ℕ) -> ∀ (n : ℕ) -> N ℕ.< n ->
          ∣ seq x n - seq z n ∣ ≤ ((+ 1) / j) {j≢0}
    lem (suc j) {j≢0} with (lemma1A x y x≃y (2 ℕ.* (suc j))) | (lemma1A y z y≃z (2 ℕ.* (suc j)))
    lem (suc j) {j≢0} | N₁ , xy | N₂ , yz = N₁ ℕ.⊔ N₂ , partN
      where
      -- It's pretty common to take ∣xₙ - yₙ∣ = ∣(xₙ - r) + (r - yₙ)∣ ≤ ∣xₙ - r∣ + ∣r - yₙ∣ in analysis.
      -- It would probably be useful to prove that generally instead of having to do all of these
      -- manipulations all of the time.
      -- Might prove a bunch of common analysis tricks generally as I go along to cut down on the algebra.
        partA : ∀ (n : ℕ) -> seq x n - seq z n ℚ.≃ (seq x n - seq z n) + 0ℚᵘ
        partA n = ≃-sym (+-identityʳ (seq x n - seq z n))

        partB : ∀ (n : ℕ) -> (seq x n - seq z n) + 0ℚᵘ ℚ.≃ (seq x n - seq z n) + (seq y n - seq y n)
        partB n = +-congʳ (seq x n - seq z n) (≃-sym (+-inverseʳ (seq y n)))

        partC : ∀ (n : ℕ) -> (seq x n - seq z n) + (seq y n - seq y n) ℚ.≃ seq x n + ((ℚ.- seq z n) + (seq y n - seq y n))
        partC n = +-assoc (seq x n) (ℚ.- seq z n) (seq y n - seq y n)

        partD : ∀ (n : ℕ) -> seq x n + ((ℚ.- seq z n) + (seq y n - seq y n)) ℚ.≃ seq x n + (((ℚ.- seq z n) + seq y n) - seq y n)
        partD n = +-congʳ (seq x n) (≃-sym (+-assoc (ℚ.- seq z n) (seq y n) (ℚ.- seq y n)))

        partE : ∀ (n : ℕ) -> seq x n + (((ℚ.- seq z n) + (seq y n)) - seq y n) ℚ.≃ seq x n + ((ℚ.- seq y n) + ((ℚ.- seq z n) + seq y n))
        partE n = +-congʳ (seq x n) (+-comm ((ℚ.- seq z n) + seq y n) (ℚ.- seq y n))

        partF : ∀ (n : ℕ) -> seq x n + ((ℚ.- seq y n) + ((ℚ.- seq z n) + seq y n)) ℚ.≃ (seq x n - seq y n) + ((ℚ.- seq z n) + seq y n)
        partF n = ≃-sym (+-assoc (seq x n) (ℚ.- seq y n) ((ℚ.- seq z n) + seq y n))

        partG : ∀ (n : ℕ) -> (seq x n - seq y n) + ((ℚ.- seq z n) + seq y n) ℚ.≃ (seq x n - seq y n) + (seq y n - seq z n)
        partG n = +-congʳ (seq x n - seq y n) (+-comm (ℚ.- seq z n) (seq y n))

        partH : ∀ (n : ℕ) -> (seq x n - seq z n) ℚ.≃ (seq x n - seq y n) + (seq y n - seq z n)
        partH n = ≃-trans (partA n) (≃-trans (partB n) (≃-trans (partC n) (≃-trans (partD n) (≃-trans (partE n) (≃-trans (partF n) (partG n))))))

        partI : numerator (((+ 1) / (2 ℕ.* (suc j))) + ((+ 1) / (2 ℕ.* (suc j)))) ≡ (+ 2) ℤ.* (+ (2 ℕ.* (suc j)))
        partI = sym (ℤP.*-distribʳ-+ (+ (2 ℕ.* (suc j))) (+ 1) (+ 1))

        partJ : ((+ 2) ℤ.* (+ (2 ℕ.* (suc j)))) / ((2 ℕ.* (suc j)) ℕ.* (2 ℕ.* (suc j))) ℚ.≃ (+ 2) / (2 ℕ.* (suc j))
        partJ = ℚ-CollapseR (+ 2) (2 ℕ.* (suc j)) (2 ℕ.* (suc j))

        partK : (+ 2) / (2 ℕ.* (suc j)) ℚ.≃ (+ 1) / (suc j)
        partK = ≃-trans (≃-reflexive (/-cong {+ 2} {2 ℕ.* (suc j)} {(+ 2) ℤ.* (+ 1)} {2 ℕ.* (suc j)} (ℤP.*-identityˡ (+ 2)) _≡_.refl _ _)) (ℚ-CollapseL 2 1 (suc j))

        partL : (((+ 1) / (2 ℕ.* (suc j))) + ((+ 1) / (2 ℕ.* (suc j)))) ℚ.≃ (+ 1) / (suc j)
        partL = ≃-trans (≃-reflexive (/-cong partI _≡_.refl _ _)) (≃-trans partJ partK)

        partN : ∀ (n : ℕ) -> (N₁ ℕ.⊔ N₂) ℕ.< n -> ∣ seq x n - seq z n ∣ ≤ ((+ 1) / (suc j))
        partN n N<n = ≤-respˡ-≃ (∣-∣-cong (≃-sym (partH n))) (≤-trans (∣p+q∣≤∣p∣+∣q∣ (seq x n - seq y n) (seq y n - seq z n))
                     (≤-trans (+-monoˡ-≤ ∣ seq y n - seq z n ∣ (xy n (ℕP.m⊔n<o⇒m<o N₁ N₂ N<n)))
                     (≤-trans (+-monoʳ-≤ ((+ 1) / (2 ℕ.* (suc j))) (yz n (ℕP.m⊔n<o⇒n<o N₁ N₂ N<n)))
                     (≤-reflexive partL))))
