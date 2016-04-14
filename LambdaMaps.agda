module LambdaMaps where

open import Data.Nat
-- open import Induction.WellFounded
-- open import Induction.Nat

-- data ℕ : Set where
--  zero : ℕ
--  succ : ℕ -> ℕ

data opt (A : Set) : Set where
  some : A -> opt A
  none : opt A

data bool : Set where
 true : bool
 false : bool

data list (A : Set) : Set where
  cons : A -> list A -> list A
  nil : list A

-- _+_ : ℕ -> ℕ -> ℕ
-- zero + N = N
-- (succ N) + M = succ (N + M)

-- -- used for termination
-- data cℕ : ℕ -> Set where
--  czero : cℕ zero
--  csuc : {n : ℕ} -> cℕ n -> cℕ (suc n)
--  cplus : {n1 n2 : ℕ} -> cℕ n1 -> cℕ n2 -> cℕ (n1 + n2)

data choice : ℕ -> Set where
 here : {n : ℕ} -> choice (suc n)
 wait : {n : ℕ} -> choice n -> choice (suc n)

data nichoice : ℕ -> Set where
 loop : {n : ℕ} -> nichoice n
 nonloop : {n : ℕ} -> choice n -> bool -> nichoice n

data map (G : Set) : ℕ -> Set where
 vert : G -> map G zero
 isth : {n1 n2 : ℕ} -> map G n1 -> map G n2 -> map G (suc (n1 + n2))
 nonisth : {n : ℕ} -> map G n -> nichoice n -> map G (suc n)

data term (G : Set) : ℕ -> Set where
 head : G -> term G zero
 app : {n1 n2 : ℕ} -> term G n1 -> term (opt G) n2 -> term G (suc (n1 + n2))

data zhlist (G : Set) : ℕ -> Set where
 zhnil : zhlist G zero
 zhcons : (n1 n2 : ℕ) -> map (opt G) n1 -> zhlist G n2 -> zhlist G (suc (n1 + n2))

data φres (G : Set) : ℕ -> Set where
 φr-vert : {n : ℕ} -> zhlist G n -> G -> φres G n
 φr-nonisth : {n1 n2 : ℕ} -> zhlist G n1 -> map (opt G) n2 -> opt (nichoice n2) -> φres G (suc (n2 + n1))
 φr-underflow : φres G zero

data _≡_ : {A : Set} -> A -> A -> Set1 where
 refl : {A : Set} {a : A} -> a ≡ a

_∘_ : {A : Set} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
refl ∘ refl = refl

cong : {A B : Set} {x y : A} (f : A → B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

sym : {A : Set} {a b : A} -> a ≡ b -> b ≡ a
sym refl = refl

+lemma : (n1 n2 n3 : ℕ) -> (n1 + suc (n3 + n2)) ≡ (suc ((n1 + n3) + n2))
+lemma zero n2 n3 = refl
+lemma (suc n1) n2 n3 = cong suc (+lemma n1 n2 n3)

+comm/2 : (n : ℕ) -> n ≡ (n + zero)
+comm/2 zero = refl
+comm/2 (suc n) = cong suc (+comm/2 n)

+comm/1 : (n1 n2 : ℕ) -> suc (n1 + n2) ≡ (n1 + suc n2)
+comm/1 zero n2 = refl
+comm/1 (suc n1) n2 = cong suc (+comm/1 n1 n2)

+comm : (n1 n2 : ℕ) -> (n1 + n2) ≡ (n2 + n1)
+comm zero n1 = +comm/2 n1
+comm (suc n1) n2 = cong suc (+comm n1 n2) ∘ +comm/1 n2 n1

φres-cong : {G : Set} {n1 n2 : ℕ} -> φres G n1 -> n1 ≡ n2 -> φres G n2
φres-cong pf refl = pf

φ : {G : Set} -> {n1 n2 : ℕ} -> map (opt G) n1 -> zhlist G n2 -> φres G (n1 + n2)
φ (vert (some g)) s = φr-vert s g
φ (vert none) zhnil = φr-underflow
φ (vert none) (zhcons _ _ h s) = φr-nonisth s h none
φ {_} {_} {n2} (isth {n3} {n4} h1 h2) s = φres-cong (φ h1 (zhcons _ _ h2 s)) (+lemma n3 n2 n4)
φ (nonisth h ν) s = φr-nonisth s h (some ν)

data τres (G : Set) (Q : ℕ -> Set) : ℕ -> Set where
 τr-vert : G -> τres G Q zero
 τr-isth : {n n1 n2 : ℕ} -> Q n1 -> Q n2 -> τres G Q (suc (n1 + n2))
 τr-nonisth : {n : ℕ} -> Q n -> nichoice n -> τres G Q (suc n)

data gzh (G : Set) : ℕ -> Set where
 ! : {n : ℕ} -> G -> zhlist G n -> gzh G n

predelay' : {n : ℕ} -> (m : ℕ) -> choice n -> choice (m + n)
predelay' zero c = c
predelay' (suc m) c = wait (predelay' m c)

choice-cong : {n1 n2 : ℕ} -> choice n1 -> n1 ≡ n2 -> choice n2
choice-cong χ refl = χ

predelay : {n : ℕ} -> (m : ℕ) -> choice n -> choice (n + m)
predelay {n} m χ = choice-cong (predelay' m χ) (+comm m n)

postdelay : {n : ℕ} -> (m : ℕ) -> choice n -> choice (n + m)
postdelay m here = here
postdelay m (wait c) = (wait (postdelay m c))

assoc : (n1 n2 n3 : ℕ) -> (n1 + (n3 + n2)) ≡ ((n1 + n3) + n2)
assoc zero n2 n3 = refl
assoc (suc n1) n2 n3 = cong suc (assoc n1 n2 n3)

zhlist-cong : {G : Set} (n1 n2 : ℕ) -> zhlist G n1 -> n1 ≡ n2 -> zhlist G n2
zhlist-cong n1 .n1 zh refl = zh

zhconcat : {G : Set} (n1 n2 : ℕ) -> zhlist G n1 -> zhlist G n2 -> zhlist G (n1 + n2)
zhconcat .zero n2 zhnil w = w
zhconcat .(suc (n1 + n3)) n2 (zhcons n1 n3 x zh1) zh2 =
 zhlist-cong _ _ (zhcons _ _ x (zhconcat _ _ zh1 zh2)) (cong suc (assoc n1 n2 n3))

aux : {n1 n2 : ℕ} {G : Set} -> G -> φres G n1 -> zhlist G n2 -> τres G (gzh G) (suc (n1 + n2))
aux {_} {n2} g1 (φr-vert s1 g2) s2 = τr-isth {_} {_} {n2} (! g1 s1) (! g2 s2)
{-
This case is the trickiest of this function. We have
g   : .G
x   : zhlist .G .n1
y   : map (opt .G) .n3
z   : opt (nichoice .n3)
s   : zhlist .G .n2

and in
τr-nonisth ?2 (nonloop ?3 ?4)
we need
?2 : gzh .G (suc (.n3 + .n1) + .n2)
?3 : choice (suc (.n3 + .n1) + .n2)
?4 : bool

The ?2 is built from g, x, y, s.
The number of choices in z : opt (nichoice .n3) is 2 * n3 + 2,
which feeds into the (n3 + 1) branches of ?3, and we siphon off a bool.
The n1 and n2 branches of ?3 correspond to other ways of constructing the
list
x @ [y] @ s
-}
aux {_} {n2} g (φr-nonisth {n1} {n3} x y z) s =
  τr-nonisth (! g (zhconcat (suc (n3 + n1)) n2 (zhcons n3 n1 y x) s))
             (process-choices n1 n2 n3 z)
  where
  process-choices : (n1 n2 n3 : ℕ) -> opt (nichoice n3) -> nichoice (suc (n3 + n1) + n2)
  process-choices n1 n2 n3 (some loop) = nonloop here true
  process-choices n1 n2 n3 (some (nonloop ν β)) = nonloop (wait (predelay n2 (postdelay n1 ν))) β
  process-choices n1 n2 n3 none = nonloop here false

aux g φr-underflow s = τr-nonisth (! g s) loop

τ : {G : Set} {n : ℕ} -> gzh G n -> τres G (gzh G) n
τ (! g zhnil) = τr-vert g
τ {G} (! g (zhcons n1 n2 h s)) = aux g h' s where
 h' : φres G n1
 h' = φres-cong (φ h zhnil) (+comm n1 zero)

data Acc (x : ℕ) : Set where
  acc : (∀ y → (y <′ x) → Acc y) → Acc x

base : ∀ y -> (y <′ zero) -> Acc y
base _ ()

gen-acc : (n : ℕ) -> Acc n
gen-acc n = acc (gen-acc-aux n)
  where
  gen-acc-aux : (n : ℕ) (y : ℕ) → y <′ n → Acc y
  gen-acc-aux n zero le = acc base
  gen-acc-aux .(suc (suc y)) (suc y) ≤′-refl = gen-acc (suc y)
  gen-acc-aux ._ (suc y) (≤′-step le) = gen-acc-aux _ (suc y) le

≤-0 : (n : ℕ) -> zero ≤′ n
≤-0 zero = ≤′-refl
≤-0 (suc n) = ≤′-step (≤-0 n)

≤-suc : {n1 n2 : ℕ} -> n1 ≤′ n2 -> suc n1 ≤′ suc n2
≤-suc ≤′-refl = ≤′-refl
≤-suc(≤′-step x) = ≤′-step (≤-suc x)

≤-lemma-1 : (n1 n2 : ℕ) -> n1 ≤′ (n1 + n2)
≤-lemma-1 zero n2 = ≤-0 n2
≤-lemma-1 (suc n1) n2 = ≤-suc (≤-lemma-1 n1 n2)

≤-lemma-2 : (n1 n2 : ℕ) -> n2 ≤′ (n1 + n2)
≤-lemma-2 zero n2 = ≤′-refl
≤-lemma-2 (suc n1) n2 = ≤′-step (≤-lemma-2 n1 n2)

make-map : (G : Set) (Q : ℕ -> Set) -> ({n : ℕ} -> Q n -> τres G Q n) -> (n : ℕ) -> Q n -> map G n
make-map G Q f n q = match n (gen-acc n) (f q) where
 match : (n : ℕ) -> Acc n -> (τres G Q n) -> map G n
 match zero α (τr-vert g) = vert g
 match _ (acc ψ) (τr-isth {_} {n1} {n2} q1 q2) =
       isth {G} {n1} {n2}
            (match n1 (ψ n1 (≤-suc (≤-lemma-1 n1 n2))) (f q1))
            (match n2 (ψ n2 (≤-suc (≤-lemma-2 n1 n2))) (f q2))
 match _ (acc ψ) (τr-nonisth {n} q ν) = nonisth (match n (ψ n ≤′-refl) (f q)) ν

use-τ : (G : Set) (n : ℕ) -> gzh G n -> map G n
use-τ G n term = make-map G (gzh G) τ n term
