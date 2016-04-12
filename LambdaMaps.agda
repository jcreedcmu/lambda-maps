module LambdaMaps where

data ℕ : Set where
 zero : ℕ
 succ : ℕ -> ℕ

-- data _+_ (A B : Set) : Set where
--   lt : A -> A + B
--   rt : B -> A + B

data opt (A : Set) : Set where
  some : A -> opt A
  none : opt A

data bool : Set where
 true : bool
 false : bool

data list (A : Set) : Set where
  cons : A -> list A -> list A
  nil : list A

_+_ : ℕ -> ℕ -> ℕ
zero + N = N
(succ N) + M = succ (N + M)

data nichoice : ℕ -> Set where
 loop : nichoice zero
 cw : {n : ℕ} -> nichoice n -> nichoice (succ n)
 ccw : {n : ℕ} -> nichoice n -> nichoice (succ n)

data map (G : Set) : ℕ -> Set where
 vert : G -> map G zero
 isth : {n1 n2 : ℕ} -> map G n1 -> map G n2 -> map G (succ (n1 + n2))
 nonisth : {n : ℕ} -> map G n -> nichoice n -> map G (succ n)

data term (G : Set) : ℕ -> Set where
 head : G -> term G zero
 app : {n1 n2 : ℕ} -> term G n1 -> term (opt G) n2 -> term G (succ (n1 + n2))

data zhlist (G : Set) : ℕ -> Set where
 zhnil : zhlist G zero
 zhcons : {n1 n2 : ℕ} -> map (opt G) n1 -> zhlist G n2 -> zhlist G (succ (n1 + n2))

data φres (G : Set) : ℕ -> Set where
 φr-vert : {n : ℕ} -> zhlist G n -> G -> φres G n
 φr-nonisth : {n1 n2 : ℕ} -> zhlist G n1 -> map (opt G) n2 -> opt (nichoice n2) -> φres G (succ (n2 + n1))
 φr-underflow : φres G zero

data _≡_ : {A : Set} -> A -> A -> Set1 where
 refl : {A : Set} {a : A} -> a ≡ a

+lemma : (n1 n2 n3 : ℕ) -> (n1 + succ (n3 + n2)) ≡ (succ ((n1 + n3) + n2))
+lemma = {!!}

+comm : (n1 n2 : ℕ) -> (n1 + n2) ≡ (n2 + n1)
+comm = {!!}

φres-cong : {G : Set} {n1 n2 : ℕ} -> φres G n1 -> n1 ≡ n2 -> φres G n2
φres-cong pf refl = pf

φ : {G : Set} -> {n1 n2 : ℕ} -> map (opt G) n1 -> zhlist G n2 -> φres G (n1 + n2)
φ (vert (some g)) s = φr-vert s g
φ (vert none) zhnil = φr-underflow
φ (vert none) (zhcons h s) = φr-nonisth s h none
φ {_} {_} {n2} (isth {n3} {n4} h1 h2) s = φres-cong (φ h1 (zhcons h2 s)) (+lemma n3 n2 n4)
φ (nonisth h ν) s = φr-nonisth s h (some ν)

data τres (G : Set) (Q : ℕ -> Set) : ℕ -> Set where
 τr-vert : G -> τres G Q zero
 τr-isth : {n n1 n2 : ℕ} -> Q n1 -> Q n2 -> τres G Q (succ (n1 + n2))
 τr-nonisth : {n : ℕ} -> Q n -> nichoice n -> τres G Q (succ n)

data gzh (G : Set) : ℕ -> Set where
 ! : {n : ℕ} -> G -> zhlist G n -> gzh G n

aux : {n1 n2 : ℕ} {G : Set} -> G -> φres G n1 -> zhlist G n2 -> τres G (gzh G) (succ (n1 + n2))
aux {_} {n2} g1 (φr-vert s1 g2) s2 = τr-isth {_} {_} {n2} (! g1 s1) (! g2 s2)
aux g (φr-nonisth x x₁ x₂) s = {!!}
aux g φr-underflow s = {!!}

τ : {G : Set} {n : ℕ} -> gzh G n -> τres G (gzh G) n
τ (! g zhnil) = τr-vert g
τ {G} (! g (zhcons {n1} {n2} h s)) = aux g h' s where
 h' : φres G n1
 h' = φres-cong (φ h zhnil) (+comm n1 zero)
