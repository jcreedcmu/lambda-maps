module LambdaMaps where

{------------------------------------
 Basic standard library stuff I'm
 copy-pasting here for simpler js output
 ------------------------------------}
data ℕ : Set where
 zero : ℕ
 suc : ℕ -> ℕ

_+_ : ℕ -> ℕ -> ℕ
zero + N = N
(suc N) + M = suc (N + M)

data _≤_ (m : ℕ) : ℕ → Set where
  ≤-refl :                         m ≤ m
  ≤-step : ∀ {n} (m≤n : m ≤ n) → m ≤ suc n

_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

data Opt (A : Set) : Set where
  some : A -> Opt A
  none : Opt A

data bool : Set where
 true : bool
 false : bool

data choice : ℕ -> Set where
 here : {n : ℕ} -> choice (suc n)
 wait : {n : ℕ} -> choice n -> choice (suc n)

data unit : Set where
 • : unit

postulate String : Set
{-# BUILTIN STRING String #-}

data List (A : Set) : Set where
  []   : List A
  _,_ : A → List A → List A
infixr 5 _,_

{------------------------------------
 Equality and lemmas
 ------------------------------------}

data _≡_ : {A : Set} -> A -> A -> Set1 where
 refl : {A : Set} {a : A} -> a ≡ a

_∘_ : {A : Set} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
refl ∘ refl = refl

cong : {A B : Set} {x y : A} (f : A → B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

sym : {A : Set} {a b : A} -> a ≡ b -> b ≡ a
sym refl = refl

subst : {A : Set} (B : A → Set) {a1 a2 : A} -> B a1 -> a1 ≡ a2 -> B a2
subst _ x refl = x

{------------------------------------
 Some ℕ lemmas
 ------------------------------------}

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

assoc : (n1 n2 n3 : ℕ) -> (n1 + (n3 + n2)) ≡ ((n1 + n3) + n2)
assoc zero n2 n3 = refl
assoc (suc n1) n2 n3 = cong suc (assoc n1 n2 n3)

≤-0 : (n : ℕ) -> zero ≤ n
≤-0 zero = ≤-refl
≤-0 (suc n) = ≤-step (≤-0 n)

≤-suc : {n1 n2 : ℕ} -> n1 ≤ n2 -> suc n1 ≤ suc n2
≤-suc ≤-refl = ≤-refl
≤-suc(≤-step x) = ≤-step (≤-suc x)

≤-lemma-1 : (n1 n2 : ℕ) -> n1 ≤ (n1 + n2)
≤-lemma-1 zero n2 = ≤-0 n2
≤-lemma-1 (suc n1) n2 = ≤-suc (≤-lemma-1 n1 n2)

≤-lemma-2 : (n1 n2 : ℕ) -> n2 ≤ (n1 + n2)
≤-lemma-2 zero n2 = ≤-refl
≤-lemma-2 (suc n1) n2 = ≤-step (≤-lemma-2 n1 n2)

{------------------------------------
 Well-founded induction
 ------------------------------------}

data Acc (x : ℕ) : Set where
  acc : (∀ y → (y < x) → Acc y) → Acc x

base : ∀ y -> (y < zero) -> Acc y
base _ ()

gen-acc : (n : ℕ) -> Acc n
gen-acc n = acc (gen-acc-aux n)
  where
  gen-acc-aux : (n : ℕ) (y : ℕ) → y < n → Acc y
  gen-acc-aux n zero le = acc base
  gen-acc-aux .(suc (suc y)) (suc y) ≤-refl = gen-acc (suc y)
  gen-acc-aux ._ (suc y) (≤-step le) = gen-acc-aux _ (suc y) le

{------------------------------------
 Type of maps
 ------------------------------------}

-- Choice of where to attach a nonisthmic edge.
-- There are 2n+1 such places in a map with n edges.
data nichoice : ℕ -> Set where
 loop : {n : ℕ} -> nichoice n
 nonloop : {n : ℕ} -> choice n -> bool -> nichoice n

-- A map with G-data at vertices and with n edges can be a single
-- vertex, the isthmic attachment of two maps, or a map with a
-- nonisthmically attached edge.
data map (G : Set) : ℕ -> Set where
 vert : G -> map G zero
 isth : {n1 n2 : ℕ} -> map G n1 -> map G n2 -> map G (suc (n1 + n2))
 nonisth : {n : ℕ} -> map G n -> nichoice n -> map G (suc n)

{------------------------------------
 Type of terms
 ------------------------------------}

-- term n m = term with n free variables and m applications
data term : ℕ -> ℕ -> Set where
 head : {n : ℕ} -> choice n -> term n zero
 app : {n m1 m2 : ℕ} -> term n m1 -> term (suc n) m2 -> term n (suc (m1 + m2))

{------------------------------------
 Auxiliary datastructures and defns for converting terms to maps
 ------------------------------------}

-- A useful intermediate data structure whose elements are each a
-- detached edge plus a map with G+1 vertex data
data zhlist (G : Set) : ℕ -> Set where
 zhnil : zhlist G zero
 zhcons : (n1 n2 : ℕ) -> map (Opt G) n1 -> zhlist G n2 -> zhlist G (suc (n1 + n2))

-- One of those such lists plus a G at the head
data gzh (G : Set) : ℕ -> Set where
 ! : {n : ℕ} -> G -> zhlist G n -> gzh G n

predelay' : {n : ℕ} -> (m : ℕ) -> choice n -> choice (m + n)
predelay' zero c = c
predelay' (suc m) c = wait (predelay' m c)

predelay : {n : ℕ} -> (m : ℕ) -> choice n -> choice (n + m)
predelay {n} m χ = subst choice (predelay' m χ) (+comm m n)

postdelay : {n : ℕ} -> (m : ℕ) -> choice n -> choice (n + m)
postdelay m here = here
postdelay m (wait c) = (wait (postdelay m c))

zhconcat : {G : Set} (n1 n2 : ℕ) -> zhlist G n1 -> zhlist G n2 -> zhlist G (n1 + n2)
zhconcat .zero n2 zhnil w = w
zhconcat .(suc (n1 + n3)) n2 (zhcons n1 n3 x zh1) zh2 =
 subst (zhlist _) (zhcons _ _ x (zhconcat _ _ zh1 zh2)) (cong suc (assoc n1 n2 n3))

{------------------------------------
 Converting terms to maps
 ------------------------------------}

-- The output of the φ function
data φres (G : Set) : ℕ -> Set where
 φr-vert : {n : ℕ} -> zhlist G n -> G -> φres G n
 φr-nonisth : {n1 n2 : ℕ} -> zhlist G n1 -> map (Opt G) n2 -> Opt (nichoice n2) -> φres G (suc (n2 + n1))
 φr-underflow : φres G zero

φ : {G : Set} -> {n1 n2 : ℕ} -> map (Opt G) n1 -> zhlist G n2 -> φres G (n1 + n2)
φ (vert (some g)) s = φr-vert s g
φ (vert none) zhnil = φr-underflow
φ (vert none) (zhcons _ _ h s) = φr-nonisth s h none
φ {_} {_} {n2} (isth {n3} {n4} h1 h2) s = subst (φres _)
                        (φ h1 (zhcons _ _ h2 s)) (+lemma n3 n2 n4)
φ (nonisth h ν) s = φr-nonisth s h (some ν)

-- The output of the τ function
data τres (G : Set) (Q : ℕ -> Set) : ℕ -> Set where
 τr-vert : G -> τres G Q zero
 τr-isth : {n n1 n2 : ℕ} -> Q n1 -> Q n2 -> τres G Q (suc (n1 + n2))
 τr-nonisth : {n : ℕ} -> Q n -> nichoice n -> τres G Q (suc n)

τ0 : {n1 n2 : ℕ} {G : Set} -> G -> φres G n1 -> zhlist G n2 -> τres G (gzh G) (suc (n1 + n2))
τ0 {_} {n2} g1 (φr-vert s1 g2) s2 = τr-isth {_} {_} {n2} (! g1 s1) (! g2 s2)
{-
This case is the trickiest of this function. We have
g   : .G
x   : zhlist .G .n1
y   : map (Opt .G) .n3
z   : Opt (nichoice .n3)
s   : zhlist .G .n2

and in
τr-nonisth ?2 (nonloop ?3 ?4)
we need
?2 : gzh .G (suc (.n3 + .n1) + .n2)
?3 : choice (suc (.n3 + .n1) + .n2)
?4 : bool

The ?2 is built from g, x, y, s.
The number of choices in z : Opt (nichoice .n3) is 2 * n3 + 2,
which feeds into the (n3 + 1) branches of ?3, and we siphon off a bool.
The n1 and n2 branches of ?3 correspond to other ways of constructing the
list
x @ [y] @ s
-}
τ0 {_} {n2} g (φr-nonisth {n1} {n3} x y z) s =
  τr-nonisth (! g (zhconcat (suc (n3 + n1)) n2 (zhcons n3 n1 y x) s))
             (process-choices n1 n2 n3 z)
  where
  process-choices : (n1 n2 n3 : ℕ) -> Opt (nichoice n3) -> nichoice (suc (n3 + n1) + n2)
  process-choices n1 n2 n3 (some loop) = nonloop here true
  process-choices n1 n2 n3 (some (nonloop ν β)) = nonloop (wait (predelay n2 (postdelay n1 ν))) β
  process-choices n1 n2 n3 none = nonloop here false

τ0 g φr-underflow s = τr-nonisth (! g s) loop

τ : {G : Set} {n : ℕ} -> gzh G n -> τres G (gzh G) n
τ (! g zhnil) = τr-vert g
τ {G} (! g (zhcons n1 n2 h s)) = τ0 g h' s where
 h' : φres G n1
 h' = subst (φres _) (φ h zhnil) (+comm n1 zero)


make-map : (G : Set) (Q : ℕ -> Set) -> ({n : ℕ} -> Q n -> τres G Q n) -> (n : ℕ) -> Q n -> map G n
make-map G Q f n q = match n (gen-acc n) (f q) where
 match : (n : ℕ) -> Acc n -> (τres G Q n) -> map G n
 match zero α (τr-vert g) = vert g
 match _ (acc ψ) (τr-isth {_} {n1} {n2} q1 q2) =
       isth {G} {n1} {n2}
            (match n1 (ψ n1 (≤-suc (≤-lemma-1 n1 n2))) (f q1))
            (match n2 (ψ n2 (≤-suc (≤-lemma-2 n1 n2))) (f q2))
 match _ (acc ψ) (τr-nonisth {n} q ν) = nonisth (match n (ψ n ≤-refl) (f q)) ν

use-τ : (G : Set) (n : ℕ) -> gzh G n -> map G n
use-τ G n term = make-map G (gzh G) τ n term

----------------------------------


{- don't need this yet -}
-- data Kv (A B : Set) : Set where
--   _⇒_ : A -> B -> Kv A B

data Json : Set where
 jnat : ℕ -> Json
 jstr : String -> Json
 jarr : List Json -> Json
-- jobj : List (Kv String Json) -> Json

nat_of_choice : {n : ℕ} -> choice n -> ℕ
nat_of_choice here = zero
nat_of_choice (wait χ) = suc (nat_of_choice χ)

json_of_nichoice : {n : ℕ} -> nichoice n -> Json
json_of_nichoice loop = jstr "loop"
json_of_nichoice (nonloop χ β) = jarr (jnat (nat_of_choice χ) , jstr (namebool β), [])
 where
 namebool : bool -> String
 namebool true = "cw"
 namebool false = "ccw"

{- don't seem to need this generality -}
-- json_of_map : {G : Set} {n : ℕ} -> (G -> Json) ->  map G n -> Json
-- json_of_map json_of_g (vert x) = jarr (jstr "vert" , json_of_g x , [])
-- json_of_map json_of_g (isth h₁ h₂) =
--   jarr (jstr "isth" , json_of_map json_of_g h₁ ,
--                       json_of_map json_of_g h₂ , [])
-- json_of_map json_of_g (nonisth h ν) =
--   jarr (jstr "nonisth" , json_of_map json_of_g h ,
--                          json_of_nichoice ν , [])

json_of_unit_map : {n : ℕ} -> map unit n -> Json
json_of_unit_map (vert _) = jstr "vert"
json_of_unit_map (isth h₁ h₂) =
  jarr (jstr "isth" , json_of_unit_map h₁ ,
                      json_of_unit_map h₂ , [])
json_of_unit_map (nonisth h ν) =
  jarr (jstr "nonisth" , json_of_unit_map h ,
                         json_of_nichoice ν , [])

module Foo where
 example1 : Json
 example1 = json_of_unit_map (use-τ unit _ (! • eterm))
  where
  eterm = zhcons _ _ (vert none) (zhcons _ _ (vert (some •)) (zhcons _ _ (vert (some •)) zhnil))

 amap : map unit (suc (suc (suc zero)))
 amap = nonisth (isth (isth (vert •) (vert •)) (vert •)) (nonloop (wait here) true)

 example2 : Json
 example2 = json_of_unit_map amap
