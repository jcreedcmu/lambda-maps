module LambdaMaps where

open import Agda.Primitive

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

data Opt {ℓ : Level} (A : Set ℓ) : Set ℓ where
  some : A -> Opt A
  none : Opt A

data Σ {ℓ1 ℓ2 : Level} (A : Set ℓ1) (B : A → Set ℓ2) : Set (ℓ1 ⊔ ℓ2) where
 σ : (a : A) (b : B a) -> Σ A B

data Bool : Set where
 true : Bool
 false : Bool

data Choice : ℕ -> Set where
 here : {n : ℕ} -> Choice (suc n)
 wait : {n : ℕ} -> Choice n -> Choice (suc n)

data Unit : Set where
 • : Unit

postulate String : Set
{-# BUILTIN STRING String #-}

data List (A : Set) : Set where
  []   : List A
  _,_ : A → List A → List A
infixr 5 _,_

{------------------------------------
 Equality: defn and lemmas
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
 Some lemmas about + and ≤
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

base : (y : ℕ) -> (y < zero) -> Acc y
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
data Nichoice : ℕ -> Set where
 loop : {n : ℕ} -> Nichoice n
 nonloop : {n : ℕ} -> Choice n -> Bool -> Nichoice n

-- A map with G-data at vertices and with n edges can be a single
-- vertex, the isthmic attachment of two maps, or a map with a
-- nonisthmically attached edge.
data Map (G : Set) : ℕ -> Set where
 vert : G -> Map G zero
 isth : {n1 n2 : ℕ} -> Map G n1 -> Map G n2 -> Map G (suc (n1 + n2))
 nonisth : {n : ℕ} -> Map G n -> Nichoice n -> Map G (suc n)

{------------------------------------
 Type of terms
 ------------------------------------}

-- Term G m contains terms with free variables of type G and m applications
data Term {ℓ : Level} : (G : Set ℓ) -> ℕ -> Set (lsuc ℓ) where
 head : {G : Set ℓ} -> G -> Term G zero
 app : {G : Set ℓ} -> {m1 m2 : ℕ} -> Term G m1 -> Term (Opt G) m2 -> Term G (suc (m2 + m1))

{------------------------------------
 Auxiliary datastructures and defns for converting terms to maps
 ------------------------------------}

-- A useful intermediate data structure whose elements are each a
-- detached edge plus a map with G+1 vertex data
data Zhlist (G : Set) : ℕ -> Set where
 zhnil : Zhlist G zero
 zhcons : (n1 n2 : ℕ) -> Map (Opt G) n1 -> Zhlist G n2 -> Zhlist G (suc (n1 + n2))

-- One of those such lists plus a G at the head
data Gzh (G : Set) : ℕ -> Set where
 ! : {n : ℕ} -> G -> Zhlist G n -> Gzh G n

predelay' : {n : ℕ} -> (m : ℕ) -> Choice n -> Choice (m + n)
predelay' zero c = c
predelay' (suc m) c = wait (predelay' m c)

predelay : {n : ℕ} -> (m : ℕ) -> Choice n -> Choice (n + m)
predelay {n} m χ = subst Choice (predelay' m χ) (+comm m n)

postdelay : {n : ℕ} -> (m : ℕ) -> Choice n -> Choice (n + m)
postdelay m here = here
postdelay m (wait c) = (wait (postdelay m c))

zhconcat : {G : Set} (n1 n2 : ℕ) -> Zhlist G n1 -> Zhlist G n2 -> Zhlist G (n1 + n2)
zhconcat .zero n2 zhnil w = w
zhconcat .(suc (n1 + n3)) n2 (zhcons n1 n3 x zh1) zh2 =
 subst (Zhlist _) (zhcons _ _ x (zhconcat _ _ zh1 zh2)) (cong suc (assoc n1 n2 n3))

{------------------------------------
 Converting a single layer of term stuff to map stuff
 ------------------------------------}

-- The output of the φ function
data φres (G : Set) : ℕ -> Set where
 φr-vert : {n : ℕ} -> Zhlist G n -> G -> φres G n
 φr-nonisth : {n1 n2 : ℕ} -> Zhlist G n1 -> Map (Opt G) n2 -> Opt (Nichoice n2) -> φres G (suc (n2 + n1))
 φr-underflow : φres G zero

φ : {G : Set} -> {n1 n2 : ℕ} -> Map (Opt G) n1 -> Zhlist G n2 -> φres G (n1 + n2)
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
 τr-nonisth : {n : ℕ} -> Q n -> Nichoice n -> τres G Q (suc n)

τ0 : {n1 n2 : ℕ} {G : Set} -> G -> φres G n1 -> Zhlist G n2 -> τres G (Gzh G) (suc (n1 + n2))
τ0 {_} {n2} g1 (φr-vert s1 g2) s2 = τr-isth {_} {_} {n2} (! g1 s1) (! g2 s2)
{-
This case is the trickiest of this function. We have
g   : .G
x   : Zhlist .G .n1
y   : Map (Opt .G) .n3
z   : Opt (Nichoice .n3)
s   : Zhlist .G .n2

and in
τr-nonisth ?2 (nonloop ?3 ?4)
we need
?2 : Gzh .G (suc (.n3 + .n1) + .n2)
?3 : Choice (suc (.n3 + .n1) + .n2)
?4 : Bool

The ?2 is built from g, x, y, s.
The number of choices in z : Opt (Nichoice .n3) is 2 * n3 + 2,
which feeds into the (n3 + 1) branches of ?3, and we siphon off a Bool.
The n1 and n2 branches of ?3 correspond to other ways of constructing the
list
x @ [y] @ s
-}
τ0 {_} {n2} g (φr-nonisth {n1} {n3} x y z) s =
  τr-nonisth (! g (zhconcat (suc (n3 + n1)) n2 (zhcons n3 n1 y x) s))
             (process-choices n1 n2 n3 z)
  where
  process-choices : (n1 n2 n3 : ℕ) -> Opt (Nichoice n3) -> Nichoice (suc (n3 + n1) + n2)
  process-choices n1 n2 n3 (some loop) = nonloop here true
  process-choices n1 n2 n3 (some (nonloop ν β)) = nonloop (wait (predelay n2 (postdelay n1 ν))) β
  process-choices n1 n2 n3 none = nonloop here false

τ0 g φr-underflow s = τr-nonisth (! g s) loop

τ : {G : Set} {n : ℕ} -> Gzh G n -> τres G (Gzh G) n
τ (! g zhnil) = τr-vert g
τ {G} (! g (zhcons n1 n2 h s)) = τ0 g h' s where
 h' : φres G n1
 h' = subst (φres _) (φ h zhnil) (+comm n1 zero)


make-map : (G : Set) (Q : ℕ -> Set) -> ({n : ℕ} -> Q n -> τres G Q n) -> (n : ℕ) -> Q n -> Map G n
make-map G Q f n q = match n (gen-acc n) (f q) where
 match : (n : ℕ) -> Acc n -> (τres G Q n) -> Map G n
 match zero α (τr-vert g) = vert g
 match _ (acc ψ) (τr-isth {_} {n1} {n2} q1 q2) =
       isth {G} {n1} {n2}
            (match n1 (ψ n1 (≤-suc (≤-lemma-1 n1 n2))) (f q1))
            (match n2 (ψ n2 (≤-suc (≤-lemma-2 n1 n2))) (f q2))
 match _ (acc ψ) (τr-nonisth {n} q ν) = nonisth (match n (ψ n ≤-refl) (f q)) ν

use-τ : (G : Set) (n : ℕ) -> Gzh G n -> Map G n
use-τ G n term = make-map G (Gzh G) τ n term

{------------------------------------
 Converting terms to maps
 ------------------------------------}

head_of_term : {G : Set} {n : ℕ} -> Term G n -> G
head_of_term (head x) = x
head_of_term (app t1 t2) = head_of_term t1

map_of_term : (G : Set) (n : ℕ) -> Term G n -> Map G n
map_of_term G n t = use-τ G n (! (head_of_term t) (spine_of_term t))
 where
 spine_of_term : {G : Set} {n : ℕ} -> Term G n -> Zhlist G n
 spine_of_term (head x) = zhnil
 spine_of_term (app {G} {m1} {m2} t1 t2) =
  zhcons m2 m1 (map_of_term (Opt G) m2 t2) (spine_of_term t1)

map_of_unit_term : (n : ℕ) -> Term Unit n -> Map Unit n
map_of_unit_term = map_of_term Unit

{------------------------------------
 Impedance matching to javascript
 ------------------------------------}

{- don't need this yet -}
-- data Kv (A B : Set) : Set where
--   _⇒_ : A -> B -> Kv A B

data Json : Set where
 jnat : ℕ -> Json
 jstr : String -> Json
 jarr : List Json -> Json
-- jobj : List (Kv String Json) -> Json

nat_of_choice : {n : ℕ} -> Choice n -> ℕ
nat_of_choice here = zero
nat_of_choice (wait χ) = suc (nat_of_choice χ)

json_of_nichoice : {n : ℕ} -> Nichoice n -> Json
json_of_nichoice loop = jstr "loop"
json_of_nichoice (nonloop χ β) = jarr (jnat (nat_of_choice χ) , jstr (namebool β), [])
 where
 namebool : Bool -> String
 namebool true = "cw"
 namebool false = "ccw"

{- don't seem to need this generality -}
-- json_of_Map : {G : Set} {n : ℕ} -> (G -> Json) ->  Map G n -> Json
-- json_of_Map json_of_g (vert x) = jarr (jstr "vert" , json_of_g x , [])
-- json_of_Map json_of_g (isth h₁ h₂) =
--   jarr (jstr "isth" , json_of_Map json_of_g h₁ ,
--                       json_of_Map json_of_g h₂ , [])
-- json_of_Map json_of_g (nonisth h ν) =
--   jarr (jstr "nonisth" , json_of_Map json_of_g h ,
--                          json_of_Nichoice ν , [])

json_of_unit_map : {n : ℕ} -> Map Unit n -> Json
json_of_unit_map (vert _) = jstr "vert"
json_of_unit_map (isth h₁ h₂) =
  jarr (jstr "isth" , json_of_unit_map h₁ ,
                      json_of_unit_map h₂ , [])
json_of_unit_map (nonisth h ν) =
  jarr (jstr "nonisth" , json_of_unit_map h ,
                         json_of_nichoice ν , [])

-- RawTerm m contains terms with m free variables
data RawTerm : ℕ → Set where
 rhead : {n : ℕ} → Choice n → RawTerm n
 rapp : {n : ℕ} → RawTerm n → RawTerm (suc n) → RawTerm n

apps_of_raw : {n : ℕ} -> RawTerm n -> ℕ
apps_of_raw (rhead x) = zero
apps_of_raw (rapp t1 t2) = suc(apps_of_raw t2 + apps_of_raw t1)

opt_map : {A B : Set} (f : A → B) -> Opt A -> Opt B
opt_map f (some x) = some (f x)
opt_map f none = none

term_map : {A B : Set} {n : ℕ} (f : A → B) -> Term A n -> Term B n
term_map f (head x) = head (f x)
term_map f (app t1 t2) = app (term_map f t1) (term_map (opt_map f) t2)

choiceopt : (n : ℕ) -> Choice (suc n) -> Opt (Choice n)
choiceopt n here = none
choiceopt n (wait χ) = some χ

term_of_raw : {n : ℕ} (t : RawTerm n) -> Term (Choice n) (apps_of_raw t)
term_of_raw (rhead x) = head x
term_of_raw (rapp t1 t2) = app (term_of_raw t1) (term_map (choiceopt _) (term_of_raw t2))

data BareTerm : Set where
 bhead : ℕ → BareTerm
 bapp : BareTerm → BareTerm → BareTerm

mk_choice : (n : ℕ) -> ℕ -> Opt(Choice n)
mk_choice (suc n) (suc m) = opt_map wait (mk_choice n m)
mk_choice (suc zero) zero = some here
mk_choice z m = none

raw_of_bare : (n : ℕ) -> BareTerm -> Opt (RawTerm n)
raw_of_bare n (bhead db) with mk_choice n db
... | none = none
... | some x = some (rhead x)
raw_of_bare n (bapp hd tl) with raw_of_bare n hd | raw_of_bare (suc n) tl
... | none | _ = none
... | some _ | none = none
... | some hh | some tt = some (rapp hh tt)

-- _>>_ : {A : Set} {B C : A → Set} {y : A} -> Opt (B y) -> ({x : A} -> B x -> C x) -> Opt (C y)
-- none >> f = none
-- (some x) >> f = some (f x)

_>>_ : {ℓ1 ℓ2 : Level} {A : Set ℓ1} {B : Set ℓ2} -> Opt A -> (A -> B) -> Opt B
none >> f = none
(some x) >> f = some (f x)
infixl 5 _>>_

_!>_ : {ℓ1 ℓ2 : Level} {A : Set ℓ1} {B : A → Set ℓ2} -> Opt A -> ((x : A) -> B x) -> Opt (Σ A B)
none !> f = none
(some x) !> f = some (σ x (f x))
infixl 5 _!>_

map_π₂ : {ℓ1 ℓ2 : Level} {A : Set ℓ1} {B C : A → Set ℓ2} -> ({x : A} -> B x -> C x) -> Σ A B -> Σ A C
map_π₂ f (σ x y) = σ x (f y)

unitchoice : Choice (suc zero) -> Unit
unitchoice here = •
unitchoice (wait ())


term_of_bare : BareTerm -> Opt (Σ (RawTerm (suc zero)) (λ z → Term Unit (apps_of_raw z)))
term_of_bare b = term_pkg
  where
  term_pkg = raw_of_bare (suc zero) b
                   !> term_of_raw
                   >> map_π₂ (term_map unitchoice)

foo : Σ (RawTerm (suc zero)) (λ z → Term Unit (apps_of_raw z))
 -> Σ ℕ (λ z → Term Unit z)
foo (σ rt t) = σ (apps_of_raw rt) t

{------------------------------------
 Examples
 ------------------------------------}

module Foo where
 example1 : Json
 example1 = json_of_unit_map (use-τ Unit _ (! • eterm))
  where
  eterm = zhcons _ _ (vert none) (zhcons _ _ (vert (some •)) (zhcons _ _ (vert (some •)) zhnil))

 amap : Map Unit (suc (suc (suc zero)))
 amap = nonisth (isth (isth (vert •) (vert •)) (vert •)) (nonloop (wait here) true)

 example2 : Json
 example2 = json_of_unit_map amap
