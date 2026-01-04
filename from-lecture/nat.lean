
inductive nat : Type where
  | zero : nat
  | succ : nat → nat

#check nat.rec

open nat

def z := zero
def one := succ z
def two := succ one
def three := succ two

def plus : nat → nat → nat := fun
  | n, succ m => plus (succ n) m -- reduce rhs leaving
  | n, zero   => n

def mul: nat -> nat -> nat := fun n m => match n with
    | zero => zero
    | succ k => plus m (mul k m)

#reduce mul three two

def plus' (n : nat) (m : nat) : nat := match n, m with
  | n, succ m => plus (succ n) m -- reduce rhs leaving
  | n, zero   => n

def plus_two : nat → nat := fun n => succ (succ n)

def do_twice (f : nat → nat) : nat → nat := fun n => f (f n)

def do_twice' :  (nat → nat) → nat → nat := fun f => fun n => f (f n)

def do_twice'' (f : nat → nat) (n : nat ): nat := f (f n)

#reduce (do_twice plus_two) one

def do_thrice (f : nat → nat) : (nat → nat) := sorry

def predecessor: nat → nat := fun
  | zero => zero
  | succ k => k

#reduce predecessor one


/-
#  Logic
-/

inductive mTrue : Prop where
  | intro

#check mTrue
#check mTrue.intro

inductive mFalse : Prop where

#check mFalse

inductive mAnd (p q : Prop) : Prop where
  | intro (hp : p) (hq : q) : mAnd p q

theorem and_true_true : mAnd mTrue mTrue :=
  mAnd.intro mTrue.intro mTrue.intro

-- `true ∧ (true ∧ true)`
theorem and_true_and_true_true :
  mAnd mTrue (mAnd mTrue mTrue) :=
    mAnd.intro mTrue.intro and_true_true


#check mAnd mTrue (mAnd mTrue mTrue)
#check mAnd.intro mTrue.intro and_true_true

-- `p ∧ q → p`
theorem p_of_p_and_q
  (p q : Prop)
  (hand : mAnd p q) : p := match hand with
    | mAnd.intro hp _ => hp

-- `p → (q → (p ∧ q)`
theorem p_and_q_of_p_q
  (p q : Prop) : p → (q → (mAnd p q)) :=
  fun funnyName hq => mAnd.intro funnyName hq

inductive mOr (p q : Prop) : Prop
  | left (hp : p) : mOr p q
  | right (hq : q) : mOr p q

-- `true ∨ false`
theorem true_or_false : mOr mTrue mFalse :=
  mOr.left mTrue.intro

theorem and_of_or (p q : Prop) : (mAnd p q) → mOr p q :=
  fun hand => match hand with
    | mAnd.intro hp _ => mOr.left hp


def mNeg (p : Prop) := p → mFalse

-- proof that `true ∧ false` is false
theorem not_true_and_false : mNeg (mAnd mTrue mFalse) :=
  fun h_true_and_false ↦ match h_true_and_false with
    | mAnd.intro _ hfalse => hfalse


-- What's provable for this very conservative notion of negation?

-- _No contradiction principle_. `¬(p ∧ ¬p)`.

theorem no_contradiction (p : Prop) : mNeg (mAnd p (mNeg p)) :=
  fun h_p_and_neg_p => match h_p_and_neg_p with
    | mAnd.intro hp hnp => hnp hp

-- _Double negation introduction_. `p → ¬¬p`.

theorem dni (p : Prop) : p → mNeg (mNeg p) :=
  fun hp =>
    fun hnp =>
      hnp hp

theorem dni' (p : Prop) : p → mNeg (mNeg p) :=
  fun hp hnp => hnp hp


-- _Double negation elimination_: `¬¬p → p`.
-- Claim: DNE implies LEM.

-- Step 1: Prove that the double negation of the law of the excluded middle.


-- Two lemmas:
theorem orImpLeft {p q r : Prop} : ((p ∨ q) → r) → (p → r) :=
  fun h_r_of_p_or_q hp => h_r_of_p_or_q (Or.inl hp)

theorem orImpRight {p q r : Prop} : ((p ∨ q) → r) → (q → r) :=
  fun h_r_of_p_or_q hq => h_r_of_p_or_q (Or.inr hq)

-- `h : ¬(p ∨ ¬p)` means `(p ∨ ¬p) → false`
-- hence, can use the lemmas, to conclude from `h` that `p → false` and `¬p → false`

-- `¬¬(p ∨ ¬p)`  means `¬(p ∨ ¬p) → false`

-- `orImpRight h_neg_p_or_neg_p` has type `¬p → false`
-- `orImpLeft h...` has type `p → false` which `¬p`

theorem neg_neg_lem (p : Prop) : ¬¬(p ∨ ¬p) :=
  fun h_neg_p_or_neg_p =>
    (orImpRight h_neg_p_or_neg_p) (orImpLeft h_neg_p_or_neg_p)

-- So now, if DNE were true, could remove `¬¬` to get LEM.

axiom mLem {p : Prop} : mOr p (mNeg p)

axiom lem {p : Prop} : p ∨ ¬p

theorem true_or_not_true : mOr mTrue (mNeg mTrue)
  := mLem

theorem true_or_not_true_constructive : mOr mTrue (mNeg mTrue)
  :=
  mOr.left mTrue.intro

#print axioms true_or_not_true

#check mFalse.rec

-- the empty function.
theorem mExfalso {p : Prop} : mFalse → p :=
  mFalse.rec

theorem exfalso {p : Prop} : False → p :=
  False.rec

-- use lem to prove:
theorem dne (p : Prop) : ¬¬p → p := fun h_neg_neg_p =>
  match @lem p with
    | Or.inl hp => hp
    | Or.inr hnp => exfalso (h_neg_neg_p hnp)

-- ∃ a b irrational, a^b rational.
--
-- Proof sketch.
--
-- Take sqrt 2^(sqrt 2) =: x
--
-- Either:
-- -- x is rational. => done
-- --
-- Or:
-- -- x is irrational. =>
-- -- x^(sqrt 2) = (sqrt 2)^2 = 2 => done^2 = 2 => done


--- Equality


-- definitional equality `defeq`.

#reduce plus one two
#reduce zero.succ.succ.succ

-- propositional equality
-- e.g. `extensional equality` of functions.
-- it's what we mean mathematically
-- but, it's undecidable in theory and practice.

-- define an equality type for `nat`

-- `mEq a b` represents the proposition that `a` is equal to `b`
inductive mEq : nat → nat → Prop where
  | refl (a : nat) : mEq a a

#check mEq one two -- we'd like to prove the negation of that (super-hard)
#check mEq one one -- we'd like to prove this (easy)

theorem one_eq_one : mEq one one := mEq.refl one -- ∎ 🎉

#check mEq two (plus one one)

#reduce plus one one
#reduce two

theorem two_eq_one_plus_one : mEq two (plus one one) := mEq.refl two
theorem two_eq_one_plus_one': mEq two (plus one one) :=
  mEq.refl (plus one one)

theorem eq_sym {a b : nat} : mEq a b → mEq b a := mEq.rec (mEq.refl a)

-- prove that `zero ≠ one`.

-- have to define a function that turns a proof of `zero = one`
-- into a proof of the unprovable object `mFalse`
--
-- strategy.
--
-- write a function `nat → Prop` such that
-- `0 → mFalse`
-- `1 → mTrue`
-- then show that the predicate at successors is provable
-- then use the principle of substitution to turn the predicate, together with a proof of `0 = 1` into a proof of the predicate at `1`, which is false.
-- then we're done.

-- helper predicate
def nonzero_type : nat → Prop
  | zero => mFalse
  | succ _ => mTrue

-- this is provable at non-zero numbers
theorem one_nonzero : nonzero_type one := mTrue.intro

#reduce(types:=true) nonzero_type one

#check one_nonzero

theorem eq_sub (a b : nat) (p : nat → Prop) : mEq a b → (p a) → (p b) :=
  mEq.rec (fun h ↦ h)

-- if zero = one, i can turn this proof into a proof of `mFalse`
def one_not_zero : mNeg (mEq one zero) := fun h_one_eq_zero =>
  eq_sub one zero nonzero_type h_one_eq_zero one_nonzero


































#reduce plus one two
#reduce three

-- but also want equality between functions iff they are _extensionally_ equal.
-- the latter is undecidable in theory and practice.

inductive mEq: nat → nat → Prop where
 | refl (a: nat): mEq a a

#check mEq one two
#check mEq.refl one

theorem zero_succ_eq_one : mEq zero.succ one := mEq.refl one
theorem zero_succ_eq_one' : mEq zero.succ one := mEq.refl zero.succ

def eq_sym {a b: nat} : mEq a b → mEq b a := mEq.rec (mEq.refl a)
def eq_subst {a b: nat} {p: nat → Prop} : mEq a b → (p a → p b) := mEq.rec (fun hpa ↦ hpa)

def nonzero_type: nat -> Prop               -- helper type...
  | zero   => mFalse
  | succ _ => mTrue
def nonzero: nonzero_type one := mTrue.intro  -- ...inhabited at parameter one.
#check nonzero                                -- : nonzero_type one
def oneNotZero : mNeg (mEq one zero) :=
  fun h: mEq one zero =>
  eq_subst h nonzero                          -- if 1=0, then the type is inhabited at zero.
