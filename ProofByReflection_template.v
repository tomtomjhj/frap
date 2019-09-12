Require Import Frap.

Set Implicit Arguments.
Set Asymmetric Patterns.
(** * Proof by Reflection
 * translate Gallina propositions into values of inductive types representing
 * syntax, so that Gallina programs may analyze them, and translate such a term
 * back to the original form *)


(** * Proving Evenness *)

Inductive isEven : nat -> Prop :=
| Even_O : isEven O
| Even_SS : forall n, isEven n -> isEven (S (S n)).

Ltac prove_even := repeat constructor.

Theorem even_6 : isEven 6.
Proof.
  prove_even.
Qed.

Set Printing All.
Print even_6.
(* Even_SS : forall (n : nat) (_ : isEven n), isEven (S (S n)) *)
Unset Printing All.

(* - Choice of [n] for each [Even_SS] application -> n^2 size proof term.
 * - Static typing does not guarantee that our tactic always behaves
 *   appropriately.  Other invocations of similar tactics might fail with
 *   dynamic type errors.
 * The techniques of proof by reflection address both complaints. *)

(* verified decision procedure in Gallina *)
Fixpoint check_even (n : nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S n') => check_even n'
  end.

(* To prove [check_even] sound, we need two IH strengthenings:
 * - Switch to _strong induction_ [n' < n]
 * - Express both cases for how a [check_even] test might turn out. *)
Lemma check_even_ok' : forall n n',
    n' < n -> if check_even n' then isEven n' else ~isEven n'.
Proof.
  (* [not = fun A : Prop => A -> False : Prop -> Prop] *)
  induct n; simplify.
  invert H.
  cases n'; simplify.
  constructor.
  cases n'; simplify.
  propositional.
  invert H0.
  specialize (IHn n').
  cases (check_even n').
  constructor.
  apply IHn.
  linear_arithmetic.
  propositional.
  invert H0.
  apply IHn.
  linear_arithmetic.
  assumption.
Qed.  

Theorem check_even_ok : forall n, check_even n = true -> isEven n.
Proof.
  simplify.
  assert (n < S n) by linear_arithmetic.
  apply check_even_ok' in H0.
  rewrite H in H0.
  assumption.
Qed.

(* reflective tactic using verified decision process
 * - proof-search process wholly within Gallina *)
Ltac prove_even_reflective :=
  match goal with
  | [ |- isEven ?N ] => apply check_even_ok; reflexivity
  end.

Theorem even_8 : isEven 8.
Proof.
  prove_even_reflective.
Qed.

Set Printing All.
Print even_8.
Unset Printing All.

Theorem even_7 : isEven 7.
Proof.
  (* prove_even_reflective. *)
Abort.


(** * Reifying the Syntax of a Trivial Tautology Language *)

Theorem true_galore : (True /\ True) -> (True \/ (True /\ (True -> True))).
Proof.
  tauto.
Qed.

Print true_galore. (* overheads *)

(* To write a reflective procedure for this class of goals, we need to get into
 * the actual "reflection" part of "proof by reflection."  It is impossible
 * to case-analyze a [Prop] in any way in Gallina.  We must _reify_ [Prop] into
 * some type that we _can_ analyze. This inductive type is a good candidate:
 *)

Inductive taut : Set :=
| TautTrue : taut
| TautAnd : taut -> taut -> taut
| TautOr : taut -> taut -> taut
| TautImp : taut -> taut -> taut.

(* reflect the syntax back to Prop (interpretation function ) *)
Fixpoint tautDenote (t : taut) : Prop :=
  match t with
    | TautTrue => True
    | TautAnd t1 t2 => tautDenote t1 /\ tautDenote t2
    | TautOr t1 t2 => tautDenote t1 \/ tautDenote t2
    | TautImp t1 t2 => tautDenote t1 -> tautDenote t2
  end.

Theorem tautTrue : forall t, tautDenote t.
Proof.
  induct t; simplify; propositional.
Qed.

(* reify to syntax *)
Ltac tautReify P :=
  match P with
    | True => TautTrue
    | ?P1 /\ ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautAnd t1 t2)
    | ?P1 \/ ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautOr t1 t2)
    | ?P1 -> ?P2 =>
      let t1 := tautReify P1 in
      let t2 := tautReify P2 in
        constr:(TautImp t1 t2)
  end.

(* [change] the goal to reified goal, then tautTrue *)
Ltac obvious :=
  match goal with
    | [ |- ?P ] =>
      let t := tautReify P in
      change (tautDenote t); apply tautTrue
  end.
Theorem true_galore' : (True /\ True) -> (True \/ (True /\ (True -> True))).
Proof.
  obvious.
Qed.

Set Printing All.
Print true_galore'.
Unset Printing All.








(** * A Monoid Expression Simplifier *)

Section monoid.
  Variable A : Set.
  Variable e : A.
  Variable f : A -> A -> A.

  Infix "+" := f.

  Hypothesis assoc : forall a b c, (a + b) + c = a + (b + c).
  Hypothesis identl : forall a, e + a = a.
  Hypothesis identr : forall a, a + e = a.

  Inductive mexp : Set :=
  | Ident : mexp
  | Var : A -> mexp
  | Op : mexp -> mexp -> mexp.

  (* Next, we write an interpretation function. *)

  Fixpoint mdenote (me : mexp) : A :=
    match me with
      | Ident => e
      | Var v => v
      | Op me1 me2 => mdenote me1 + mdenote me2
    end.































  Ltac reify me :=
    match me with
      | e => Ident
      | ?me1 + ?me2 =>
        let r1 := reify me1 in
        let r2 := reify me2 in
          constr:(Op r1 r2)
      | _ => constr:(Var me)
    end.

  (*Ltac monoid :=
    match goal with
      | [ |- ?me1 = ?me2 ] =>
        let r1 := reify me1 in
        let r2 := reify me2 in
          change (mdenote r1 = mdenote r2);
            apply monoid_reflect; simplify
    end.

  Theorem t1 : forall a b c d, a + b + c + d = a + (b + c) + d.
    simplify; monoid.
    reflexivity.
  Qed.*)
End monoid.



(** * Set Simplification for Model Checking *)

(* Let's take a closer look at model-checking proofs like from last class. *)

(* Here's a simple transition system, where state is just a [nat], and where
 * each step subtracts 1 or 2. *)

Inductive subtract_step : nat -> nat -> Prop :=
| Subtract1 : forall n, subtract_step (S n) n
| Subtract2 : forall n, subtract_step (S (S n)) n.

Definition subtract_sys (n : nat) : trsys nat := {|
  Initial := {n};
  Step := subtract_step
|}.

Lemma subtract_ok :
  invariantFor (subtract_sys 5)
               (fun n => n <= 5).
Proof.
  eapply invariant_weaken.

  apply multiStepClosure_ok.
  simplify.
  (* Here we'll see that the Frap libary uses slightly different, optimized
   * versions of the model-checking relations.  For instance, [multiStepClosure]
   * takes an extra set argument, the _worklist_ recording newly discovered
   * states.  There is no point in following edges out of states that were
   * already known at previous steps. *)

  (* Now, some more manual iterations: *)
  eapply MscStep.
  closure.
  (* Ew.  What a big, ugly set expression.  Let's shrink it down to something
   * more readable, with duplicates removed, etc. *)
  simplify.
  (* How does the Frap library do that?  Proof by reflection is a big part of
   * it!  Let's develop a baby version of that automation.  The full-scale
   * version is in file Sets.v. *)
Abort.
















(* Back to our example, which we can now finish without calling [simplify] to
 * reduces trees of union operations. *)
(*Lemma subtract_ok :
  invariantFor (subtract_sys 5)
               (fun n => n <= 5).
Proof.
  eapply invariant_weaken.

  apply multiStepClosure_ok.
  simplify.

  (* Now, some more manual iterations: *)
  eapply MscStep.
  closure.
  simplify_set.
  (* Success!  One subexpression shrunk.  Now for the other. *)
  simplify_set.
  (* Our automation doesn't handle set difference, so we finish up calling the
   * library tactic. *)
  simplify.

  eapply MscStep.
  closure.
  simplify_set.
  simplify_set.
  simplify.

  eapply MscStep.
  closure.
  simplify_set.
  simplify_set.
  simplify.

  eapply MscStep.
  closure.
  simplify_set.
  simplify_set.
  simplify.

  model_check_done.

  simplify.
  linear_arithmetic.
Qed.*)


(** * A Smarter Tautology Solver *)

Definition propvar := nat.

Inductive formula : Set :=
| Atomic : propvar -> formula
| Truth : formula
| Falsehood : formula
| And : formula -> formula -> formula
| Or : formula -> formula -> formula
| Imp : formula -> formula -> formula.

Definition asgn := nat -> Prop.

Fixpoint formulaDenote (atomics : asgn) (f : formula) : Prop :=
  match f with
    | Atomic v => atomics v
    | Truth => True
    | Falsehood => False
    | And f1 f2 => formulaDenote atomics f1 /\ formulaDenote atomics f2
    | Or f1 f2 => formulaDenote atomics f1 \/ formulaDenote atomics f2
    | Imp f1 f2 => formulaDenote atomics f1 -> formulaDenote atomics f2
  end.

Section my_tauto.
  Variable atomics : asgn.

  Require Import ListSet.

  Definition add (s : set propvar) (v : propvar) := set_add eq_nat_dec v s.

  Fixpoint allTrue (s : set propvar) : Prop :=
    match s with
      | nil => True
      | v :: s' => atomics v /\ allTrue s'
    end.

  Theorem allTrue_add : forall v s,
    allTrue s
    -> atomics v
    -> allTrue (add s v).
  Proof.
    induct s; simplify; propositional;
      match goal with
        | [ |- context[if ?E then _ else _] ] => destruct E
      end; simplify; propositional.
  Qed.

  Theorem allTrue_In : forall v s,
    allTrue s
    -> set_In v s
    -> atomics v.
  Proof.
    induct s; simplify; equality.
  Qed.

  Fixpoint forward (f : formula) (known : set propvar) (hyp : formula)
           (cont : set propvar -> bool) : bool :=
    match hyp with
    | Atomic v => cont (add known v)
    | Truth => cont known
    | Falsehood => true
    | And h1 h2 => forward (Imp h2 f) known h1 (fun known' =>
                     forward f known' h2 cont)
    | Or h1 h2 => forward f known h1 cont && forward f known h2 cont
    | Imp _ _ => cont known
    end.

  Fixpoint backward (known : set propvar) (f : formula) : bool :=
    match f with
    | Atomic v => if In_dec eq_nat_dec v known then true else false
    | Truth => true
    | Falsehood => false
    | And f1 f2 => backward known f1 && backward known f2
    | Or f1 f2 => backward known f1 || backward known f2
    | Imp f1 f2 => forward f2 known f1 (fun known' => backward known' f2)
    end.
End my_tauto.

Lemma forward_ok : forall atomics hyp f known cont,
    forward f known hyp cont = true
    -> (forall known', allTrue atomics known'
                       -> cont known' = true
                       -> formulaDenote atomics f)
    -> allTrue atomics known
    -> formulaDenote atomics hyp
    -> formulaDenote atomics f.
Proof.
  induct hyp; simplify; propositional.

  apply H0 with (known' := add known p).
  apply allTrue_add.
  assumption.
  assumption.
  assumption.

  eapply H0.
  eassumption.
  assumption.

  eapply IHhyp1 in H.
  simplify; propositional.
  simplify.
  eapply IHhyp2.
  eassumption.
  assumption.
  assumption.
  assumption.
  assumption.
  assumption.

  apply andb_true_iff in H; propositional.
  eapply IHhyp1.
  eassumption.
  assumption.
  assumption.
  assumption.

  apply andb_true_iff in H; propositional.
  eapply IHhyp2.
  eassumption.
  assumption.
  assumption.
  assumption.

  eapply H0.
  eassumption.
  assumption.
Qed.

Lemma backward_ok' : forall atomics f known,
    backward known f = true
    -> allTrue atomics known
    -> formulaDenote atomics f.
Proof.
  induct f; simplify; propositional.

  cases (in_dec Nat.eq_dec p known); propositional.
  eapply allTrue_In.
  eassumption.
  unfold set_In.
  assumption.
  equality.

  equality.

  apply andb_true_iff in H; propositional.
  eapply IHf1.
  eassumption.
  assumption.

  apply andb_true_iff in H; propositional.
  eapply IHf2.
  eassumption.
  assumption.

  apply orb_true_iff in H; propositional.
  left.
  eapply IHf1.
  eassumption.
  assumption.
  right.
  eapply IHf2.
  eassumption.
  assumption.

  eapply forward_ok.
  eassumption.
  simplify.
  eapply IHf2.
  eassumption.
  assumption.
  assumption.
  assumption.
Qed.

Theorem backward_ok : forall f,
    backward [] f = true
    -> forall atomics, formulaDenote atomics f.
Proof.
  simplify.
  apply backward_ok' with (known := []).
  assumption.
  simplify.
  propositional.
Qed.

(* Find the position of an element in a list. *)
Ltac position x ls :=
  match ls with
  | [] => constr:(@None nat)
  | x :: _ => constr:(Some 0)
  | _ :: ?ls' =>
    let p := position x ls' in
    match p with
    | None => p
    | Some ?n => constr:(Some (S n))
    end
  end.

(* Compute a duplicate-free list of all variables in [P], combining it with
 * [acc]. *)
Ltac vars_in P acc :=
  match P with
  | True => acc
  | False => acc
  | ?Q1 /\ ?Q2 =>
    let acc' := vars_in Q1 acc in
    vars_in Q2 acc'
  | ?Q1 \/ ?Q2 =>
    let acc' := vars_in Q1 acc in
    vars_in Q2 acc'
  | ?Q1 -> ?Q2 =>
    let acc' := vars_in Q1 acc in
    vars_in Q2 acc'
  | _ =>
    let pos := position P acc in
    match pos with
    | Some _ => acc
    | None => constr:(P :: acc)
    end
  end.

(* Reification of formula [P], with a pregenertaed list [vars] of variables it
 * may mention *)
Ltac reify_tauto' P vars :=
  match P with
  | True => Truth
  | False => Falsehood
  | ?Q1 /\ ?Q2 =>
    let q1 := reify_tauto' Q1 vars in
    let q2 := reify_tauto' Q2 vars in
    constr:(And q1 q2)
  | ?Q1 \/ ?Q2 =>
    let q1 := reify_tauto' Q1 vars in
    let q2 := reify_tauto' Q2 vars in
    constr:(Or q1 q2)
  | ?Q1 -> ?Q2 =>
    let q1 := reify_tauto' Q1 vars in
    let q2 := reify_tauto' Q2 vars in
    constr:(Imp q1 q2)
  | _ =>
    let pos := position P vars in
    match pos with
    | Some ?pos' => constr:(Atomic pos')
    end
  end.

(* Our final tactic implementation is now fairly straightforward.  First, we
 * [intro] all quantifiers that do not bind [Prop]s.  Then we reify.  Finally,
 * we call the verified procedure through a lemma. *)

Ltac my_tauto :=
  repeat match goal with
           | [ |- forall x : ?P, _ ] =>
             match type of P with
               | Prop => fail 1
               | _ => intro
             end
         end;
  match goal with
    | [ |- ?P ] =>
      let vars := vars_in P (@nil Prop) in
      let p := reify_tauto' P vars in
      change (formulaDenote (nth_default False vars) p)
  end;
  apply backward_ok; reflexivity.

(* A few examples demonstrate how the tactic works: *)

Theorem mt1 : True.
Proof.
  my_tauto.
Qed.

Print mt1.

Theorem mt2 : forall x y : nat, x = y -> x = y.
Proof.
  my_tauto.
Qed.

Print mt2.

Theorem mt3 : forall x y z,
  (x < y /\ y > z) \/ (y > z /\ x < S y)
  -> y > z /\ (x < y \/ x < S y).
Proof.
  my_tauto.
Qed.

Print mt3.

Theorem mt4 : True /\ True /\ True /\ True /\ True /\ True /\ False -> False.
Proof.
  my_tauto.
Qed.

Print mt4.

Theorem mt4' : True /\ True /\ True /\ True /\ True /\ True /\ False -> False.
Proof.
  tauto.
Qed.

Print mt4'.
