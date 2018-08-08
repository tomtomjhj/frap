(* http://adam.chlipala.net/cpdt/html/Match.html *)
Require Import Frap.

Set Implicit Arguments.


(** * Ltac Programming Basics *)
Ltac find_if :=
  match goal with
  | [ |- if ?X then _ else _ ] => cases X
  end.

Theorem hmm : forall (a b c : bool),
  if a
    then if b
      then True
      else True
    else if c
      then True
      else True.
Proof.
  simplify; repeat find_if; trivial.
Qed.

(* context patterns *)
Ltac find_if_inside :=
  match goal with
  | [ |- context[if ?X then _ else _] ] => cases X
  end.

Theorem hmm2 : forall (a b : bool),
  (if a then 42 else 42) = (if b then 42 else 42).
Proof.
   simplify; repeat find_if_inside; trivial.
Qed.

(** * Automating the two-thread locked-increment example from TransitionSystems *)

(* Let's experience the process of gradually automating the proof we finished
 * the last lecture with.  Here's the system-definition code, stripped of
 * comments. *)

Inductive increment_program :=
| Lock
| Read
| Write (local : nat)
| Unlock
| Done.

Record inc_state := {
  Locked : bool;
  Global : nat
}.

Record threaded_state shared private := {
  Shared : shared;
  Private : private
}.

Definition increment_state := threaded_state inc_state increment_program.

Inductive increment_init : increment_state -> Prop :=
| IncInit :
  increment_init {| Shared := {| Locked := false; Global := O |};
                    Private := Lock |}.

Inductive increment_step : increment_state -> increment_state -> Prop :=
| IncLock : forall g,
  increment_step {| Shared := {| Locked := false; Global := g |};
                    Private := Lock |}
                 {| Shared := {| Locked := true; Global := g |};
                    Private := Read |}
| IncRead : forall l g,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Read |}
                 {| Shared := {| Locked := l; Global := g |};
                    Private := Write g |}
| IncWrite : forall l g v,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Write v |}
                 {| Shared := {| Locked := l; Global := S v |};
                    Private := Unlock |}
| IncUnlock : forall l g,
  increment_step {| Shared := {| Locked := l; Global := g |};
                    Private := Unlock |}
                 {| Shared := {| Locked := false; Global := g |};
                    Private := Done |}.

Definition increment_sys := {|
  Initial := increment_init;
  Step := increment_step
|}.

Inductive parallel1 shared private1 private2
  (init1 : threaded_state shared private1 -> Prop)
  (init2 : threaded_state shared private2 -> Prop)
  : threaded_state shared (private1 * private2) -> Prop :=
| Pinit : forall sh pr1 pr2,
  init1 {| Shared := sh; Private := pr1 |}
  -> init2 {| Shared := sh; Private := pr2 |}
  -> parallel1 init1 init2 {| Shared := sh; Private := (pr1, pr2) |}.

Inductive parallel2 shared private1 private2
          (step1 : threaded_state shared private1 -> threaded_state shared private1 -> Prop)
          (step2 : threaded_state shared private2 -> threaded_state shared private2 -> Prop)
          : threaded_state shared (private1 * private2)
            -> threaded_state shared (private1 * private2) -> Prop :=
| Pstep1 : forall sh pr1 pr2 sh' pr1',
  step1 {| Shared := sh; Private := pr1 |} {| Shared := sh'; Private := pr1' |}
  -> parallel2 step1 step2 {| Shared := sh; Private := (pr1, pr2) |}
               {| Shared := sh'; Private := (pr1', pr2) |}
| Pstep2 : forall sh pr1 pr2 sh' pr2',
  step2 {| Shared := sh; Private := pr2 |} {| Shared := sh'; Private := pr2' |}
  -> parallel2 step1 step2 {| Shared := sh; Private := (pr1, pr2) |}
               {| Shared := sh'; Private := (pr1, pr2') |}.

Definition parallel shared private1 private2
           (sys1 : trsys (threaded_state shared private1))
           (sys2 : trsys (threaded_state shared private2)) := {|
  Initial := parallel1 sys1.(Initial) sys2.(Initial);
  Step := parallel2 sys1.(Step) sys2.(Step)
|}.

Definition increment2_sys := parallel increment_sys increment_sys.

Definition contribution_from (pr : increment_program) : nat :=
  match pr with
  | Unlock => 1
  | Done => 1
  | _ => 0
  end.

Definition has_lock (pr : increment_program) : bool :=
  match pr with
  | Read => true
  | Write _ => true
  | Unlock => true
  | _ => false
  end.

Definition shared_from_private (pr1 pr2 : increment_program) :=
  {| Locked := has_lock pr1 || has_lock pr2;
     Global := contribution_from pr1 + contribution_from pr2 |}.

Definition instruction_ok (self other : increment_program) :=
  match self with
  | Lock => True
  | Read => has_lock other = false
  | Write n => has_lock other = false /\ n = contribution_from other
  | Unlock => has_lock other = false
  | Done => True
  end.

Inductive increment2_invariant :
  threaded_state inc_state (increment_program * increment_program) -> Prop :=
| Inc2Inv : forall pr1 pr2,
  instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> increment2_invariant {| Shared := shared_from_private pr1 pr2; Private := (pr1, pr2) |}.

Lemma Inc2Inv' : forall sh pr1 pr2,
  sh = shared_from_private pr1 pr2
  -> instruction_ok pr1 pr2
  -> instruction_ok pr2 pr1
  -> increment2_invariant {| Shared := sh; Private := (pr1, pr2) |}.
(*                                     ^^*)
Proof.
  simplify.
  rewrite H.
  apply Inc2Inv; assumption.
Qed.

(* OK, HERE is where prove the main theorem. *)

Theorem increment2_invariant_ok : invariantFor increment2_sys increment2_invariant.
Proof.
  Print increment2_invariant.
  Check invariant_induction.
  apply invariant_induction; simplify; (*.*)
  
(*  invert H. invert H0. invert H1. apply Inc2Inv'. unfold shared_from_private; simplify.*)
(*  repeat (match goal with
  | [H : parallel1 _ _ _ |- _] => invert H
  | [H : parallel2 _ _ _ _ |- _] => invert H
  | [H : increment_init _ |- _] => invert H
  | [|- increment2_invariant _] => apply Inc2Inv'
  | [|- context[shared_from_private _ _]] => unfold shared_from_private
  end; simplify; try equality).*)
  repeat (match goal with
  | [H : parallel1 _ _ _ |- _] => invert H
  | [H : parallel2 _ _ _ _ |- _] => invert H
  | [H : increment_init _ |- _] => invert H
  | [H : increment_step _ _ |- _] => invert H
  | [H : increment2_invariant _ |- _] => invert H
  | [H : instruction_ok ?pr _ |- _] => cases pr
  | [|- increment2_invariant _] => apply Inc2Inv'
  | [|- context[shared_from_private _ _]] => unfold shared_from_private
  end; simplify; try equality).
Qed.

(** * Implementing some of [propositional] ourselves *)

Print True.
Print False.
Locate "/\".
Print and.
Locate "\/".
Print or.
(* Implication ([->]) is built into Coq, so nothing to look up there. *)

Ltac my_tauto :=
  repeat match goal with
  | [ H : ?P |- ?P ] => exact H
  | [ H : _ /\ _ |- _ ] => cases H
  | [ H : _ \/ _ |- _ ] => cases H
  | [ H : False |- _ ] => cases H
  | [ H1 : ?P -> ?Q, H2 : ?P |- _ ] => specialize (H1 H2)
  | [ |- True ] => constructor
  | [ |- _ -> _ ] => intro
  | [ |- _ /\ _ ] => constructor
  end.


Section propositional.
  Variables P Q R : Prop.

  Theorem propositional : (P \/ Q \/ False) /\ (P -> Q) -> True /\ Q.
  Proof.
    my_tauto.
Qed.
End propositional.

(* Backrtracking example #1 *)

Theorem m1 : True.
Proof.
  match goal with
    | [ |- _ ] => intro  (* backtrack *)
    | [ |- True ] => constructor
  end.
Qed.

(* Backtracking example #2 *)
(* failure can move to a different pattern *)
Theorem m2 : forall P Q R : Prop, P -> Q -> R -> Q.
Proof.
  intros; match goal with
            | [ H : _ |- _ ] => idtac H
          end.
  (* this [match] first tries binding [H] to [H1], which cannot be used to prove [Q] *)
  intros; match goal with
          | [ H : _ |- _ ] => idtac H; exact H (* H1 fails -> match another *)
          end.
Qed.

(* Let's try some more ambitious reasoning, with quantifiers.  We'll be
 * instantiating quantified facts heuristically.  If we're not careful, we get
 * in a loop repeating the same instantiation forever. *)

(* Spec: ensure that [P] doesn't follow trivially from hypotheses. *)
Ltac notHyp P :=
  match goal with
  | [ H : P |- _ ] => fail 1 (* fail whole [match]: second case will not be tried *)
  | _ =>
    match P with
    | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2]
    | _ => idtac (* placeholder *)
    end
  end.
(* [fail N]: failing at the backtracking point [N] levels out from where we are.
 * [first]: first tactic that doesn't fail 
 * The fail 2 at the end says to fail both the [first] and the [match] wrapped around it.
 *)

(* Spec: takes as input a proof term and adds its conclusion as a new hypothesis,
 * only if that conclusion is not already present, failing otherwise. *)
Ltac extend pf :=
  let t := type of pf in
  notHyp t; (* generalize pf; intro. *)
  pose proof pf.
  
(* [generalize] takes as input a term t (for instance, a proof of some proposition)
 * and then changes the conclusion from G to forall (x:T), G′, where T is the type of t 
 * (for instance, the proposition proved by the proof t) *)
(* [pose proof term] behaves like [assert T  by exact term] where term : T.
 * [assert (H : U)] adds a new hypothesis of name H asserting U to the current 
 * goal and opens a new subgoal U
 *)
(* Spec: add all simple consequences of known facts, including
 * [forall]-quantified. *)
Ltac completer :=
  repeat match goal with
         | [ H : _ /\ _ |- _ ] => destruct H
         | [ H : ?P -> ?Q, H' : ?P |- _ ] => specialize (H H')
         (*            ^^ why? see completer' *)
         | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
         | [ |- _ /\ _ ] => constructor
         | [ |- forall x, _ ] => intro
         (* [ |- _ -> _ ] => intro
          * -> is special non-dependent case of forall *)
         end.

Section firstorder.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo : forall (y x : A), P x -> S x.
  Proof.
    completer.
    assumption.
  Qed.
End firstorder.

Ltac completer' :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
           | [ H : ?P /\ ?Q |- _ ] => destruct H;
             repeat match goal with
                      | [ H' : P /\ Q |- _ ] => clear H'
                    end
           | [ H : ?P -> _, H' : ?P |- _ ] => specialize (H H')
           (*            ^^ *)
           | [ |- forall x, _ ] => intro

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
         end.


Section firstorder'.
  Variable A : Set.
  Variables P Q R S : A -> Prop.

  Hypothesis H1 : forall x, P x -> Q x /\ R x.
  Hypothesis H2 : forall x, R x -> S x.

  Theorem fo' : forall (y x : A), P x -> S x.
    completer'.
(*y : A
  H1 : P y -> Q y /\ R y
  H2 : R y -> S y
  x : A
  H : P x
  ============================
   S x
  quantified thms instantiated y, but last match in completer' is correct.
*)
  Abort.
End firstorder'.

Theorem t1 : forall x : nat, x = x.
  match goal with
  | [ |- forall x, _ ] => trivial
  (*| [ |- forall x, ?P ] => trivial
    this fails 
    | [|-forall x, ?P x] => trivial
    this works
    *)
  end.
Qed.
(* unification variables may not contain locally bound variables. In this case,
 * ?P would need to be bound to x = x, which contains the local quantified 
 * variable x. 
 * In an Ltac pattern, Coq matches a wildcard implication against a
 * universal quantification.
 *)


(** * Functional Programming in Ltac *)
Print O.

(* Spec: return length of list. *)
Ltac length ls :=
  match ls with
    | nil => O  (* 0 vs O *)
    | _ :: ?ls' =>
      let ls'' := length ls' in
        constr:(S ls'')
  end.
   (* - escape into the Gallina parsing nonterminal
    * - Gallina terms built by tactics must be bound explicitly via let or a 
    *   similar technique, rather than inserting Ltac calls directly in other
        Gallina terms. *)

Goal False.
  let n := length (1 :: 2 :: 3 :: nil) in
    pose n.
Abort.

(* Spec: map Ltac function over list. *)
Ltac map T f :=
  let rec map' ls :=
    match ls with
    | nil => constr:(@nil T)
    | ?x :: ?ls' =>
      let x' := f x in
      let ls'' := map' ls' in
      constr:(x' :: ls'')
    end in
  map'.
(* Ltac func can't have implicit args. Ltac programs are dynamically typed. *)

Goal False.
  let ls := map (nat * nat)%type ltac:(fun x => constr:((x, x))) (1::2::3::nil) in
  pose ls.
Abort.

(* Now let's revisit [length] and see how we might implement "printf debugging"
 * for it. *)
Module Import WithPrinting.
  Ltac length ls :=
    idtac ls; (* debug trace *)
    match ls with
    | nil => O
    | _ :: ?ls' =>
      let ls'' := length ls' in
      constr:(S ls'')
    end.
End WithPrinting.

Goal False.
(*let n := length (1::2::3::nil) in
  pose n. 
  variable n should be bound to a term. (dynamic type error) *)
Abort.
(* Dual status of Ltac as both a purely functional and an imperative PL
 * The basic programming language is purely functional, but tactic scripts are
 * one "datatype" that can be returned by such programs, and Coq will run such
 * a script using an imperative semantics that mutates proof states.
 * An Ltac tactic program returns a function that, when run later, will perform
 * the desired proof modification. These functions are distinct from other
 * types of data, like numbers or Gallina terms. The prior, correctly working
 * version of length computed solely with Gallina terms, but the new one is
 * implicitly returning a tactic function, as indicated by the use of idtac
 * and semicolon. However, the new version's recursive call to length is
 * structured to expect a Gallina term, not a tactic function, as output.
 * As a result, we have a basic dynamic type error.
 *
 * The problem is that Ltac as a language contains several datatypes.  One of               
 * them is "tactic sequence," which can't be mixed with other datatypes like                
 * "term in the logic."  Tactic sequences don't return results.  We can use                 
 * continuation-passing style as a mitigation. *)  

Module Import WithPrintingFixed.
  Ltac length ls k :=
    idtac ls;
    match ls with
    | nil => k O
    | _ :: ?ls' => length ls' ltac:(fun n => k (S n))
    end.
End WithPrintingFixed.

Goal False.
  length (1 :: 2 :: 3 :: nil) ltac:(fun n => pose n).
Abort.


(** * Recursive Proof Search *)

(* Let's work on a tactic to try all possible instantiations of quantified
 * hypotheses, attempting to find out where the goal becomes obvious. This 
 * is probably a bad idea for almost all goals, but it makes for a nice 
 * example of recursive proof search procedures in Ltac.*)
 
(* try all possible proofs with chain length at most n *)
Ltac inster n :=
  intuition; (* fancier version of [propositional] *)
  match n with
  | S ?n' =>
    match goal with
    | [ H : forall x : ?T, _, y : ?T |- _ ] => idtac n H y; pose proof (H y); inster n' 
    end
  (*| _  => idtac    fail!*)
  end.
(* when one rec call fails, [match goal] backtracking causes to try the next instantiation
 * (implicit state)
 * -> exhaustive search *)


Section test_inster.
  Variable A : Set.
  Variables P Q : A -> Prop.
  Variable f : A -> A.
  Variable g : A -> A -> A.

  Hypothesis H1 : forall x y, P (g x y) -> Q (f x).

  Theorem test_inster : forall x, P (g x x) -> Q (f x).
  Proof.
    inster 2.
(*  type error when directly do [H1 x] *)
  Qed.

  Hypothesis H3 : forall u v, P u /\ P v /\ u <> v -> P (g u v).
  Hypothesis H4 : forall u, Q (f u) -> P u /\ P (f u).

  Theorem test_inster2 : forall x y, x <> y -> P x -> Q (f y) -> Q (f x).
  Proof.
    inster 3.
 (* 3 H4 y -> 2 H1 x -> 1 H6 y *)
    Restart.
    intuition.
    (* Check H4 y. this won't type check ??? *)
    assert (H4' := H4).
    Check H4' y. (* this works. ?????????????????????????????? *)
    pose proof H4' y.
    intuition.
    assert (H1' := H1).
    pose proof H1' x.
    assert (H6' := H6).
    pose proof H6' y.
    intuition.
  Qed.
End test_inster.

(** ** A fancier example of proof search (probably skipped on first
       reading/run-through) *)

Definition imp (P1 P2 : Prop) := P1 -> P2.
Infix "-->" := imp (no associativity, at level 95).
Ltac imp := unfold imp; firstorder.

(** These lemmas about [imp] will be useful in the tactic that we will write. *)

Theorem and_True_prem : forall P Q,
  (P /\ True --> Q)
  -> (P --> Q).
Proof.
  imp.
Qed.

Theorem and_True_conc : forall P Q,
  (P --> Q /\ True)
  -> (P --> Q).
Proof.
  imp.
Qed.

Theorem pick_prem1 : forall P Q R S,
  (P /\ (Q /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
Proof.
  imp.
Qed.

Theorem pick_prem2 : forall P Q R S,
  (Q /\ (P /\ R) --> S)
  -> ((P /\ Q) /\ R --> S).
Proof.
  imp.
Qed.

Theorem comm_prem : forall P Q R,
  (P /\ Q --> R)
  -> (Q /\ P --> R).
Proof.
  imp.
Qed.

Theorem pick_conc1 : forall P Q R S,
  (S --> P /\ (Q /\ R))
  -> (S --> (P /\ Q) /\ R).
Proof.
  imp.
Qed.

Theorem pick_conc2 : forall P Q R S,
  (S --> Q /\ (P /\ R))
  -> (S --> (P /\ Q) /\ R).
Proof.
  imp.
Qed.

Theorem comm_conc : forall P Q R,
  (R --> P /\ Q)
  -> (R --> Q /\ P).
Proof.
  imp.
Qed.

Ltac search_prem tac :=
  let rec search P :=
    tac
    || (apply and_True_prem; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (apply pick_prem1; search P1)
           || (apply pick_prem2; search P2)
       end
  in match goal with
       | [ |- ?P /\ _ --> _ ] => search P
       | [ |- _ /\ ?P --> _ ] => apply comm_prem; search P
       | [ |- _ --> _ ] => progress (tac || (apply and_True_prem; tac))
     end.
(*
* for every subformula P of the implication premise, we want P to "have a turn,"
  where the premise is rearranged into the form P /\ Q for some Q
* Pass P explicitly as a kind of decreasing induction measure, to avoid looping 
  forever when tac always fails. Tactic tac should expect to see a goal in this 
  form and focus its attention on the first conjunct of the premise
* [progress] fails when its argument tactic succeeds without changing the current subgoal. 
*)
Ltac search_conc tac :=
  let rec search P :=
    tac
    || (apply and_True_conc; tac)
    || match P with
         | ?P1 /\ ?P2 =>
           (apply pick_conc1; search P1)
           || (apply pick_conc2; search P2)
       end
  in match goal with
       | [ |- _ --> ?P /\ _ ] => search P
       | [ |- _ --> _ /\ ?P ] => apply comm_conc; search P
       | [ |- _ --> _ ] => progress (tac || (apply and_True_conc; tac))
     end.

Theorem False_prem : forall P Q,
  False /\ P --> Q.
Proof.
  imp.
Qed.

Theorem True_conc : forall P Q : Prop,
  (P --> Q)
  -> (P --> True /\ Q).
Proof.
  imp.
Qed.

Theorem Match : forall P Q R : Prop,
  (Q --> R)
  -> (P /\ Q --> P /\ R).
Proof.
  imp.
Qed.

(* Inductive ex (A : Type) (P : A -> Prop) : Prop :=
     ex_intro : forall x : A, P x -> exists y, P y *)
Locate "exists".
Theorem ex_prem : forall (T : Type) (P : T -> Prop) (Q R : Prop),
  (forall x, P x /\ Q --> R)
  -> (ex P /\ Q --> R).
Proof.
  imp.
Qed.

Theorem ex_conc : forall (T : Type) (P : T -> Prop) (Q R : Prop) x,
  (Q --> P x /\ R)
  -> (Q --> ex P /\ R).
Proof.
  imp.
Qed.

Theorem imp_True : forall P,
  P --> True.
Proof.
  imp.
Qed.
(*
 * [simple apply term] behaves like apply but it reasons modulo conversion only on
 * subterms that contain no variables to instantiate
 *)
Ltac matcher :=
  intros;
    repeat search_prem ltac:(simple apply False_prem || (simple apply ex_prem; intro));
      repeat search_conc ltac:(simple apply True_conc || simple eapply ex_conc
        || search_prem ltac:(simple apply Match));
      try simple apply imp_True.

(* Our tactic succeeds at proving a simple example. *)

Theorem t2 : forall P Q : Prop,
  Q /\ (P /\ False) /\ P --> P /\ Q.
Proof.
  matcher.
Qed.

(* In the generated proof, we find a trace of the workings of the search tactics. *)
Print t2.
(* fun P Q : Prop => comm_prem (pick_prem1 (pick_prem2 (False_prem (P /\ Q))))
     : forall P Q : Prop, Q /\ (P /\ False) /\ P --> P /\ Q *)

(* We can also see that [matcher] is well-suited for cases where some human
 * intervention is needed after the automation finishes. *)

Theorem t3 : forall P Q R : Prop,
  P /\ Q --> Q /\ R /\ P.
Proof.
  matcher.
Abort.

(* The [matcher] tactic even succeeds at guessing quantifier instantiations.  It
 * is the unification that occurs in uses of the [Match] lemma that does the
 * real work here. *)

Theorem t4 : forall (P : nat -> Prop) Q, (exists x, P x /\ Q) --> Q /\ (exists x, P x).
Proof.
  matcher.
Qed.

Print t4.
(* 
fun (P : nat -> Prop) (Q : Prop) =>
and_True_prem
  (ex_prem
     (fun x : nat =>
      pick_prem2
        (Match (and_True_conc (ex_conc (fun x0 : nat => P x0) x (Match (imp_True (P:=True))))))))
     : forall (P : nat -> Prop) (Q : Prop),
       (exists x : nat, P x /\ Q) --> Q /\ (exists x : nat, P x)
*)


(** * Creating Unification Variables *)

(* A final useful ingredient in tactic crafting is the ability to allocate new
 * unification variables explicitly.  Before we are ready to write a tactic, we
 * can try out its ingredients one at a time. *)
(* placeholders, then syntatic unification *)
Theorem t5 : (forall x : nat, S x > x) -> 2 > 1.
Proof.
  intros.

  evar (y : nat). (* y := ?y : nat   * ?y: unification variable *)

  let y' := eval unfold y in y in
    clear y; specialize (H y').
  (* H : S ?y > ?y *)
  apply H.
Qed.

(* Spec: create new evar of type [T] and pass to [k]. *)
Ltac newEvar T k :=
  let x := fresh "x" in
  evar (x : T);
  let x' := eval unfold x in x in
  clear x; k x'.

(* Spec: instantiate initial [forall]s of [H] with new evars. *)
Ltac insterU H :=
  repeat match type of H with
         | forall x : ?T, _ => newEvar T ltac:(fun y => specialize (H y))
         end.

Theorem t5' : (forall x : nat, S x > x) -> 2 > 1.
Proof.
  intro H.
  insterU H.
  apply H.
Qed.

(* This particular example is somewhat silly, since [apply] by itself would have
 * solved the goal originally.  ^Separate forward reasoning is more useful on
 * hypotheses that end in existential quantifications.^  Before we go through an
 * example, it is useful to define a variant of [insterU] that does not clear
 * the base hypothesis we pass to it. *)

Ltac insterKeep H :=
  let H' := fresh "H'" in
  pose proof H as H'; insterU H'.

Section t6.
  Variables A B : Type.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t6 : forall v1 v2, exists u1, exists u2, P (f v1 v2) (g u1 u2).
  Proof.
    intros.
    do 2 insterKeep H1.
    repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
           end.
    (* eauto *)
    eexists. eexists. (* placeholders for quantified vars *)
    apply H2.
    (* H : P ?x0@{H':=ex_intro (fun u : B => P ?x u) x0 p} x ?? *)
    exact H. exact p.
  Qed.
End t6.

(* Here's an example where something bad happens. *)

Section t7.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t7 : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
  Proof.
    intros; do 2 insterKeep H1;
      repeat match goal with
               | [ H : ex _ |- _ ] => destruct H
             end; eauto.

    (* Oh, two trivial goals remain. *)
    Unshelve.
    assumption.
    assumption.
  Qed.
End t7.

(* Problem: The [forall] rule was also matching implications -> treat them differently
 * in forall x : ?T, ...., If T has type Prop, then x's instantiation should be 
 * thought of as a proof. Thus, instead of picking a new unification variable for it,
 * apply a user-supplied tactic [tac]
 *)

Module Import FixedInster.
  Ltac insterU tac H :=
    repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
             | Prop =>
               (let H' := fresh "H'" in
                assert (H':T) by solve [ tac ]; (* solve T by tac *)
                specialize (H H'); clear H')
               || fail 1 (* if tac fails to prove T, abort instantiation *)
             | _ => newEvar T ltac:(fun y => specialize (H y))
             end
           end.
  (* solve [expr*|] : eval exprs to tactic vals, apply each to the goal independently.
   *                  fail if no tactic that completetely solves the goal. *)
  Ltac insterKeep tac H :=
    let H' := fresh "H'" in
      generalize H; intro H'; insterU tac H'.
End FixedInster.


Section t7'.
  Variables A B : Type.
  Variable Q : A -> Prop.
  Variable P : A -> B -> Prop.
  Variable f : A -> A -> A.
  Variable g : B -> B -> B.

  Hypothesis H1 : forall v, Q v -> exists u, P v u.
  Hypothesis H2 : forall v1 u1 v2 u2,
    P v1 u1
    -> P v2 u2
    -> P (f v1 v2) (g u1 u2).

  Theorem t7' : forall v1 v2, Q v1 -> Q v2 -> exists u1, exists u2, P (f v1 v2) (g u1 u2).
  Proof.
    intros.            (* 1st-class tactic may not begin with match *)
    do 2 insterKeep 
      ltac:(idtac; match goal with
                   | [ H : Q ?v |- _ ] =>
                      match goal with
                      | [ _ : context[P v _] |- _ ] => fail 1
                      | _ => apply H
                      end
                   end) H1. 
    (* ^ find and apply a Q hypothesis over a variable about which
     * we do not yet know any P facts *)
    repeat match goal with
           | [ H : ex _ |- _ ] => destruct H
           end; eauto.
  Qed.
End t7'.

(* explictly instantiating existential variables *)
Theorem t8 : exists p : nat * nat, fst p = 3.
Proof.
  econstructor.
  instantiate (1 := (3, 2)).
  (* " 1:= " : identifies an existential variable appearing in the current goal,
               with the last existential appearing assigned number 1 *)
  equality.
Qed.

(* A way that plays better with automation: *)

Theorem t9 : exists p : nat * nat, fst p = 3.
Proof.
  econstructor. match goal with
                | [ |- fst ?x = 3 ] => unify x (3, 2)
                end; equality.
Qed.
