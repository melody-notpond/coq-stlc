Import Nat Peano.
Require Import List.
Require Import Classes.SetoidClass Arith.PeanoNat.
Require Import
  ExtLib.Data.Monads.OptionMonad
  ExtLib.Structures.Monad.
Import MonadNotation.
Open Scope nat_scope.
Open Scope monad_scope.

Inductive type : Set :=
  | ty_unit
  | ty_arrow (a r : type).

Inductive term : Set :=
  | tm_unit
  | tm_var (index: nat)
  | tm_abs (body: term)
  | tm_app (func: term) (arg: term)
  | tm_ann (tm: term) (ty: type).

Definition context := list type.

Inductive typing : context -> term -> type -> Prop :=
  | dt_unit : forall G, typing G tm_unit ty_unit
  | dt_var
      : forall G i ty,
        nth_error G i = Some ty ->
        typing G (tm_var i) ty
  | dt_arrow_intro
      : forall G b ta tr,
        typing (ta :: G) b tr ->
        typing G (tm_abs b) (ty_arrow ta tr)
  | dt_arrow_elim
      : forall G f a ta tr,
        typing G f (ty_arrow ta tr) ->
        typing G a ta ->
        typing G (tm_app f a) tr
  | dt_ann
      : forall G tm ty,
        typing G tm ty ->
        typing G (tm_ann tm ty) ty.

Fixpoint teqb (t t' : type) : bool :=
  match t, t' with
  | ty_unit, ty_unit => true
  | ty_arrow a r, ty_arrow a' r' =>
      teqb a a' && teqb r r'
  | _, _ => false
  end.

Lemma teqb_eq : forall t t', teqb t t' = true <-> t = t'.
Proof.
  intro t.
  induction t; destruct t'; simpl; try easy.
  split.
  - intros H.
    f_equal.
    + apply IHt1.
      now apply andb_prop in H as [H _].
    + apply IHt2.
      now apply andb_prop in H as [_ H].
  - intros H.
    injection H as H1 H2.
    apply andb_true_intro.
    apply IHt1 in H1.
    apply IHt2 in H2.
    now split.
Qed.

Lemma teqb_refl : forall t, teqb t t = true.
Proof.
  intros.
  now apply teqb_eq.
Qed.

Definition fail {A} : option A := None.

Fixpoint check (G: context) (tm: term) (ty: type)
  {struct tm} : option type :=
  match tm, ty with
  | tm_unit, ty_unit => ret ty_unit
  | tm_unit, _ => fail
  | tm_abs b, ty_arrow a r =>
      check (a :: G) b r;;
      ret (ty_arrow a r)
  | tm_abs _, _ => fail
  | tm_var i, ty =>
      ty' <- nth_error G i;;
      if teqb ty ty' then
        ret ty
      else fail
  | tm_app f a, ty =>
      tf <- infer G f;;
      ty' <- match tf with
      | ty_arrow ta tr =>
          check G a ta;;
          ret tr
      | _ => fail
      end;;
      if teqb ty ty' then
        ret ty
      else fail
  | tm_ann tm ty', ty =>
      ty'' <- check G tm ty';;
      if teqb ty'' ty then
        ret ty
      else fail
  end
with infer (G: context) (tm: term)
  {struct tm} : option type :=
  match tm with
  | tm_var i => nth_error G i
  | tm_app f a =>
      ty <- infer G f;;
      match ty with
      | ty_arrow ta tr =>
          check G a ta;;
          ret tr
      | _ => fail
      end
  | tm_ann tm ty => check G tm ty
  | _ => fail
  end.

Lemma bidir_check_some
  : forall G tm ty ty',
    check G tm ty = Some ty' -> ty = ty'.
Proof.
  intros G tm.
  generalize dependent G.
  destruct tm; intros.
  - destruct ty; try easy.
    simpl in H.
    now injection H as H.
  - simpl in H; destruct (nth_error G index); try easy.
    destruct (teqb ty t); try easy.
    now injection H as H.
  - destruct ty; try easy.
    simpl in H.
    destruct (check (ty1 :: G) tm ty2); try easy.
    now injection H as H.
  - simpl in H.
    destruct (infer G tm1); try easy.
    destruct t; try easy.
    destruct (check G tm2 t1); try easy.
    destruct (teqb ty t2); try easy.
    now injection H as H.
  - simpl in H.
    destruct (check G tm ty); try easy.
    destruct (teqb t ty0); try easy.
    now injection H as H.
Qed.

Theorem bidir_sound_check
  : forall G tm ty,
    check G tm ty = Some ty -> typing G tm ty
with bidir_sound_infer
  : forall G tm ty,
    infer G tm = Some ty -> typing G tm ty.
Proof.
  - intros G tm.
    generalize dependent G.
    induction tm; intros.
    + destruct ty; try easy.
      constructor.
    + simpl in H.
      destruct (nth_error G index) eqn:E; try easy.
      destruct (teqb ty t) eqn:E'; try easy.
      constructor.
      apply teqb_eq in E'.
      now rewrite E'.
    + destruct ty; try easy.
      constructor.
      simpl in H.
      destruct (check (ty1 :: G) tm ty2) eqn:E; try easy.
      apply IHtm.
      now rewrite <- (bidir_check_some _ _ _ _ E) in E.
    + simpl in H.
      destruct (infer G tm1) eqn:E; try easy.
      destruct t; try easy.
      destruct (check G tm2 t1) eqn:E'; try easy.
      destruct (teqb ty t2) eqn:E''; try easy.
      apply teqb_eq in E''.
      rewrite E'' in *.
      econstructor.
      apply bidir_sound_infer.
      apply E.
      apply IHtm2.
      now rewrite <- (bidir_check_some _ _ _ _ E') in E'.
    + simpl in H.
      destruct (check G tm ty) eqn:E; try easy.
      rewrite <- (bidir_check_some _ _ _ _ E) in H.
      rewrite <- (bidir_check_some _ _ _ _ E) in E.
      destruct (teqb ty ty0) eqn:E'; try easy.
      apply teqb_eq in E'.
      rewrite <- E'.
      constructor.
      now apply IHtm.
  - intros G tm.
    generalize dependent G.
    induction tm; intros; try easy.
    + simpl in H.
      now constructor.
    + simpl in H.
      destruct (infer G tm1) eqn:E; try easy.
      destruct t; try easy.
      destruct (check G tm2 t1) eqn:E'; try easy.
      econstructor.
      apply IHtm1 in E.
      injection H as H.
      rewrite H in E.
      apply E.
      rewrite <- (bidir_check_some _ _ _ _ E') in E'.
      now apply bidir_sound_check in E'.
    + simpl in H.
      rewrite <- (bidir_check_some _ _ _ _ H).
      rewrite <- (bidir_check_some _ _ _ _ H) in H.
      constructor.
      now apply bidir_sound_check.
Qed.


