(* Distributed under the terms of the MIT license.   *)

From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst
     PCUICEquality PCUICTyping
     PCUICReduction PCUICPosition.
Local Open Scope string_scope.
Set Asymmetric Patterns.
Require Import CRelationClasses.
Require Import Equations.Type.Relation Equations.Type.Relation_Properties.

Set Default Goal Selector "!".

Reserved Notation " Σ ;;; Γ |- t == u " (at level 50, Γ, t, u at next level).


Instance cumul_refl' {cf:checker_flags} Σ Γ : Reflexive (cumul Σ Γ).
Proof.
  intro; constructor. reflexivity.
Qed.

Instance conv_refl' {cf:checker_flags} Σ Γ : Reflexive (conv Σ Γ).
Proof.
  intro; constructor. reflexivity.
Qed.

Lemma red_cumul `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- t <= u.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X.
  - apply cumul_refl'.
  - econstructor 2. all: eauto.
Qed.

Lemma red_cumul_inv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u} :
  red Σ Γ t u ->
  Σ ;;; Γ |- u <= t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X.
  - apply cumul_refl'.
  - econstructor 3. all: eauto.
Qed.

Lemma red_cumul_cumul `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  red Σ Γ t u -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- t <= v.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. 1: auto.
  econstructor 2; eauto.
Qed.

Lemma red_cumul_cumul_inv `{cf : checker_flags} {Σ : global_env_ext} {Γ t u v} :
  red Σ Γ t v -> Σ ;;; Γ |- u <= v -> Σ ;;; Γ |- u <= t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X. 1: auto.
  econstructor 3.
  - eapply IHX. eauto.
  - eauto.
Qed.


Lemma conv_cumul2 {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u -> (Σ ;;; Γ |- t <= u) * (Σ ;;; Γ |- u <= t).
Proof.
  induction 1.
  - split; constructor; now apply eq_term_leq_term.
  - destruct IHX as [H1 H2]. split.
    * econstructor 2; eassumption.
    * econstructor 3; eassumption.
  - destruct IHX as [H1 H2]. split.
    * econstructor 3; eassumption.
    * econstructor 2; eassumption.
  - destruct IHX as [H1 H2]. split.
    * econstructor 4; eassumption.
    * econstructor 5; eassumption.
  - destruct IHX as [H1 H2]. split.
    * econstructor 5; eassumption.
    * econstructor 4; eassumption.
Qed.

Lemma conv_cumul {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- t = u -> Σ ;;; Γ |- t <= u.
Proof.
  intro H; now apply conv_cumul2 in H.
Qed.

Lemma conv_cumul_inv {cf:checker_flags} Σ Γ t u :
  Σ ;;; Γ |- u = t -> Σ ;;; Γ |- t <= u.
Proof.
  intro H; now apply conv_cumul2 in H.
Qed.

Lemma cumul2_conv {cf:checker_flags} Σ Γ t u :
  (Σ ;;; Γ |- t <= u) * (Σ ;;; Γ |- u <= t) -> Σ ;;; Γ |- t = u.
Proof.
  intros [H1 H2]; revert H2. induction H1.
Abort.

Lemma red_conv {cf:checker_flags} (Σ : global_env_ext) Γ t u
  : red Σ Γ t u -> Σ ;;; Γ |- t = u.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n in X.
  induction X.
  - reflexivity.
  - econstructor 2. all: eauto.
Defined.
Hint Resolve red_conv : core.

Lemma eq_term_App `{checker_flags} φ f f' :
  eq_term φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma eq_term_mkApps `{checker_flags} φ f l f' l' :
  eq_term φ f f' ->
  All2 (eq_term φ) l l' ->
  eq_term φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in l', f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - cbn. eapply IHl.
    + constructor; assumption.
    + assumption.
Qed.

Lemma leq_term_App `{checker_flags} φ f f' :
  leq_term φ f f' ->
  isApp f = isApp f'.
Proof.
  inversion 1; reflexivity.
Qed.

Lemma leq_term_mkApps `{checker_flags} φ f l f' l' :
  leq_term φ f f' ->
  All2 (eq_term φ) l l' ->
  leq_term φ (mkApps f l) (mkApps f' l').
Proof.
  induction l in l', f, f' |- *; intro e; inversion_clear 1.
  - assumption.
  - cbn. apply IHl.
    + constructor; try assumption.
    + assumption.
Qed.

Hint Resolve leq_term_refl cumul_refl' : core.

Lemma red_conv_conv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- u = v -> Σ ;;; Γ |- t = v.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X; auto.
  econstructor 2; eauto.
Qed.

Lemma red_conv_conv_inv `{cf : checker_flags} Σ Γ t u v :
  red (fst Σ) Γ t u -> Σ ;;; Γ |- v = u -> Σ ;;; Γ |- v = t.
Proof.
  intros. apply red_alt in X. apply clos_rt_rt1n_iff in X.
  induction X; auto.
  now econstructor 3; [eapply IHX|]; eauto.
Qed.

Instance conv_sym `{cf : checker_flags} (Σ : global_env_ext) Γ :
  Symmetric (conv Σ Γ).
Proof.
  intros t u X. induction X.
  - eapply eq_term_sym in e; now constructor.
  - eapply red_conv_conv_inv.
    + eapply red1_red in r. eauto.
    + eauto.
  - eapply red_conv_conv.
    + eapply red1_red in r. eauto.
    + eauto.
  - eapply conv_eta_r. all: eassumption.
  - eapply conv_eta_l. all: eassumption.
Qed.


Inductive conv_pb :=
| Conv
| Cumul.

Definition conv_cum `{cf : checker_flags} leq Σ Γ u v :=
  match leq with
  | Conv => ∥ Σ ;;; Γ |- u = v ∥
  | Cumul => ∥ Σ ;;; Γ |- u <= v ∥
  end.

Lemma conv_conv_cum_l `{cf : checker_flags} :
  forall (Σ : global_env_ext) leq Γ u v, wf Σ ->
      Σ ;;; Γ |- u = v ->
      conv_cum leq Σ Γ u v.
Proof.
  intros Σ [] Γ u v h.
  - cbn. constructor. assumption.
  - cbn. constructor. now apply conv_cumul.
Qed.

Lemma conv_conv_cum_r `{cf : checker_flags} :
  forall (Σ : global_env_ext) leq Γ u v, wf Σ ->
      Σ ;;; Γ |- u = v ->
      conv_cum leq Σ Γ v u.
Proof.
  intros Σ [] Γ u v wfΣ h.
  - cbn. constructor. apply conv_sym; auto.
  - cbn. constructor. apply conv_cumul.
    now apply conv_sym.
Qed.

Lemma cumul_App_l `{cf : checker_flags} :
  forall {Σ Γ f g x},
    Σ ;;; Γ |- f <= g ->
    Σ ;;; Γ |- tApp f x <= tApp g x.
Proof.
  intros Σ Γ f g x h.
  induction h.
  - eapply cumul_refl. constructor.
    + assumption.
    + apply eq_term_refl.
  - eapply cumul_red_l ; try eassumption.
    econstructor. assumption.
  - eapply cumul_red_r ; try eassumption.
    econstructor. assumption.
  - eapply cumul_eta_l. 2: eassumption.
    destruct e as [na [A [f [π [? ?]]]]]. subst.
    exists na, A, f, (stack_cat π (App x ε)).
    rewrite 2!zipc_stack_cat. cbn. intuition reflexivity.
  - eapply cumul_eta_r. 1: eassumption.
    destruct e as [na [A [f [π [? ?]]]]]. subst.
    exists na, A, f, (stack_cat π (App x ε)).
    rewrite 2!zipc_stack_cat. cbn. intuition reflexivity.
Qed.


From Equations Require Import Equations Relation.
Derive Signature for red1.

Require Import PCUICAstUtils.
Require Import List. Import ListNotations. Open Scope list_scope.

Lemma app_mkApps u v t l :
  isApp t = false -> tApp u v = mkApps t l ->
  ∑ l', (l = l' ++ [v])%list × u = mkApps t l'.
Proof.
  intros h e. induction l in u, v, t, e, h |- * using list_rect_rev.
  - cbn in e. subst. cbn in h. discriminate.
  - rewrite <- mkApps_nested in e. cbn in e.
    exists l. inversion e. subst. auto.
Qed.

Lemma red1_tApp_inv Σ Γ t u v (H : red1 Σ Γ (tApp t u) v)
  : (∑ w, red1 Σ Γ t w × v = tApp w u) + (∑ w, red1 Σ Γ u w × v = tApp t w).
Proof.
  depelim H.
  - admit.
  - left. apply app_mkApps in H; cbnr.
    destruct H as [l [H1 H2]]; subst.
    exists (mkApps fn l). split.
    + eapply red_fix; tea. admit. (* wrong *)
    + now rewrite <- mkApps_nested.
  - left; eexists; split; tea. reflexivity.
  - right; eexists; split; tea. reflexivity.
Abort.

Require Import ssrbool.

Lemma not_isLambda_mkApps u l :
  ~~ isLambda u -> ~~ isLambda (mkApps u l).
Proof.
  induction l in u |- *; cbn; auto.
Qed.

Lemma tLambda_mkApps_not_isLambda na A t u l :
  ~~ isLambda u -> tLambda na A t <> mkApps u l.
Proof.
  intros H e. eapply not_isLambda_mkApps in H.
  rewrite <- e in H; auto.
Qed.

Lemma tLambda_mkApps_tFix na A t mfix idx args :
  tLambda na A t <> mkApps (tFix mfix idx) args.
Proof.
  now apply tLambda_mkApps_not_isLambda.
Qed.

Lemma tRel_mkApps_tFix n mfix idx args :
  tRel n <> mkApps (tFix mfix idx) args.
Proof.
  induction args using rev_ind; cbn.
  - inversion 1.
  - rewrite <- mkApps_nested; cbn. inversion 1.
Qed.

(* Lemma tVar_mkApps_tFix n mfix idx args : *)
(*   tVar n <> mkApps (tFix mfix idx) args. *)
(* Proof. *)
(*   induction args using rev_ind; cbn. *)
(*   - inversion 1. *)
(*   - rewrite <- mkApps_nested; cbn. inversion 1. *)
(* Qed. *)

  (* TODO MOVE *)
  Fixpoint isFixApp t : bool :=
    match t with
    | tApp f u => isFixApp f
    | tFix mfix idx => true
    | _ => false
    end.

  (* TODO MOVE *)
  Lemma isFixApp_mkApps :
    forall t l,
      isFixApp (mkApps t l) = isFixApp t.
  Proof.
    intros t l. induction l in t |- *.
    - cbn. reflexivity.
    - cbn. rewrite IHl. reflexivity.
  Qed.

Require Import PCUICLiftSubst Arith Lia.
Lemma lift_tLambda_inv n k M na A t (H : lift n k M = tLambda na A t)
  : ∑ A' t', M = tLambda na A' t' /\ A = lift n k A' /\ t = lift n (S k) t'.
Proof.
  induction M; cbn in *; try now inversion H.
  - destruct (PeanoNat.Nat.leb k n0); inversion H.
  - invs H. repeat eexists.
Defined.

Lemma lift_Apps_Construct_inv n k M ind c u args
      (H : lift n k M = mkApps (tConstruct ind c u) args)
  : ∑ args', M = mkApps (tConstruct ind c u) args'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using MCList.rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    { destruct (k <=? n0); discriminate. }
    exists []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    { destruct (k <=? n0); discriminate. }
    invs H. apply IHargs in H1. destruct H1 as [args' [H1 H2]]; subst.
    exists (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split.
Qed.

Lemma lift_Apps_Fix_inv n k M mfix idx args
      (H : lift n k M = mkApps (tFix mfix idx) args)
  : ∑ mfix' args', M = mkApps (tFix mfix' idx) args'
             /\ mfix = map (map_def (lift n k) (lift n (#|mfix'| + k))) mfix'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using MCList.rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    { destruct (k <=? n0); discriminate. }
    invs H. eexists _, []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    { destruct (k <=? n0); discriminate. }
    invs H. apply IHargs in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    exists mfix', (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split; tas.
Qed.

Lemma lift_Apps_CoFix_inv n k M mfix idx args
      (H : lift n k M = mkApps (tCoFix mfix idx) args)
  : ∑ mfix' args', M = mkApps (tCoFix mfix' idx) args'
             /\ mfix = map (map_def (lift n k) (lift n (#|mfix'| + k))) mfix'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using MCList.rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    { destruct (k <=? n0); discriminate. }
    invs H. eexists _, []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    { destruct (k <=? n0); discriminate. }
    invs H. apply IHargs in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    exists mfix', (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split; tas.
Qed.
    

Require Import Program PCUICWeakening.

(* todo replace in liftsubst *)
Lemma isLambda_lift n k (bod : term) :
  isLambda (lift n k bod) = isLambda bod.
Proof. destruct bod; cbnr. now destruct (k <=? n0). Qed.

(* todo replace in weakening *)
Lemma lift_unfold_fix n k mfix idx :
  unfold_fix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx
  = option_map (on_snd (lift n k)) (unfold_fix mfix idx).
Proof.
  unfold unfold_fix.
  rewrite nth_error_map. destruct (nth_error mfix idx); cbnr.
  rewrite isLambda_lift.
  destruct isLambda; cbnr. f_equal. unfold on_snd; cbn. f_equal.
  rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite fix_subst_length. f_equal.
  unfold fix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.

Lemma lift_unfold_cofix n k mfix idx :
  unfold_cofix (map (map_def (lift n k) (lift n (#|mfix| + k))) mfix) idx
  = option_map (on_snd (lift n k)) (unfold_cofix mfix idx).
Proof.
  unfold unfold_cofix.
  rewrite nth_error_map. destruct (nth_error mfix idx); cbnr.
  f_equal. unfold on_snd; cbn. f_equal.
  rewrite (distr_lift_subst_rec _ _ n 0 k).
  rewrite cofix_subst_length. f_equal.
  unfold cofix_subst. rewrite !map_length.
  generalize #|mfix| at 2 3. induction n0; auto. simpl.
  f_equal. apply IHn0.
Qed.

(* todo replace in weakening *)
Lemma lift_is_constructor args narg n k :
  is_constructor narg args = is_constructor narg (map (lift n k) args).
Proof.
  unfold is_constructor. rewrite nth_error_map.
  destruct nth_error; cbnr.
  unfold isConstruct_app. destruct decompose_app eqn:Heq.
  eapply decompose_app_lift in Heq as ->; cbn.
  destruct t0; cbnr. destruct (k <=? n0); reflexivity.
Qed.


Lemma red1_strengthening Σ Γ Γ' Γ'' M N' :
  red1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) N'
  -> ∑ N, red1 Σ (Γ ,,, Γ') M N × N' = lift #|Γ''| #|Γ'| N.
Proof.
  intro H; dependent induction H.
  - destruct M; cbn in x; try discriminate.
    { destruct (#|Γ'| <=? n); discriminate. }
    destruct M1; cbn in x; try discriminate.
    { destruct (#|Γ'| <=? n); discriminate. }
    eexists. split.
    { constructor. }
    invs x. now rewrite distr_lift_subst10.
  - destruct M; cbn in x; try discriminate.
    { destruct (#|Γ'| <=? n); discriminate. }
    eexists. split.
    { constructor. }
    invs x. now rewrite distr_lift_subst10.
  - destruct M; cbn in x; try discriminate.
    rewrite <- app_context_assoc in e.
    destruct (Nat.leb_spec0 #|Γ'| n); invs x.
    + rewrite nth_error_app_context_ge in e;
        rewrite app_context_length, lift_context_length in *; [|lia].
      eexists. split.
      { constructor. rewrite nth_error_app_context_ge; tas.
        etransitivity; tea. do 2 f_equal. lia. }
      rewrite simpl_lift; try lia.
      f_equal. lia.
    + rewrite nth_error_app_context_lt in e;
        rewrite ?app_context_length, ?lift_context_length in *; [|lia].
      rewrite nth_error_app_context_lt in e;
        rewrite ?app_context_length, ?lift_context_length in *; [|lia].
      rewrite nth_error_lift_context_eq in e.
      case_eq (nth_error Γ' n); [|intro H; rewrite H in e; discriminate].
      intros [na [bd|] ty] H; rewrite H in e; [|discriminate].
      eexists. split.
      { constructor. rewrite nth_error_app_context_lt; [|lia].
        rewrite H. reflexivity. }
      cbn in *. clear H. invs e.
      rewrite permute_lift; [|lia]. f_equal; lia.
  - destruct M; cbn in x; try discriminate.
    { destruct (#|Γ'| <=? n); discriminate. }
    invs x. symmetry in H2; apply lift_Apps_Construct_inv in H2.
    destruct H2 as [args' [H1 H2]]; subst.
    eexists. split.
    { constructor. }
    symmetry; apply lift_iota_red.
  - symmetry in x; apply lift_Apps_Fix_inv in x.
    destruct x as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_fix in e.
    destruct (unfold_fix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    cbn in e. invs e.
    rewrite <- lift_is_constructor in e0.
    eexists; split.
    { econstructor; tea. }
    symmetry; apply lift_mkApps.
  - destruct M; cbn in x; try discriminate.
    { destruct (#|Γ'| <=? n); discriminate. }
    invs x. symmetry in H2; apply lift_Apps_CoFix_inv in H2.
    destruct H2 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_cofix in e.
    destruct (unfold_cofix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    cbn in e. invs e.
    eexists; split.
    { econstructor; tea. }
    cbn. f_equal. symmetry; apply lift_mkApps.
  - destruct M; cbn in x; try discriminate.
    { destruct (#|Γ'| <=? n); discriminate. }
    invs x. symmetry in H1; apply lift_Apps_CoFix_inv in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_cofix in e.
    destruct (unfold_cofix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    cbn in e. invs e.
    eexists; split.
    { econstructor; tea. }
    cbn. f_equal. symmetry; apply lift_mkApps.
  - 
  - 

    


  induction M in Γ' |- *; cbn.
  - case_eq (#|Γ'| <=? n); intro le.
    + toProp.
      intro H; depelim H; [|now apply tRel_mkApps_tFix in H].
      rewrite nth_error_app_context_ge in e;
        rewrite lift_context_length in *; [|lia].
      rewrite nth_error_app_context_ge in e; [|lia].
      eexists. split.
      -- constructor. rewrite nth_error_app_context_ge; tas.
         etransitivity; tea. do 2 f_equal. lia.
      -- rewrite simpl_lift; try lia.
         f_equal; lia.
    + apply Nat.leb_gt in le. (* todo toProp *)
      intro H; depelim H; [|now apply tRel_mkApps_tFix in H].
      rewrite nth_error_app_context_lt in e;
        [|rewrite lift_context_length; lia].
      rewrite nth_error_lift_context_eq in e.
      case_eq (nth_error Γ' n); [|intro H; rewrite H in e; discriminate].
      intros [na [bd|] ty] H; rewrite H in e; [|discriminate].
      eexists. split.
      -- constructor. rewrite nth_error_app_context_lt; tas.
         rewrite H. cbn. reflexivity.
      -- cbn in *. clear H. invs e.
         rewrite permute_lift; [|lia].
         f_equal; lia.
  - inversion 1.
    apply (f_equal isFixApp) in H.
    rewrite isFixApp_mkApps in H; discriminate. 
  -

   -
         rewrite <- nth_error_map in e.

         etransitivity; tea. do 2 f_equal. lia.
      -- rewrite simpl_lift; try lia.
         f_equal; lia.


Admitted.




Lemma eta_postponment Σ Γ u v w (H1 : eta_expands u v) (H2 : red1 Σ Γ v w)
  : ∑ v', clos_refl (red1 Σ Γ) u v' × clos_refl eta_expands v' w.
Proof.
  destruct H1 as [na [A [t [π [e1 e2]]]]]; subst.
  induction π; cbn in *.
  - depelim H2.
    + now apply tLambda_mkApps_tFix in H.
    + exists t; split.
      * constructor 2.
      * constructor. exists na, M', t, Empty; split; cbnr.
    + depelim H2.
      * red in H. cbn in H. inversion H; subst; clear H.
        apply lift_tLambda_inv in H1.
        destruct H1 as [A' [t' [H1 [H2 H3]]]]; subst.
        assert (X : (lift 1 1 t') {0 := tRel 0} = t') by admit.
        rewrite X. eexists. admit.
      * admit.
      * apply (red1_strengthening Σ Γ [] [vass na A]) in H2.
        cbn in H2; destruct H2 as [H [H1 H2]]; subst.
        exists H; split.
        -- now constructor.
        -- constructor. eexists _, _, _, Empty.
           repeat split.
      * invs H2.
        -- inversion H0.
        -- symmetry in H; now apply tRel_mkApps_tFix in H.
