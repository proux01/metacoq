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



Require Import List Arith Lia ssrbool.
From MetaCoq Require Import PCUICAstUtils PCUICLiftSubst PCUICWeakening.
Import ListNotations. Open Scope list_scope.

From Equations Require Import Equations Relation.
Require Import Equations.Prop.DepElim.

Derive Signature for red1.

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

Lemma lift_tLambda_inv n k M na A t (H : lift n k M = tLambda na A t)
  : ∑ A' t', M = tLambda na A' t' /\ A = lift n k A' /\ t = lift n (S k) t'.
Proof.
  induction M; cbn in *; try now inversion H.
  - invs H. repeat eexists.
Defined.

Lemma lift_Apps_Construct_inv n k M ind c u args
      (H : lift n k M = mkApps (tConstruct ind c u) args)
  : ∑ args', M = mkApps (tConstruct ind c u) args'
             /\ args = map (lift n k) args'.
Proof.
  revert M H. induction args using MCList.rev_ind; cbn; intros M H.
  - destruct M; cbn in H; try discriminate.
    exists []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
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
    invs H. eexists _, []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
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
    invs H. eexists _, []. repeat split; tas.
  - rewrite <- mkApps_nested in H; cbn in H.
    destruct M; cbn in H; try discriminate.
    invs H. apply IHargs in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    exists mfix', (args' ++ [M2]). rewrite <- mkApps_nested; cbn.
    rewrite map_app. repeat split; tas.
Qed.
    


(* todo replace in liftsubst *)
Lemma isLambda_lift n k (bod : term) :
  isLambda (lift n k bod) = isLambda bod.
Proof. destruct bod; cbnr. Qed.

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
  destruct t0; cbnr.
Qed.

Lemma nth_error_lift_context Γ Γ' Γ'' n :
  nth_error (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ')
            (if #|Γ'| <=? n then #|Γ''| + n else n)
  = nth_error (Γ ,,, lift_context #|Γ''| 0 Γ') n.
Proof.
  destruct (leb_spec_Set #|Γ'| n).
  - rewrite !nth_error_app_context_ge; rewrite ?lift_context_length; try lia.
    f_equal; lia.
  - rewrite !nth_error_app_context_lt; rewrite ?lift_context_length; try lia.
    reflexivity.
Qed.



Lemma red1_strengthening {cf:checker_flags} Σ Γ Γ' Γ'' M N' :
  wf Σ ->
  red1 Σ (Γ ,,, Γ'' ,,, lift_context #|Γ''| 0 Γ') (lift #|Γ''| #|Γ'| M) N'
  -> ∑ N, red1 Σ (Γ ,,, Γ') M N × N' = lift #|Γ''| #|Γ'| N.
Proof.
  intros HΣ H; dependent induction H using red1_ind_all.
  - destruct M; cbn in H; try discriminate.
    destruct M1; invs H.
    eexists. split.
    { constructor. }
    now rewrite distr_lift_subst10.
  - destruct M; invs H.
    eexists. split.
    { constructor. }
    now rewrite distr_lift_subst10.
  - destruct M; invs H0.
    rewrite <- app_context_assoc in H.
    destruct (leb_spec_Set #|Γ'| n).
    + rewrite nth_error_app_context_ge in H;
        rewrite app_context_length, lift_context_length in *; [|lia].
      eexists. split.
      { constructor. rewrite nth_error_app_context_ge; tas.
        etransitivity; tea. do 2 f_equal. lia. }
      rewrite simpl_lift; try lia.
      f_equal. lia.
    + rewrite nth_error_app_context_lt in H;
        rewrite ?app_context_length, ?lift_context_length in *; [|lia].
      rewrite nth_error_app_context_lt in H;
        rewrite ?app_context_length, ?lift_context_length in *; [|lia].
      rewrite nth_error_lift_context_eq in H.
      case_eq (nth_error Γ' n); [|intro HH; rewrite HH in H; discriminate].
      intros [na [bd|] ty] HH; rewrite HH in H; [|discriminate].
      eexists. split.
      { constructor. rewrite nth_error_app_context_lt; [|lia].
        rewrite HH. reflexivity. }
      clear HH. invs H.
      rewrite permute_lift; [|lia]. f_equal; lia.
  - destruct M; invs H.
    apply lift_Apps_Construct_inv in H3.
    destruct H3 as [args' [H1 H2]]; subst.
    eexists. split.
    { constructor. }
    symmetry; apply lift_iota_red.
  - apply lift_Apps_Fix_inv in H1.
    destruct H1 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_fix in H.
    destruct (unfold_fix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    invs H. rewrite <- lift_is_constructor in H0.
    eexists; split.
    { econstructor; tea. }
    symmetry; apply lift_mkApps.
  - destruct M; invs H0.
    apply lift_Apps_CoFix_inv in H4.
    destruct H4 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_cofix in H.
    destruct (unfold_cofix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    invs H. eexists; split.
    { econstructor; tea. }
    cbn. f_equal. symmetry; apply lift_mkApps.
  - destruct M; invs H0.
    apply lift_Apps_CoFix_inv in H3.
    destruct H3 as [mfix' [args' [H1 [H2 H3]]]]; subst.
    rewrite lift_unfold_cofix in H.
    destruct (unfold_cofix mfix' idx) as [[]|] eqn:eq; [|discriminate].
    invs H. eexists; split.
    { econstructor; tea. }
    cbn. f_equal. symmetry; apply lift_mkApps.
  - destruct M; invs H1.
    eexists; split.
    { econstructor; tea. }
    rewrite PCUICUnivSubst.lift_subst_instance_constr.
    f_equal. destruct decl as []; cbn in *; subst.
    eapply lift_declared_constant in H; tas.
    apply (f_equal cst_body) in H; cbn in *.
    apply some_inj in H; eassumption.
  - destruct M; invs H0.
    apply lift_Apps_Construct_inv in H3.
    destruct H3 as [args' [H1 H2]]; subst.
    rewrite nth_error_map in H.
    destruct (nth_error args' (pars + narg)) eqn:X; invs H.
    eexists; split.
    { econstructor; tea. }
    reflexivity.

  - destruct M0; invs H0.
    edestruct IHred1 as [M1' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 10; eassumption. }
    cbn; congruence.
  - destruct M0; invs H0.
    edestruct (IHred1 Γ0 (Γ' ,, vass na M0_1)) as [M2' [H1 H2]];
      tas; try reflexivity.
    { rewrite lift_context_snoc. rewrite app_context_cons; f_equal.
      now rewrite Nat.add_0_r. }
    eexists. split.
    { constructor 11; eassumption. }
    cbn in *; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M1' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 12; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 13; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct (IHred1 Γ0 (Γ' ,, vdef na M1 M2)) as [M3' [H1 H2]];
      tas; try reflexivity.
    { rewrite lift_context_snoc. rewrite app_context_cons; f_equal.
      now rewrite Nat.add_0_r. }
    eexists. split.
    { constructor 14; eassumption. }
    cbn in *; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M1' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 15; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 16; eassumption. }
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ brs,
                OnOne2 (on_Trel_eq (red1 Σ (Γ0 ,,, Γ')) snd fst) brs0 brs
                × brs' = map (on_snd (lift #|Γ''| #|Γ'|)) brs). {
      clear -X HΣ.
      dependent induction X.
      + destruct brs0 as [|[brs0 brs0'] brs1]; invs H.
        destruct p as [[H1 H2] H3].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        exists ((brs0, N) :: brs1). split.
        { constructor; split; tas; reflexivity. }
        destruct hd'; cbn in *; unfold on_snd; cbn. congruence.
      + destruct brs0 as [|[brs0 brs0'] brs1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn. congruence. }
    destruct XX as [brs [Hb1 Hb2]].
    eexists. split.
    { constructor 17; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 18; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 19; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 20; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct IHred1 as [M2' [H1 H2]]; tas; try reflexivity.
    eexists. split.
    { constructor 21; eassumption. }
    cbn; congruence.
  - destruct M; invs H0.
    edestruct (IHred1 Γ0 (Γ' ,, vass na M3)) as [M2' [H1 H2]];
      tas; try reflexivity.
    { rewrite lift_context_snoc. rewrite app_context_cons; f_equal.
      now rewrite Nat.add_0_r. }
    eexists. split.
    { constructor 22; eassumption. }
    cbn in *; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l,
                OnOne2 (red1 Σ (Γ0 ,,, Γ')) l0 l
                × l' = map (lift #|Γ''| #|Γ'|) l). {
      clear -X HΣ.
      dependent induction X.
      + destruct l0 as [|l0 l1]; invs H.
        destruct p as [H1 H2].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        exists (N :: l1). split.
        { constructor; assumption. }
        cbn; congruence.
      + destruct l0 as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 23; eassumption. }
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l,
                OnOne2 (fun x y => red1 Σ (Γ0 ,,, Γ') (dtype x) (dtype y)
                  × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix l
                × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                                       (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      set (k := #|mfix|) in *; clearbody k.
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        destruct l0 as [na ty bd arg]; cbn in *.
        exists ({| dname := na; dtype := N; dbody := bd; rarg := arg |} :: l1). split.
        { constructor; cbn; now split. }
        cbn; f_equal. unfold map_def; destruct hd'; cbn in *. congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 24; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l, OnOne2 (fun x y =>
     red1 Σ (Γ0 ,,, Γ' ,,, fix_context mfix) (dbody x) (dbody y)
     × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix l
     × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                            (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      rewrite lift_fix_context in X.
      pose proof (lift_context_app #|Γ''| 0 Γ' (fix_context mfix)) as e.
      rewrite Nat.add_0_r in e.
      rewrite <- app_context_assoc, <- e in X; clear e.
      (* pose proof (fix_context_length mfix) as Hctx. *)
      rewrite <- (fix_context_length mfix) in *.
      set (ctx := fix_context mfix) in *; clearbody ctx.
      (* set (k := #|mfix|) in *; clearbody k. *)
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        destruct l0 as [na ty bd arg]; simpl in *.
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        { f_equal. f_equal.
          now rewrite app_context_length. }
        exists ({| dname := na; dtype := ty; dbody := N; rarg := arg |} :: l1). split.
        { constructor; simpl; split; try reflexivity.
          now rewrite app_context_assoc in HN1. }
        cbn; f_equal. unfold map_def; destruct hd'; simpl in *.
          rewrite app_context_length in HN2; simpl in HN2.
          congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 25; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l,
                OnOne2 (fun x y => red1 Σ (Γ0 ,,, Γ') (dtype x) (dtype y)
                  × (dname x, dbody x, rarg x) = (dname y, dbody y, rarg y)) mfix l
                × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                                       (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      set (k := #|mfix|) in *; clearbody k.
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        destruct l0 as [na ty bd arg]; cbn in *.
        exists ({| dname := na; dtype := N; dbody := bd; rarg := arg |} :: l1). split.
        { constructor; cbn; now split. }
        cbn; f_equal. unfold map_def; destruct hd'; cbn in *. congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 26; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
  - destruct M; invs H.
    assert (XX: ∑ l, OnOne2 (fun x y =>
     red1 Σ (Γ0 ,,, Γ' ,,, fix_context mfix) (dbody x) (dbody y)
     × (dname x, dtype x, rarg x) = (dname y, dtype y, rarg y)) mfix l
     × mfix1 = map (map_def (lift #|Γ''| #|Γ'|)
                            (lift #|Γ''| (#|mfix| + #|Γ'|))) l). {
      clear -X HΣ.
      rewrite lift_fix_context in X.
      pose proof (lift_context_app #|Γ''| 0 Γ' (fix_context mfix)) as e.
      rewrite Nat.add_0_r in e.
      rewrite <- app_context_assoc, <- e in X; clear e.
      (* pose proof (fix_context_length mfix) as Hctx. *)
      rewrite <- (fix_context_length mfix) in *.
      set (ctx := fix_context mfix) in *; clearbody ctx.
      (* set (k := #|mfix|) in *; clearbody k. *)
      dependent induction X.
      + destruct mfix as [|l0 l1]; invs H.
        destruct p as [[H1 H2] H3].
        destruct l0 as [na ty bd arg]; simpl in *.
        edestruct H2 as [N [HN1 HN2]]; tas; try reflexivity.
        { f_equal. f_equal.
          now rewrite app_context_length. }
        exists ({| dname := na; dtype := ty; dbody := N; rarg := arg |} :: l1). split.
        { constructor; simpl; split; try reflexivity.
          now rewrite app_context_assoc in HN1. }
        cbn; f_equal. unfold map_def; destruct hd'; simpl in *.
          rewrite app_context_length in HN2; simpl in HN2.
          congruence.
      + destruct mfix as [|l0 l1]; invs H.
        edestruct IHX as [N [HN1 HN2]]; tas; try reflexivity.
        eexists; split.
        { constructor 2; eassumption. }
        cbn; congruence. }
    destruct XX as [l [Hb1 Hb2]].
    eexists. split.
    { constructor 27; eassumption. }
    apply OnOne2_length in Hb1.
    cbn; congruence.
Qed.




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
