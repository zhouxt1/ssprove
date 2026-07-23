(** Standalone birthday-bound combinatorics, no packages/adversaries involved.

  Sampling [q] values one at a time, uniformly from a space of size [N],
  and flagging "bad" the first time a freshly-sampled value repeats one
  already seen: Pr[bad] <= q*(q-1) / (2*N). This is the pure-probability
  fact underlying step (2c) of the up-to-bad argument in HKDF.v.

  Note for anyone extending this file: [lia] and [lra] do not work here
  (confirmed by direct test) -- both fail with "Cannot find witness" even
  on trivial goals like [k.+1 = k + 1] or [x + y = y + x], because they
  are hard-coded to recognise Coq/Stdlib's own [nat]/[R] operations, not
  mathcomp's algebraic-hierarchy notations (mathcomp's [nat] arithmetic
  goes through [addn]/[muln]/etc, and [R] here is an abstract [realType],
  not [Coq.Reals.R]). All arithmetic below is manual [ssrnat]/[ssralg]
  rewriting instead. The other recurring gotcha: small literals like [2]
  are internally successors ([1.+1]), so generic lemmas with a [_.+1]
  pattern (e.g. [addnS], [mulnS]) can spuriously match a bare numeral
  instead of the intended subterm -- when that happens, pin the exact
  occurrence with [rewrite (lemma explicit_args)] or [rewrite -[x]lemma]
  rather than leaving arguments to unification.
*)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths".
Unset SsrOldRewriteGoalsOrder.

From SSProve.Crypt Require Import Axioms UniformDistrLemmas.

Import GRing.Theory.
Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Local Open Scope ring_scope.

Section Birthday.

  Context (N : nat) (HN : (0 < N)%nat).

  Definition unif_ordN : {distr 'I_N / R} := mkdistr is_uniform.

  Fixpoint bad_dist (q : nat) (used : {set 'I_N}) : {distr (bool * {set 'I_N}) / R} :=
    match q with
    | 0 => dunit (false, used)
    | q'.+1 =>
        dlet (fun x =>
                if x \in used then dunit (true, used)
                else bad_dist q' (x |: used))
             unif_ordN
    end.

  (* NAT arithmetic throughout, cast to [R] only once at the end -- avoids
    ever needing to reason about signs / real subtraction. For [q = 0] the
    truncated subtraction inside is irrelevant since it's multiplied by 0;
    for [q > 0] it is exact ([2*k+q >= q >= 1]). *)
  Definition bad_bound (q k : nat) : R := (q * (2 * k + q - 1))%:R / (2 * N)%:R.

  Lemma bad_bound_ge0 : forall q k, 0 <= bad_bound q k.
  Proof.
    intros q k. rewrite /bad_bound.
    by apply: divr_ge0; rewrite ler0n.
  Qed.

  Lemma pr_unif_set (used : {set 'I_N}) :
    \P_[ unif_ordN ] (mem used) = #|used|%:R / N%:R.
  Proof.
    have Huniq : uniq (enum used) := enum_uniq used.
    have Heq : (mem used) = [pred x in enum used] :> pred 'I_N.
    { apply: functional_extensionality => x. rewrite /= -topredE /=. by rewrite mem_enum. }
    rewrite Heq.
    rewrite (pr_mem unif_ordN Huniq).
    under eq_bigr => x _ do rewrite /unif_ordN mkdistrE.
    rewrite big_const_seq count_predT -cardE /r card_ord.
    rewrite -mulr_natl.
    rewrite -[1%:~R]/(1 : R) -[N%:~R]/(N%:R : R).
    rewrite mulr1.
    elim: #|used| => [| n IHn] /=.
    - by rewrite mul0r.
    - by rewrite IHn -natr1 -mulrDl addrC.
  Qed.

  Lemma bad_dist_bound :
    forall q (used : {set 'I_N}),
      \P_[ bad_dist q used ] (fun '(b, _) => b) <= bad_bound q #|used|.
  Proof.
    induction q as [| q IHq]; intros used.
    - rewrite /bad_bound /= mul0n GRing.mul0r.
      rewrite pr_dunit /=.
      apply: lexx.
    - rewrite /=.
      rewrite __deprecated__pr_dlet.
      pose C := bad_bound q #|used|.+1.
      have Hpt : forall x : 'I_N,
        \P_[ if x \in used then dunit (true, used) else bad_dist q (x |: used) ]
          (fun '(b, _) => b) <= (x \in used)%:R + C.
      { move=> x.
        case: (boolP (x \in used)) => Hx.
        - rewrite pr_dunit /=.
          rewrite lerDl. apply: bad_bound_ge0.
        - rewrite GRing.add0r.
          apply: (le_trans (IHq (x |: used))).
          rewrite /C cardsU1 Hx add1n.
          apply: lexx.
      }
      have Hs1 : \E?_[ unif_ordN ]
        (fun x => \P_[ if x \in used then dunit (true, used) else bad_dist q (x |: used) ] (fun '(b, _) => b)).
      { apply: summable_has_exp. apply: summable_fin. }
      have Hs2 : \E?_[ unif_ordN ] (fun x => (x \in used)%:R + C).
      { apply: summable_has_exp. apply: summable_fin. }
      have Hstep := le_exp Hs1 Hs2 Hpt.
      apply: (le_trans Hstep).
      have Hbc := bad_bound_ge0 q #|used|.+1. rewrite -/C in Hbc.
      have -> :
        \E_[ unif_ordN ] (fun x => (x \in used)%:R + C)
        = \P_[ unif_ordN ] (mem used) + \P_[ unif_ordN ] predT * C.
      { rewrite /esp.
        have Heq : (fun x => ((x \in used)%:R + C) * unif_ordN x)
          =1 ((fun x => (x \in used)%:R * unif_ordN x) \+ (fun x => C * unif_ordN x)).
        { move=> x /=. by rewrite mulrDl. }
        have Hnn1 : forall x : 'I_N, 0 <= (x \in used)%:R * unif_ordN x.
        { move=> x. apply: mulr_ge0; [exact: ler0n | exact: ge0_mu]. }
        have Hnn2 : forall x : 'I_N, 0 <= C * unif_ordN x.
        { move=> x. apply: mulr_ge0; [exact: Hbc | exact: ge0_mu]. }
        rewrite (eq_sum Heq).
        have HsumPsum :
          sum ((fun x => (x \in used)%:R * unif_ordN x) \+ (fun x => C * unif_ordN x))
          = psum ((fun x => (x \in used)%:R * unif_ordN x) \+ (fun x => C * unif_ordN x)).
        { symmetry. apply: psum_sum.
          move=> x /=. by rewrite addr_ge0 // ?Hnn1 ?Hnn2. }
        rewrite HsumPsum.
        have HpsumD :
          psum ((fun x => (x \in used)%:R * unif_ordN x) \+ (fun x => C * unif_ordN x))
          = psum (fun x => (x \in used)%:R * unif_ordN x) + psum (fun x => C * unif_ordN x).
        { exact: (psumD Hnn1 Hnn2 (summable_fin _) (summable_fin _)). }
        rewrite HpsumD [X in _ = X + _]/pr.
        congr (_ + _).
        rewrite [in RHS]mulrC -(psumZ _ Hbc).
        apply: eq_psum => x /=.
        by rewrite mul1r.
      }
      have Hconst : \P_[unif_ordN] predT * C <= C.
      { rewrite -[X in _ <= X]mul1r ler_wpM2r //. exact: le1_pr. }
      rewrite pr_unif_set.
      apply: (le_trans (lerD (lexx _) Hconst)).
      rewrite /C /bad_bound.
      move: #|used| => k.
      have e1 : (2 * k.+1 + q - 1)%N = (2 * k + q + 1)%N.
      { rewrite -[k.+1]addn1 mulnDr muln1 addnAC.
        by rewrite (addnS (2 * k + q) 1) subn1. }
      have e2 : (2 * k + q.+1 - 1)%N = (2 * k + q)%N.
      { by rewrite -[q.+1]addn1 addnA addnK. }
      rewrite e1 e2.
      have Hcombine : k%:R / N%:R = (2 * k)%:R / (2 * N)%:R :> R.
      { rewrite !natrM invfM mulrA (mulrAC 2%:R) divff ?mul1r //.
        by rewrite pnatr_eq0. }
      rewrite Hcombine -mulrDl.
      rewrite ler_pdivrMr; first by rewrite ltr0n muln_gt0 HN.
      rewrite mulrAC -mulrA divff;
        first by rewrite pnatr_eq0 muln_eq0 negb_or -!lt0n HN.
      rewrite mulr1 -natrD ler_nat.
      rewrite -[q.+1]addn1 mulnDl mul1n (mulnDr q (2 * k + q) 1) muln1.
      rewrite (addnCA (2 * k) (q * (2 * k + q)) q).
      exact: leqnn.
  Qed.

End Birthday.
