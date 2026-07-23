(** Fundamental Lemma of Game-Playing: the semantic core.

  Standalone probability lemma, no packages/pRHL/adversaries involved.
  Given a coupling [d] of two distributions [d0] and [d1] on the SAME
  outcome type [T], and predicates [bad]/[event] on [T] such that:
  - [bad] is "synced" across the coupling's support (whenever
    [d (x, y) > 0], [bad x = bad y]), and
  - outside of [bad], [event] agrees across the coupling's support
    (whenever [d (x, y) > 0] and [bad x = false], [event x = event y]),
  then [`|\P_[d0] event - \P_[d1] event| <= \P_[d0] bad] (and, as a
  byproduct, [\P_[d0] bad = \P_[d1] bad]).

  This is the standard "identical until bad" probability computation
  underlying the Fundamental Lemma of Game Playing (Bellare-Rogaway).
  SSProve does not currently have this lemma (confirmed by searching
  pkg_advantage.v / pkg_rhl.v / Theta_exCP.v / Couplings.v -- see the
  discussion in HKDF.v). This file supplies the semantic (distribution
  -level) half; lifting it through packages/adversaries to a bound on
  [AdvantageE] is separate, further work (see pkg_upto_bad.v). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths".
Unset SsrOldRewriteGoalsOrder.

Import GRing.Theory.
Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Local Open Scope ring_scope.

Section UpToBad.

  Context {R : realType} {T : choiceType}.
  Context (d0 d1 : {distr T / R}) (d : {distr (T * T) / R}).
  Context (Hd0 : dfst d = d0) (Hd1 : dsnd d = d1).
  Context (event bad : pred T).
  Context (Hbad_sync : forall x y, (0 < d (x, y))%R -> bad x = bad y).
  Context (Hagree :
    forall x y, (0 < d (x, y))%R -> bad x = false -> event x = event y).

  Let posE (p : T * T) : (0 <= d p)%R := ge0_mu d p.

  Let G (p : T * T) : R := (bad p.1)%:R * d p.
  Let H (p : T * T) : R := (bad p.2)%:R * d p.
  Let A (p : T * T) : R := (event p.1)%:R * d p.
  Let B (p : T * T) : R := (event p.2)%:R * d p.

  Lemma GH_eq : forall p, G p = H p.
  Proof.
    move=> [x y] /=. rewrite /G /H /=.
    case: (d (x, y) =P 0) => Hd0xy.
    - by rewrite Hd0xy !mulr0.
    - have Hpos : (0 < d (x, y))%R.
      { rewrite lt0r. apply/andP; split; [by apply/eqP | exact: posE (x,y) ]. }
      by rewrite (Hbad_sync x y Hpos).
  Qed.

  Lemma AG_bound : forall p, A p <= B p + G p.
  Proof.
    move=> [x y] /=. rewrite /A /B /G /=.
    case: (d (x, y) =P 0) => Hd0xy.
    - by rewrite Hd0xy !mulr0 addr0.
    - have Hpos : (0 < d (x, y))%R.
      { rewrite lt0r. apply/andP; split; [by apply/eqP | exact: posE (x,y) ]. }
      case: (boolP (bad x)) => Hbadx.
      + rewrite mul1r.
        have HxD : (event x)%:R * d (x, y) <= d (x, y).
        { case: (event x); by rewrite ?mul1r ?mul0r // posE. }
        apply: (le_trans HxD). rewrite lerDr.
        case: (event y); by rewrite ?mul1r ?mul0r // posE.
      + have -> : event x = event y.
        { apply: Hagree Hpos _. exact: (negbTE Hbadx). }
        by rewrite mul0r addr0 lexx.
  Qed.

  Lemma BG_bound : forall p, B p <= A p + G p.
  Proof.
    move=> [x y] /=. rewrite /A /B /G /=.
    case: (d (x, y) =P 0) => Hd0xy.
    - by rewrite Hd0xy !mulr0 addr0.
    - have Hpos : (0 < d (x, y))%R.
      { rewrite lt0r. apply/andP; split; [by apply/eqP | exact: posE (x,y) ]. }
      case: (boolP (bad x)) => Hbadx.
      + rewrite mul1r.
        have HyD : (event y)%:R * d (x, y) <= d (x, y).
        { case: (event y); by rewrite ?mul1r ?mul0r // posE. }
        apply: (le_trans HyD). rewrite lerDr.
        case: (event x); by rewrite ?mul1r ?mul0r // posE.
      + have -> : event x = event y.
        { apply: Hagree Hpos _. exact: (negbTE Hbadx). }
        by rewrite mul0r addr0 lexx.
  Qed.

  (* Collapsing a [psum] over the coupling's pairs down to a marginal
    [\P_[.]] statement: pull the (0/1-valued, hence nonneg) coefficient
    into the inner [psum] via [psumZ], then recognise the inner [psum]
    as the marginal ([dfstE]/[dsndE]) which is exactly [d0]/[d1] by the
    coupling hypotheses. *)
  Lemma A_collapse : psum A = \P_[d0] event.
  Proof.
    rewrite /A /pr (psum_pair (summable_condl _ (summable_mu d))).
    apply: eq_psum => x /=.
    rewrite (psumZ _ (ler0n _ (event x))) -dfstE Hd0 //.
  Qed.

  Lemma B_collapse : psum B = \P_[d1] event.
  Proof.
    rewrite /B /pr (psum_pair_swap (summable_condl _ (summable_mu d))).
    apply: eq_psum => y /=.
    rewrite (psumZ _ (ler0n _ (event y))) -__deprecated__dsndE Hd1 //.
  Qed.

  Lemma G_collapse : psum G = \P_[d0] bad.
  Proof.
    rewrite /G /pr (psum_pair (summable_condl _ (summable_mu d))).
    apply: eq_psum => x /=.
    rewrite (psumZ _ (ler0n _ (bad x))) -dfstE Hd0 //.
  Qed.

  Lemma H_collapse : psum H = \P_[d1] bad.
  Proof.
    rewrite /H /pr (psum_pair_swap (summable_condl _ (summable_mu d))).
    apply: eq_psum => y /=.
    rewrite (psumZ _ (ler0n _ (bad y))) -__deprecated__dsndE Hd1 //.
  Qed.

  (** The Fundamental Lemma's semantic core: [bad] has the same
    probability on both sides, and outside of it the two events'
    probabilities can differ by at most that much. *)
  Lemma pr_bad_sync : \P_[d0] bad = \P_[d1] bad.
  Proof.
    rewrite -G_collapse -H_collapse.
    apply: eq_psum. exact: GH_eq.
  Qed.

  Lemma pr_up_to_bad :
    `| \P_[d0] event - \P_[d1] event | <= \P_[d0] bad.
  Proof.
    have HAnn : forall p, (0 <= A p)%R.
    { move=> p. rewrite /A. exact: mulr_ge0 (ler0n _ _) (posE p). }
    have HBnn : forall p, (0 <= B p)%R.
    { move=> p. rewrite /B. exact: mulr_ge0 (ler0n _ _) (posE p). }
    have HGnn : forall p, (0 <= G p)%R.
    { move=> p. rewrite /G. exact: mulr_ge0 (ler0n _ _) (posE p). }
    have HGsum : summable (fun p => G p) := summable_condl _ (summable_mu d).
    have HAsum : summable (fun p => A p) := summable_condl _ (summable_mu d).
    have HBsum : summable (fun p => B p) := summable_condl _ (summable_mu d).
    rewrite ler_norml. apply/andP; split.
    - rewrite lerBrDl lerBlDl -B_collapse -G_collapse -A_collapse addrC.
      rewrite -(psumD HAnn HGnn HAsum HGsum).
      apply: le_psum; last exact: (summableD HAsum HGsum).
      move=> p. apply/andP; split; [exact: HBnn | exact: BG_bound].
    - rewrite lerBlDl -A_collapse -B_collapse -G_collapse.
      rewrite -(psumD HBnn HGnn HBsum HGsum).
      apply: le_psum; last exact: (summableD HBsum HGsum).
      move=> p. apply/andP; split; [exact: HAnn | exact: AG_bound].
  Qed.

End UpToBad.
