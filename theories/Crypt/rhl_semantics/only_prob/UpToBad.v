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

From SSProve.Crypt Require Import Axioms.

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

(** The "independent" (product) coupling of two distributions, and the
  fact that it's a genuine coupling. This is exactly the abandoned
  [Independent_coupling] section at the bottom of Couplings.v (fully
  commented out there, ending in three [Admitted]s) -- needed for the
  up-to-bad adversary-linking argument: once a shared [bad] flag is
  already true, the two sides of the coupling no longer need to be
  related by shared-code induction at all; each side just needs to
  keep [bad] true *on its own*, and the product coupling combines two
  such independent, unary facts into one relational statement for free
  (its whole support is exactly the product of the two marginals, so a
  postcondition of the shape [phi0 x /\ phi1 y] transfers immediately
  from "phi0 holds on d0's support" and "phi1 holds on d1's support"). *)
Section IndependentCoupling.

  Context {R : realType} {T1 T2 : choiceType}.
  Context (c1 : {distr T1 / R}) (c2 : {distr T2 / R}).
  (* [c1]/[c2] need to be *lossless* (total mass exactly 1, not just
    <=1) for the marginals of the product coupling to come out exactly
    right -- true of any package's underlying distribution (validity
    gives losslessness), but not of an arbitrary subdistribution, so
    it has to be assumed here explicitly. *)
  Context (Hc1 : psum c1 = 1) (Hc2 : psum c2 = 1).

  Definition indp : {distr (T1 * T2) / R} :=
    \dlet_(x <- c1) \dlet_(y <- c2) dunit (x, y).

  Lemma indp_ext (x : T1) (y : T2) : indp (x, y) = c1 x * c2 y.
  Proof.
    rewrite /indp dletE.
    have Hinner : forall x0, (\dlet_(y0 <- c2) dunit (x0, y0)) (x, y) = (x0 == x)%:R * c2 y.
    { move=> x0. rewrite dletE.
      transitivity (psum (fun y0 => (x0 == x)%:R * ((y0 == y)%:R * c2 y0))).
      - apply: eq_psum => y0. rewrite dunit1E xpair_eqE.
        case: (eqVneq x0 x) => Hx0; case: (eqVneq y0 y) => Hy0;
          rewrite ?Hx0 ?Hy0 ?eqxx //= ?mul0r ?mul1r ?mulr0 ?mulr1 //.
      - rewrite (psumZ _ (ler0n _ _)). congr (_ * _). exact: esym (pr_pred1 c2 y).
    }
    transitivity (psum (fun x0 => (x0 == x)%:R * (c1 x * c2 y))).
    - apply: eq_psum => x0. rewrite Hinner.
      case: (eqVneq x0 x) => Hx0.
      + by rewrite Hx0 !mul1r.
      + have Hf : (false%:R : R) = 0 by [].
        by rewrite Hf ?mul0r ?mulr0.
    - transitivity (psum (fun x0 => (c1 x * c2 y) * (x0 == x)%:R)).
      { apply: eq_psum => x0. by rewrite mulrC. }
      rewrite (psumZ _ (mulr_ge0 (ge0_mu c1 x) (ge0_mu c2 y))).
      transitivity ((c1 x * c2 y) * psum (fun x0 => dunit (T:=T1) x x0)).
      { congr (_ * _). apply: eq_psum => x0. by rewrite dunit1E eq_sym. }
      have Hdunit1 : psum (fun x0 => @dunit R T1 x x0) = 1.
      { have Hle1 : psum (fun x0 => @dunit R T1 x x0) <= 1 := @le1_mu R T1 (dunit x).
        have Hge1 : (1:R) <= psum (fun x0 => @dunit R T1 x x0).
        { have H1 : `| @dunit R T1 x x | <= psum (fun x0 => @dunit R T1 x x0)
            := @ger1_psum R T1 (dunit x) x (@summable_mu R T1 (dunit x)).
          by rewrite dunit1E eqxx normr1 in H1. }
        apply: Order.POrderTheory.le_anti. by rewrite Hle1 Hge1. }
      by rewrite Hdunit1 mulr1.
  Qed.

  (* Generic distr-extensionality: same pointwise function forces the
    same record, the other fields being irrelevant by proof irrelevance.
    (SubDistr.v has [distr_ext], but only for its own globally-fixed [R]
    from Axioms.v, not our section-local, arbitrary [R : realType].) *)
  Lemma distr_ext_local {A : choiceType} (mu nu : {distr A / R}) :
    mu =1 nu -> mu = nu.
  Proof.
    destruct mu as [mu muz mu_smbl mu_psum], nu as [nu nuz nu_smbl nu_psum].
    simpl. move=> H. move: muz mu_smbl mu_psum nuz nu_smbl nu_psum.
    apply boolp.funext in H. rewrite H. intuition. f_equal.
    all: apply proof_irrelevance.
  Qed.

  Lemma indp_lmg : dfst indp = c1.
  Proof.
    apply: distr_ext_local => x. rewrite dfstE.
    transitivity (psum (fun y => c1 x * c2 y)).
    { apply: eq_psum => y. exact: indp_ext. }
    by rewrite (psumZ _ (ge0_mu c1 x)) Hc2 mulr1.
  Qed.

  Lemma indp_rmg : dsnd indp = c2.
  Proof.
    apply: distr_ext_local => y. rewrite __deprecated__dsndE.
    transitivity (psum (fun x => c2 y * c1 x)).
    { apply: eq_psum => x. rewrite mulrC. exact: indp_ext. }
    by rewrite (psumZ _ (ge0_mu c2 y)) Hc1 mulr1.
  Qed.

  Lemma indp_coupling : dfst indp = c1 /\ dsnd indp = c2.
  Proof. split; [exact: indp_lmg | exact: indp_rmg]. Qed.

End IndependentCoupling.
