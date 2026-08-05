import SchedulingPaper.MixedQuotaRounding
import SchedulingPaper.HarmonicOperational
import Mathlib.Tactic

/-!
# Fixed-offset limits for rounded mixed quotas

Dynamic cap and harmonic counts differ from a common integral scale by
bounded integer offsets.  This module proves that fixed nonnegative offsets
do not change the normalized limiting benchmark.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound

def affineCount (P d q : ℕ) : ℕ := P * (q + 1) + d

theorem affineCount_pos {P d q : ℕ} (hP : 0 < P) :
    0 < affineCount P d q := by
  unfold affineCount
  positivity

theorem affineCount_div_scale_tendsto (P d : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (affineCount P d q : ℝ) / (q + 1 : ℝ))
      Filter.atTop (nhds (P : ℝ)) := by
  let correction : ℕ → ℝ :=
    fun q => (d : ℝ) / (q + 1 : ℝ)
  have hcorrection :
      Filter.Tendsto correction Filter.atTop (nhds 0) := by
    have ht :=
      (tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto
      (fun q : ℕ => (d : ℝ) / ((q + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) at ht
    simpa only [Nat.cast_add, Nat.cast_one] using ht
  have hsum :=
    (tendsto_const_nhds :
      Filter.Tendsto (fun _q : ℕ => (P : ℝ))
        Filter.atTop (nhds (P : ℝ))).add hcorrection
  convert hsum using 1
  funext q
  dsimp [correction, affineCount]
  have hscale : (q + 1 : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp [hscale]
  ring

theorem affineCount_ratio_tendsto
    {P Q : ℕ} (hQ : 0 < Q) (d e : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (affineCount P d q : ℝ) /
          (affineCount Q e q : ℝ))
      Filter.atTop (nhds ((P : ℝ) / (Q : ℝ))) := by
  have hP := affineCount_div_scale_tendsto P d
  have hQlim := affineCount_div_scale_tendsto Q e
  have hdiv :=
    hP.div hQlim (by exact_mod_cast hQ.ne')
  convert hdiv using 1
  funext q
  have hs : (q + 1 : ℝ) ≠ 0 := by positivity
  have hden : (affineCount Q e q : ℝ) ≠ 0 := by
    exact_mod_cast (affineCount_pos (d := e) (q := q) hQ).ne'
  change
    (affineCount P d q : ℝ) / (affineCount Q e q : ℝ) =
      ((affineCount P d q : ℝ) / (q + 1 : ℝ)) /
        ((affineCount Q e q : ℝ) / (q + 1 : ℝ))
  field_simp [hs, hden]

theorem affineCount_inv_tendsto_zero
    {P : ℕ} (hP : 0 < P) (d : ℕ) :
    Filter.Tendsto
      (fun q : ℕ => 1 / (affineCount P d q : ℝ))
      Filter.atTop (nhds 0) := by
  have hone :
      Filter.Tendsto
        (fun q : ℕ => 1 / (q + 1 : ℝ))
        Filter.atTop (nhds 0) := by
    have ht :=
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto
      (fun q : ℕ => 1 / ((q + 1 : ℕ) : ℝ))
      Filter.atTop (nhds 0) at ht
    simpa only [Nat.cast_add, Nat.cast_one] using ht
  have hden := affineCount_div_scale_tendsto P d
  have hdiv := hone.div hden (by exact_mod_cast hP.ne')
  convert hdiv using 1
  · funext q
    have hs : (q + 1 : ℝ) ≠ 0 := by positivity
    have hp : (affineCount P d q : ℝ) ≠ 0 := by
      exact_mod_cast (affineCount_pos (d := d) (q := q) hP).ne'
    change
      1 / (affineCount P d q : ℝ) =
        (1 / (q + 1 : ℝ)) /
          ((affineCount P d q : ℝ) / (q + 1 : ℝ))
    field_simp [hs, hp]
  · simp

/-- The harmonic ratio attached to two affine counts. -/
def affineRatio (A B a b q : ℕ) : ℝ :=
  (affineCount A a q : ℝ) / (affineCount B b q : ℝ)

theorem affineRatio_tendsto
    {A B : ℕ} (hB : 0 < B) (a b : ℕ) :
    Filter.Tendsto (affineRatio A B a b)
      Filter.atTop (nhds ((A : ℝ) / (B : ℝ))) := by
  simpa [affineRatio] using
    affineCount_ratio_tendsto (P := A) hB a b

/-- The processing-mass Riemann sum remains convergent when the harmonic
ratio varies through affine integer approximations. -/
theorem mixedProcessingRiemannSum_affine_tendsto
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (a b : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        mixedProcessingRiemannSum
          (affineRatio A B a b q)
          (affineCount A a q - 1))
      Filter.atTop
      (nhds
        ((1 + (A : ℝ) / (B : ℝ)) *
            Real.log (1 + (A : ℝ) / (B : ℝ)) -
          (A : ℝ) / (B : ℝ))) := by
  let α : ℝ := (A : ℝ) / (B : ℝ)
  let αq : ℕ → ℝ := affineRatio A B a b
  let target : ℝ → ℝ :=
    fun x => (1 + x) * Real.log (1 + x) - x
  have hαpos : 0 < α := by
    dsimp [α]
    positivity
  have hαq : Filter.Tendsto αq Filter.atTop (nhds α) := by
    simpa [αq, α] using affineRatio_tendsto hB a b
  have hone :
      Filter.Tendsto (fun q => 1 + αq q)
        Filter.atTop (nhds (1 + α)) :=
    tendsto_const_nhds.add hαq
  have hlog :
      Filter.Tendsto (fun q => Real.log (1 + αq q))
        Filter.atTop (nhds (Real.log (1 + α))) :=
    (Real.continuousAt_log (by linarith : 1 + α ≠ 0)).tendsto.comp hone
  have htarget :
      Filter.Tendsto (fun q => target (αq q))
        Filter.atTop (nhds (target α)) := by
    simpa [target] using (hone.mul hlog).sub hαq
  have hinv :=
    affineCount_inv_tendsto_zero hA a
  have herr :
      Filter.Tendsto
        (fun q => (αq q) ^ 2 /
          (affineCount A a q : ℝ))
        Filter.atTop (nhds 0) := by
    have hmul := (hαq.pow 2).mul hinv
    simpa [div_eq_mul_inv] using hmul
  have hdiff :
      Filter.Tendsto
        (fun q =>
          mixedProcessingRiemannSum
              (αq q) (affineCount A a q - 1) -
            target (αq q))
        Filter.atTop (nhds 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero
      (g := fun q =>
        (αq q) ^ 2 / (affineCount A a q : ℝ))
    · intro q
      exact dist_nonneg
    · intro q
      have hK : 0 < affineCount A a q :=
        affineCount_pos hA
      have hαqpos : 0 < αq q := by
        dsimp [αq, affineRatio]
        exact div_pos
          (by exact_mod_cast affineCount_pos (d := a) (q := q) hA)
          (by exact_mod_cast affineCount_pos (d := b) (q := q) hB)
      have hbound :=
        mixedProcessingRiemannSum_error_le
          hαqpos (affineCount A a q - 1)
      have hsucc :
          affineCount A a q - 1 + 1 =
            affineCount A a q := by omega
      have hsuccReal :
          ((affineCount A a q - 1 : ℕ) : ℝ) + 1 =
            (affineCount A a q : ℝ) := by
        exact_mod_cast hsucc
      rw [mixedProcessingIntegral_eq hαqpos.le] at hbound
      simpa [Real.dist_eq, target, hsuccReal] using hbound
    · exact herr
  have hsum := hdiff.add htarget
  simpa [target, α] using hsum

/-- The normalized harmonic pair-processing expression has the same limit
under fixed affine count offsets. -/
theorem harmonicNormalizedProcessing_affine_tendsto
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (a b : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        harmonicNormalizedProcessing
          (affineRatio A B a b q) 0
          (affineCount A a q - 1))
      Filter.atTop
      (nhds (harmonicIntegral ((A : ℝ) / (B : ℝ)))) := by
  let α : ℝ := (A : ℝ) / (B : ℝ)
  let αq : ℕ → ℝ := affineRatio A B a b
  have hαpos : 0 < α := by
    dsimp [α]
    positivity
  have hαq : Filter.Tendsto αq Filter.atTop (nhds α) := by
    simpa [αq, α] using affineRatio_tendsto hB a b
  have hone :
      Filter.Tendsto (fun q => 1 + αq q)
        Filter.atTop (nhds (1 + α)) :=
    tendsto_const_nhds.add hαq
  have hlog :
      Filter.Tendsto (fun q => Real.log (1 + αq q))
        Filter.atTop (nhds (Real.log (1 + α))) :=
    (Real.continuousAt_log (by linarith : 1 + α ≠ 0)).tendsto.comp hone
  have hclosed :
      Filter.Tendsto
        (fun q => harmonicIntegralClosedForm (αq q))
        Filter.atTop (nhds (harmonicIntegralClosedForm α)) := by
    unfold harmonicIntegralClosedForm
    have hhalf :
        Filter.Tendsto (fun _q : ℕ => (1 / 2 : ℝ))
          Filter.atTop (nhds (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    have ht :=
      (((hhalf.mul (hone.pow 2)).mul hlog).sub
        (hαq.const_mul (1 / 2))).sub
        ((hαq.pow 2).const_mul (1 / 4))
    convert ht using 1 <;> ring
  have hinv :=
    affineCount_inv_tendsto_zero hA a
  have herr :
      Filter.Tendsto
        (fun q => (αq q) ^ 3 /
          (2 * (affineCount A a q : ℝ)))
        Filter.atTop (nhds 0) := by
    have hmul := (hαq.pow 3).mul hinv
    have hhalf := hmul.const_mul (1 / 2)
    convert hhalf using 1
    · funext q
      ring
    · simp
  have hdiff :
      Filter.Tendsto
        (fun q =>
          harmonicNormalizedProcessing
              (αq q) 0 (affineCount A a q - 1) -
            harmonicIntegralClosedForm (αq q))
        Filter.atTop (nhds 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero
      (g := fun q =>
        (αq q) ^ 3 /
          (2 * (affineCount A a q : ℝ)))
    · intro q
      exact dist_nonneg
    · intro q
      have hK : 0 < affineCount A a q :=
        affineCount_pos hA
      have hαqpos : 0 < αq q := by
        dsimp [αq, affineRatio]
        exact div_pos
          (by exact_mod_cast affineCount_pos (d := a) (q := q) hA)
          (by exact_mod_cast affineCount_pos (d := b) (q := q) hB)
      have hbound :=
        harmonicRiemannSum_error_le
          hαqpos (affineCount A a q - 1)
      have hsucc :
          affineCount A a q - 1 + 1 =
            affineCount A a q := by omega
      have hsuccReal :
          ((affineCount A a q - 1 : ℕ) : ℝ) + 1 =
            (affineCount A a q : ℝ) := by
        exact_mod_cast hsucc
      have hclosedEq :=
        harmonicIntegral_eq_closedForm hαqpos.le
      have heq :
          harmonicNormalizedProcessing
                (αq q) 0 (affineCount A a q - 1) -
              harmonicIntegralClosedForm (αq q) =
            (1 / 2 : ℝ) *
              (harmonicRiemannSum (αq q)
                  (affineCount A a q - 1) -
                ∫ t in 0..αq q,
                  harmonicRationalIntegrand (αq q) t) := by
        rw [← hclosedEq]
        unfold harmonicIntegral harmonicNormalizedProcessing
        simp only [zero_mul, zero_div, add_zero]
        ring
      rw [hsuccReal] at hbound
      rw [Real.dist_eq, sub_zero, heq, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc
        (1 / 2 : ℝ) *
              |harmonicRiemannSum (αq q)
                  (affineCount A a q - 1) -
                ∫ t in 0..αq q,
                  harmonicRationalIntegrand (αq q) t| ≤
            (1 / 2 : ℝ) *
              ((αq q) ^ 3 /
                (affineCount A a q : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound (by norm_num)
        _ = (αq q) ^ 3 /
              (2 * (affineCount A a q : ℝ)) := by
          field_simp
    · exact herr
  have hsum := hdiff.add hclosed
  have hlimitEq :
      harmonicIntegralClosedForm α = harmonicIntegral α :=
    (harmonicIntegral_eq_closedForm hαpos.le).symm
  rw [← hlimitEq]
  simpa using hsum

theorem harmonicPairCorrection_affine_tendsto_zero
    {A B : ℕ} (hB : 0 < B) (a b : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        harmonicPairCorrection
          (affineCount A a q) (affineCount B b q))
      Filter.atTop (nhds 0) := by
  let αq : ℕ → ℝ := affineRatio A B a b
  let zinv : ℕ → ℝ :=
    fun q => 1 / (affineCount B b q : ℝ)
  have hαq :
      Filter.Tendsto αq Filter.atTop
        (nhds ((A : ℝ) / (B : ℝ))) := by
    simpa [αq] using affineRatio_tendsto hB a b
  have hzinv :
      Filter.Tendsto zinv Filter.atTop (nhds 0) := by
    simpa [zinv] using affineCount_inv_tendsto_zero hB b
  have hupper :
      Filter.Tendsto
        (fun q =>
          (1 / 2 : ℝ) * αq q * zinv q +
            (1 / 2 : ℝ) * (αq q) ^ 2 * zinv q)
        Filter.atTop (nhds 0) := by
    have hfirst := (hαq.mul hzinv).const_mul (1 / 2)
    have hsecond :=
      ((hαq.pow 2).mul hzinv).const_mul (1 / 2)
    convert hfirst.add hsecond using 1 <;> ring
  apply squeeze_zero
    (g := fun q =>
      (1 / 2 : ℝ) * αq q * zinv q +
        (1 / 2 : ℝ) * (αq q) ^ 2 * zinv q)
  · intro q
    exact harmonicPairCorrection_nonneg
      (affineCount_pos hB)
  · intro q
    have hbound :=
      harmonicPairCorrection_le
        (K := affineCount A a q)
        (Z := affineCount B b q)
        (affineCount_pos hB)
    calc
      harmonicPairCorrection
          (affineCount A a q) (affineCount B b q) ≤
          (affineCount A a q : ℝ) /
                (2 * (affineCount B b q : ℝ) ^ 2) +
            (affineCount A a q : ℝ) ^ 2 /
                (2 * (affineCount B b q : ℝ) ^ 3) :=
        hbound
      _ = (1 / 2 : ℝ) * αq q * zinv q +
            (1 / 2 : ℝ) * (αq q) ^ 2 * zinv q := by
        dsimp [αq, zinv, affineRatio]
        have hZ : (affineCount B b q : ℝ) ≠ 0 := by
          exact_mod_cast (affineCount_pos (d := b) (q := q) hB).ne'
        field_simp [hZ]
  · exact hupper

theorem harmonicPairCost_affine_tendsto
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (a b : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        pairCost
            (harmonicFutureLevels
              (affineCount B b q : ℝ) 0
              (affineCount A a q)) /
          (affineCount B b q : ℝ) ^ 2)
      Filter.atTop
      (nhds (harmonicIntegral ((A : ℝ) / (B : ℝ)))) := by
  have hmain :=
    harmonicNormalizedProcessing_affine_tendsto
      hA hB a b
  have hcorrection :=
    harmonicPairCorrection_affine_tendsto_zero
      (A := A) hB a b
  have hadd := hmain.add hcorrection
  convert hadd using 1
  · funext q
    rw [pairCost_normalized_eq
      (affineCount_pos hA) (affineCount_pos hB)]
    simp [affineRatio]
  · simp

theorem triangular_affine_ratio_tendsto
    {P Q : ℕ} (hQ : 0 < Q) (d e : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        triangular (affineCount P d q) /
          (affineCount Q e q : ℝ) ^ 2)
      Filter.atTop
      (nhds (((P : ℝ) / (Q : ℝ)) ^ 2 / 2)) := by
  let rq : ℕ → ℝ :=
    fun q =>
      (affineCount P d q : ℝ) /
        (affineCount Q e q : ℝ)
  let qinv : ℕ → ℝ :=
    fun q => 1 / (affineCount Q e q : ℝ)
  have hr :
      Filter.Tendsto rq Filter.atTop
        (nhds ((P : ℝ) / (Q : ℝ))) := by
    simpa [rq] using
      affineCount_ratio_tendsto (P := P) hQ d e
  have hinv :
      Filter.Tendsto qinv Filter.atTop (nhds 0) := by
    simpa [qinv] using affineCount_inv_tendsto_zero hQ e
  have ht :=
    ((hr.pow 2).const_mul (1 / 2)).add
      ((hr.mul hinv).const_mul (1 / 2))
  convert ht using 1
  · funext q
    dsimp [rq, qinv]
    unfold triangular
    have hQne : (affineCount Q e q : ℝ) ≠ 0 := by
      exact_mod_cast (affineCount_pos (d := e) (q := q) hQ).ne'
    field_simp [hQne]
  · ring

theorem harmonicTriangular_affine_tendsto
    {A B : ℕ} (hB : 0 < B) (a b : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        triangular
            (affineCount A a q + affineCount B b q) /
          (affineCount B b q : ℝ) ^ 2)
      Filter.atTop
      (nhds
        ((1 + (A : ℝ) / (B : ℝ)) ^ 2 / 2)) := by
  have h :=
    triangular_affine_ratio_tendsto
      (P := A + B) hB (a + b) b
  convert h using 1
  · funext q
    congr 2
    simp only [affineCount]
    ring
  · congr 2
    have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    push_cast
    field_simp [hBne]
    ring

theorem harmonicFiniteOffline_affine_tendsto
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (a b : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        harmonicFiniteOffline
            (affineCount A a q) (affineCount B b q) 0 /
          (affineCount B b q : ℝ) ^ 2)
      Filter.atTop
      (nhds
        (harmonicLimitDenominator
          ((A : ℝ) / (B : ℝ)))) := by
  have htri :=
    harmonicTriangular_affine_tendsto
      (A := A) hB a b
  have hpair :=
    harmonicPairCost_affine_tendsto hA hB a b
  have hadd := htri.add hpair
  convert hadd using 1
  · funext q
    simp only [harmonicFiniteOffline, add_div]
  · rw [harmonicLimitDenominator_eq_integral
      (by positivity : 0 ≤ (A : ℝ) / (B : ℝ))]
    ring

theorem harmonicFutureLevels_sum_affine_tendsto
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (a b : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (harmonicFutureLevels
          (affineCount B b q : ℝ) 0
          (affineCount A a q)).sum /
            (affineCount B b q : ℝ))
      Filter.atTop
      (nhds
        ((1 + (A : ℝ) / (B : ℝ)) *
          Real.log (1 + (A : ℝ) / (B : ℝ)))) := by
  have hratio :=
    affineRatio_tendsto (A := A) hB a b
  have hriemann :=
    mixedProcessingRiemannSum_affine_tendsto
      hA hB a b
  have hadd := hratio.add hriemann
  convert hadd using 1
  · funext q
    have hK : 0 < affineCount A a q :=
      affineCount_pos hA
    have hZ : 0 < affineCount B b q :=
      affineCount_pos hB
    rw [harmonicFutureLevels_sum_div_eq hK hZ]
    rfl
  · ring

theorem harmonicFiniteAdvantage_affine_tendsto
    {A B : ℕ} (hB : 0 < B) (a b : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        harmonicFiniteAdvantage
            (affineCount A a q) (affineCount B b q) /
          (affineCount B b q : ℝ) ^ 2)
      Filter.atTop
      (nhds
        ((A : ℝ) / (B : ℝ) +
          ((A : ℝ) / (B : ℝ)) ^ 2 / 2)) := by
  let αq : ℕ → ℝ := affineRatio A B a b
  let zinv : ℕ → ℝ :=
    fun q => 1 / (affineCount B b q : ℝ)
  have hαq :
      Filter.Tendsto αq Filter.atTop
        (nhds ((A : ℝ) / (B : ℝ))) := by
    simpa [αq] using affineRatio_tendsto hB a b
  have hzinv :
      Filter.Tendsto zinv Filter.atTop (nhds 0) := by
    simpa [zinv] using affineCount_inv_tendsto_zero hB b
  have ht :=
    (hαq.add ((hαq.pow 2).const_mul (1 / 2))).sub
      ((hαq.mul hzinv).const_mul (1 / 2))
  convert ht using 1
  · funext q
    dsimp [αq, zinv, affineRatio]
    unfold harmonicFiniteAdvantage
    have hZ : (affineCount B b q : ℝ) ≠ 0 := by
      exact_mod_cast (affineCount_pos (d := b) (q := q) hB).ne'
    field_simp [hZ]
    ring
  · ring

theorem mixedFiniteOffline_affine_tendsto
    {u : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    (m a b : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        mixedFiniteOffline u
            (affineCount M m q)
            (affineCount A a q)
            (affineCount B b q) /
          (affineCount B b q : ℝ) ^ 2)
      Filter.atTop
      (nhds
        (mixedScaledOffline u
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))) := by
  let μ : ℝ := (M : ℝ) / (B : ℝ)
  let α : ℝ := (A : ℝ) / (B : ℝ)
  have hharm :=
    harmonicFiniteOffline_affine_tendsto hA hB a b
  have hCratio :=
    affineCount_ratio_tendsto (P := M) hB m b
  have hKratio :=
    affineCount_ratio_tendsto (P := A) hB a b
  have hKZratio :
      Filter.Tendsto
        (fun q =>
          ((affineCount A a q + affineCount B b q : ℕ) : ℝ) /
            (affineCount B b q : ℝ))
        Filter.atTop (nhds (1 + α)) := by
    have hone :
        Filter.Tendsto (fun _q : ℕ => (1 : ℝ))
          Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    convert hKratio.add hone using 1
    · funext q
      have hZ : (affineCount B b q : ℝ) ≠ 0 := by
        exact_mod_cast (affineCount_pos (d := b) (q := q) hB).ne'
      push_cast
      field_simp [hZ]
    · dsimp [α]
      ring
  have hprocessing :=
    harmonicFutureLevels_sum_affine_tendsto hA hB a b
  have htail := hKZratio.add hprocessing
  have hcross := hCratio.mul htail
  have htriangle :=
    (triangular_affine_ratio_tendsto
      (P := M) hB m b).const_mul u
  have hsum := (hharm.add hcross).add htriangle
  convert hsum using 1
  · funext q
    unfold mixedFiniteOffline
    have hZ : (affineCount B b q : ℝ) ≠ 0 := by
      exact_mod_cast (affineCount_pos (d := b) (q := q) hB).ne'
    field_simp [hZ]
  · unfold mixedScaledOffline
    dsimp [μ, α]
    ring

theorem mixedFiniteAdvantage_affine_tendsto
    {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    (m a b : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        (harmonicFiniteAdvantage
            (affineCount A a q)
            (affineCount B b q) +
          (affineCount M m q : ℕ) *
            (affineCount M m q +
              affineCount A a q +
              affineCount B b q : ℕ)) /
          (affineCount B b q : ℝ) ^ 2)
      Filter.atTop
      (nhds
        (mixedScaledAdvantage
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))) := by
  let μ : ℝ := (M : ℝ) / (B : ℝ)
  let α : ℝ := (A : ℝ) / (B : ℝ)
  have hharm :=
    harmonicFiniteAdvantage_affine_tendsto
      (A := A) hB a b
  have hCratio :=
    affineCount_ratio_tendsto (P := M) hB m b
  have hKratio :=
    affineCount_ratio_tendsto (P := A) hB a b
  have hZratio :
      Filter.Tendsto
        (fun _q : ℕ => (1 : ℝ))
        Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hsize := (hCratio.add hKratio).add hZratio
  have hcap := hCratio.mul hsize
  have hsum := hharm.add hcap
  convert hsum using 1
  · funext q
    have hZ : (affineCount B b q : ℝ) ≠ 0 := by
      exact_mod_cast (affineCount_pos (d := b) (q := q) hB).ne'
    push_cast
    field_simp [hZ]
  · unfold mixedScaledAdvantage
    ring

theorem mixedFiniteOnline_affine_tendsto
    {u : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    (m a b : ℕ) :
    Filter.Tendsto
      (fun q : ℕ =>
        mixedFiniteOnline u
            (affineCount M m q)
            (affineCount A a q)
            (affineCount B b q) /
          (affineCount B b q : ℝ) ^ 2)
      Filter.atTop
      (nhds
        (mixedScaledOffline u
            ((M : ℝ) / (B : ℝ))
            ((A : ℝ) / (B : ℝ)) +
          mixedScaledAdvantage
            ((M : ℝ) / (B : ℝ))
            ((A : ℝ) / (B : ℝ)))) := by
  have hoffline :=
    mixedFiniteOffline_affine_tendsto
      (u := u) hM hA hB m a b
  have hadvantage :=
    mixedFiniteAdvantage_affine_tendsto
      hM hA hB m a b
  have hsum := hoffline.add hadvantage
  convert hsum using 1
  funext q
  rw [mixedFiniteOnline_eq_offline_add_advantage,
    add_div, add_div]
  ring

theorem eventually_mixedFinite_ratio_offsets
    {u : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    {target : ℝ}
    (htarget :
      target <
        mixedScaledBenchmark u
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))
    (hu : 0 < u) (m a b : ℕ) :
    ∀ᶠ q : ℕ in Filter.atTop,
      target *
          mixedFiniteOffline u
            (affineCount M m q)
            (affineCount A a q)
            (affineCount B b q) ≤
        mixedFiniteOnline u
          (affineCount M m q)
          (affineCount A a q)
          (affineCount B b q) := by
  let μ : ℝ := (M : ℝ) / (B : ℝ)
  let α : ℝ := (A : ℝ) / (B : ℝ)
  let D : ℝ := mixedScaledOffline u μ α
  let G : ℝ := mixedScaledAdvantage μ α
  have hμ : 0 < μ := by
    dsimp [μ]
    positivity
  have hα : 0 < α := by
    dsimp [α]
    positivity
  have hD : 0 < D :=
    mixedScaledOffline_pos hu hμ.le hα
  have hoffline :=
    mixedFiniteOffline_affine_tendsto
      (u := u) hM hA hB m a b
  have honline :=
    mixedFiniteOnline_affine_tendsto
      (u := u) hM hA hB m a b
  have htargetScaled :=
    hoffline.const_mul target
  have hdiff := honline.sub htargetScaled
  have hgap : target - 1 < G / D := by
    dsimp [mixedScaledBenchmark, μ, α, D, G] at htarget ⊢
    linarith
  have hlimitPos : 0 < (D + G) - target * D := by
    have := (lt_div_iff₀ hD).mp hgap
    nlinarith
  have hevent :
      ∀ᶠ q : ℕ in Filter.atTop,
        0 <
          mixedFiniteOnline u
              (affineCount M m q)
              (affineCount A a q)
              (affineCount B b q) /
              (affineCount B b q : ℝ) ^ 2 -
            target *
              (mixedFiniteOffline u
                  (affineCount M m q)
                  (affineCount A a q)
                  (affineCount B b q) /
                (affineCount B b q : ℝ) ^ 2) :=
    hdiff (Ioi_mem_nhds hlimitPos)
  filter_upwards [hevent] with q hq
  have hden :
      0 < (affineCount B b q : ℝ) ^ 2 := by
    have hZ : 0 < (affineCount B b q : ℝ) := by
      exact_mod_cast affineCount_pos (d := b) (q := q) hB
    positivity
  have hquot :
      0 <
        (mixedFiniteOnline u
            (affineCount M m q)
            (affineCount A a q)
            (affineCount B b q) -
          target *
            mixedFiniteOffline u
              (affineCount M m q)
              (affineCount A a q)
              (affineCount B b q)) /
          (affineCount B b q : ℝ) ^ 2 := by
    convert hq using 1 <;> ring
  have hnum :
      0 <
        mixedFiniteOnline u
            (affineCount M m q)
            (affineCount A a q)
            (affineCount B b q) -
          target *
            mixedFiniteOffline u
              (affineCount M m q)
              (affineCount A a q)
              (affineCount B b q) := by
    exact (div_pos_iff.mp hquot).resolve_right
      (fun hneg => (not_lt_of_ge hden.le hneg.2))
      |>.1
  linarith

theorem eventually_mixedFinite_deferral_offsets
    {u : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    (hgap :
      0 <
        (1 + (A : ℝ) / (B : ℝ)) *
            (u - 1 - Real.log (1 + (A : ℝ) / (B : ℝ))) -
          (M : ℝ) / (B : ℝ))
    (m a b : ℕ) :
    ∀ᶠ q : ℕ in Filter.atTop,
      0 ≤
        ((affineCount A a q +
            affineCount B b q : ℕ) : ℝ) * (u - 1) -
          (harmonicFutureLevels
            (affineCount B b q : ℝ) 0
            (affineCount A a q)).sum -
          (affineCount M m q : ℕ) := by
  let μ : ℝ := (M : ℝ) / (B : ℝ)
  let α : ℝ := (A : ℝ) / (B : ℝ)
  have hKratio :=
    affineCount_ratio_tendsto (P := A) hB a b
  have hone :
      Filter.Tendsto (fun _q : ℕ => (1 : ℝ))
        Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hsize :
      Filter.Tendsto
        (fun q =>
          ((affineCount A a q +
              affineCount B b q : ℕ) : ℝ) /
            (affineCount B b q : ℝ))
        Filter.atTop (nhds (1 + α)) := by
    convert hKratio.add hone using 1
    · funext q
      have hZ : (affineCount B b q : ℝ) ≠ 0 := by
        exact_mod_cast (affineCount_pos (d := b) (q := q) hB).ne'
      push_cast
      field_simp [hZ]
    · dsimp [α]
      ring
  have hprocessing :=
    harmonicFutureLevels_sum_affine_tendsto hA hB a b
  have hcap :=
    affineCount_ratio_tendsto (P := M) hB m b
  have hlimit :=
    (hsize.const_mul (u - 1)).sub hprocessing |>.sub hcap
  have hlimitPos :
      0 <
        (1 + α) * (u - 1) -
          (1 + α) * Real.log (1 + α) - μ := by
    dsimp [μ, α] at hgap ⊢
    linarith
  have hlimitPos' :
      0 <
        (u - 1) * (1 + α) -
          (1 + (A : ℝ) / (B : ℝ)) *
            Real.log (1 + (A : ℝ) / (B : ℝ)) -
          (M : ℝ) / (B : ℝ) := by
    dsimp [α, μ] at hlimitPos ⊢
    linarith
  have hevent :
      ∀ᶠ q : ℕ in Filter.atTop,
        0 <
          (((affineCount A a q +
                affineCount B b q : ℕ) : ℝ) *
              (u - 1) -
            (harmonicFutureLevels
              (affineCount B b q : ℝ) 0
              (affineCount A a q)).sum -
            (affineCount M m q : ℕ)) /
              (affineCount B b q : ℝ) := by
    have hevent' :
        ∀ᶠ q : ℕ in Filter.atTop,
          0 <
            (u - 1) *
                (((affineCount A a q +
                    affineCount B b q : ℕ) : ℝ) /
                  (affineCount B b q : ℝ)) -
              (harmonicFutureLevels
                (affineCount B b q : ℝ) 0
                (affineCount A a q)).sum /
                  (affineCount B b q : ℝ) -
              (affineCount M m q : ℕ) /
                  (affineCount B b q : ℝ) :=
      hlimit (Ioi_mem_nhds hlimitPos')
    filter_upwards [hevent'] with q hq
    have hZ : (affineCount B b q : ℝ) ≠ 0 := by
      exact_mod_cast (affineCount_pos (d := b) (q := q) hB).ne'
    have heq :
        (((affineCount A a q +
                affineCount B b q : ℕ) : ℝ) *
              (u - 1) -
            (harmonicFutureLevels
              (affineCount B b q : ℝ) 0
              (affineCount A a q)).sum -
            (affineCount M m q : ℕ)) /
              (affineCount B b q : ℝ) =
          (u - 1) *
              (((affineCount A a q +
                  affineCount B b q : ℕ) : ℝ) /
                (affineCount B b q : ℝ)) -
            (harmonicFutureLevels
              (affineCount B b q : ℝ) 0
              (affineCount A a q)).sum /
                (affineCount B b q : ℝ) -
            (affineCount M m q : ℕ) /
                (affineCount B b q : ℝ) := by
      field_simp [hZ]
    rw [heq]
    exact hq
  filter_upwards [hevent] with q hq
  have hZ : 0 < (affineCount B b q : ℝ) := by
    exact_mod_cast affineCount_pos (d := b) (q := q) hB
  have hnum :=
    (div_pos_iff.mp hq).resolve_right
      (fun hneg => (not_lt_of_ge hZ.le hneg.2))
      |>.1
  linarith

/-- A single eventual threshold works simultaneously for every offset in
three prescribed finite ranges. -/
theorem eventually_mixedFinite_ratio_and_deferral_bounded_offsets
    {u : ℝ} {M A B : ℕ}
    (hM : 0 < M) (hA : 0 < A) (hB : 0 < B)
    {target : ℝ}
    (htarget :
      target <
        mixedScaledBenchmark u
          ((M : ℝ) / (B : ℝ))
          ((A : ℝ) / (B : ℝ)))
    (hu : 0 < u)
    (hgap :
      0 <
        (1 + (A : ℝ) / (B : ℝ)) *
            (u - 1 - Real.log (1 + (A : ℝ) / (B : ℝ))) -
          (M : ℝ) / (B : ℝ))
    (mMax aMax bMax : ℕ) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ∀ m ≤ mMax, ∀ a ≤ aMax, ∀ b ≤ bMax,
        target *
            mixedFiniteOffline u
              (affineCount M m q)
              (affineCount A a q)
              (affineCount B b q) ≤
          mixedFiniteOnline u
            (affineCount M m q)
            (affineCount A a q)
            (affineCount B b q) ∧
        0 ≤
          ((affineCount A a q +
              affineCount B b q : ℕ) : ℝ) * (u - 1) -
            (harmonicFutureLevels
              (affineCount B b q : ℝ) 0
              (affineCount A a q)).sum -
            (affineCount M m q : ℕ) := by
  have hall :
      ∀ᶠ q : ℕ in Filter.atTop,
        ∀ m : Fin (mMax + 1),
          ∀ a : Fin (aMax + 1),
            ∀ b : Fin (bMax + 1),
              target *
                  mixedFiniteOffline u
                    (affineCount M m q)
                    (affineCount A a q)
                    (affineCount B b q) ≤
                mixedFiniteOnline u
                  (affineCount M m q)
                  (affineCount A a q)
                  (affineCount B b q) ∧
              0 ≤
                ((affineCount A a q +
                    affineCount B b q : ℕ) : ℝ) * (u - 1) -
                  (harmonicFutureLevels
                    (affineCount B b q : ℝ) 0
                    (affineCount A a q)).sum -
                  (affineCount M m q : ℕ) := by
    apply Filter.eventually_all.mpr
    intro m
    apply Filter.eventually_all.mpr
    intro a
    apply Filter.eventually_all.mpr
    intro b
    exact
      (eventually_mixedFinite_ratio_offsets
        hM hA hB htarget hu m a b).and
      (eventually_mixedFinite_deferral_offsets
        hM hA hB hgap m a b)
  filter_upwards [hall] with q hq
  intro m hm a ha b hb
  let mi : Fin (mMax + 1) :=
    ⟨m, Nat.lt_succ_iff.mpr hm⟩
  let ai : Fin (aMax + 1) :=
    ⟨a, Nat.lt_succ_iff.mpr ha⟩
  let bi : Fin (bMax + 1) :=
    ⟨b, Nat.lt_succ_iff.mpr hb⟩
  simpa [mi, ai, bi] using hq mi ai bi

end LowerBound

end

end SchedulingPaper
