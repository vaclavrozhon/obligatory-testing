import SchedulingPaper.RandomizedOptionalCompletionIntegral
import SchedulingPaper.RandomizedOptionalCompletionInvariant
import SchedulingPaper.RandomizedOptionalObservedGreedyEnvelope
import Mathlib.Tactic

/-!
# Integrating observed optional-testing transcripts

This file identifies the abstract completion steps with the literal online
transcript.  It also packages the generic prefix-to-area theorem in the
notation used by the observed scheduler semantics.
-/

namespace SchedulingPaper
namespace RandomizedOptional
namespace ObservedEnvelope

open ObservedOnline
open ObservedTrace
open TraceBijection
open Randomized

noncomputable section

def observationCompletionCount {n : ℕ} (processing : Fin n → ℝ)
    (observation : Observation n) : ℕ :=
  if (observation.completionLabel processing).isSome then 1 else 0

def transcriptCompletionSteps {n : ℕ} (processing : Fin n → ℝ)
    (transcript : Transcript n) : List CompletionStep :=
  transcript.map fun observation =>
    ⟨observation.actualDuration processing,
      observationCompletionCount processing observation⟩

@[simp] theorem transcriptCompletionSteps_append {n : ℕ}
    (processing : Fin n → ℝ) (left right : Transcript n) :
    transcriptCompletionSteps processing (left ++ right) =
      transcriptCompletionSteps processing left ++
        transcriptCompletionSteps processing right := by
  simp [transcriptCompletionSteps]

@[simp] theorem completionStepsTime_transcriptCompletionSteps {n : ℕ}
    (processing : Fin n → ℝ) (transcript : Transcript n) :
    completionStepsTime (transcriptCompletionSteps processing transcript) =
      elapsed processing transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      change observation.actualDuration processing +
          completionStepsTime (transcriptCompletionSteps processing rest) =
        observation.actualDuration processing + elapsed processing rest
      rw [ih]

@[simp] theorem completionStepsCount_transcriptCompletionSteps {n : ℕ}
    (processing : Fin n → ℝ) (transcript : Transcript n) :
    completionStepsCount (transcriptCompletionSteps processing transcript) =
      completionCount processing transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      change observationCompletionCount processing observation +
          completionStepsCount (transcriptCompletionSteps processing rest) =
        (if (observation.completionLabel processing).isSome then 1 else 0) +
          completionCount processing rest
      rw [ih]
      rfl

@[simp] theorem completionStepsCost_transcriptCompletionSteps {n : ℕ}
    (processing : Fin n → ℝ) (transcript : Transcript n) :
    completionStepsCost (transcriptCompletionSteps processing transcript) =
      suffixWeightedDuration processing transcript := by
  induction transcript with
  | nil => rfl
  | cons observation rest ih =>
      change observation.actualDuration processing *
            completionStepsCount
              (transcriptCompletionSteps processing (observation :: rest)) +
          completionStepsCost (transcriptCompletionSteps processing rest) =
        observation.actualDuration processing *
            completionCount processing (observation :: rest) +
          suffixWeightedDuration processing rest
      rw [completionStepsCount_transcriptCompletionSteps, ih]

private theorem blind_reveal_mem_of_observation_mem {n : ℕ}
    {job : Fin n} {value : ℝ} {transcript : Transcript n}
    (hmem : Observation.blindCompleted job value ∈ transcript) :
    (job, value) ∈ transcript.revealedResults := by
  induction transcript with
  | nil => simp at hmem
  | cons observation rest ih =>
      cases observation with
      | testResult headJob headValue =>
          simp only [List.mem_cons] at hmem
          simp only [Transcript.revealedResults, List.mem_cons]
          exact hmem.elim (by simp) (fun h => Or.inr (ih h))
      | processed headJob =>
          simp only [List.mem_cons] at hmem
          simp only [Transcript.revealedResults]
          exact hmem.elim (by simp) ih
      | blindCompleted headJob headValue =>
          simp only [List.mem_cons] at hmem
          simp only [Transcript.revealedResults, List.mem_cons]
          exact hmem.elim (fun h => Or.inl (by simpa using h))
            (fun h => Or.inr (ih h))

theorem transcriptCompletionSteps_duration_nonneg {n : ℕ}
    {processing : Fin n → ℝ} {transcript : Transcript n}
    (hprocessing : ∀ job, 0 ≤ processing job)
    (hmatch : AllRevealsMatch processing transcript) :
    ∀ step ∈ transcriptCompletionSteps processing transcript,
      0 ≤ step.duration := by
  intro step hstep
  obtain ⟨observation, hmem, rfl⟩ := List.mem_map.mp hstep
  cases observation with
  | testResult job value =>
      simp [Observation.actualDuration]
  | processed job =>
      simpa [Observation.actualDuration] using hprocessing job
  | blindCompleted job value =>
      have hvalue : value = processing job :=
        hmatch job value (blind_reveal_mem_of_observation_mem hmem)
      simpa [Observation.actualDuration, hvalue] using hprocessing job

theorem completionCost_nonneg_of_revealsMatch {n : ℕ}
    {processing : Fin n → ℝ} {transcript : Transcript n}
    (hprocessing : ∀ job, 0 ≤ processing job)
    (hmatch : AllRevealsMatch processing transcript) :
    0 ≤ completionCost processing transcript := by
  rw [completionCost_eq_suffixWeightedDuration]
  rw [← completionStepsCost_transcriptCompletionSteps]
  exact completionStepsCost_nonneg
    (transcriptCompletionSteps_duration_nonneg hprocessing hmatch)

/-- If every literal transcript prefix is dominated by a continuous
monotone completion envelope, then the normalized sum of completion times is
at least the corresponding shifted remaining-mass integral. -/
theorem transcriptCost_ge_remaining_integral
    {n : ℕ} (hn : 0 < n) {processing : Fin n → ℝ}
    (transcript : Transcript n) (curve : ℝ → ℝ)
    (hcurveContinuous : Continuous curve) (hcurveMono : Monotone curve)
    (ζ ε : ℝ)
    (hprocessing : ∀ job, 0 ≤ processing job)
    (hmatch : AllRevealsMatch processing transcript)
    (hcomplete : completionCount processing transcript = n)
    (hprefix : ∀ pre, pre <+: transcript →
      (completionCount processing pre : ℝ) / n ≤
        curve (elapsed processing pre / n + ζ) + ε) :
    (∫ x in 0..elapsed processing transcript / n,
        (1 - curve (x + ζ) - ε)) ≤
      completionCost processing transcript / (n : ℝ) ^ 2 := by
  rw [completionCost_eq_suffixWeightedDuration]
  let steps := transcriptCompletionSteps processing transcript
  have hstepsDuration : ∀ step ∈ steps, 0 ≤ step.duration := by
    simpa [steps] using
      transcriptCompletionSteps_duration_nonneg hprocessing hmatch
  have hstepsComplete : completionStepsCount steps = n := by
    simpa [steps] using hcomplete
  have hstepsPrefix : ∀ pre, pre <+: steps →
      (completionStepsCount pre : ℝ) / n ≤
        curve (completionStepsTime pre / n + ζ) + ε := by
    intro pre hpre
    rcases List.prefix_map_iff.mp (by simpa [steps, transcriptCompletionSteps]
      using hpre) with ⟨source, hsource, rfl⟩
    change (completionStepsCount
        (transcriptCompletionSteps processing source) : ℝ) / n ≤
      curve (completionStepsTime
        (transcriptCompletionSteps processing source) / n + ζ) + ε
    rw [completionStepsCount_transcriptCompletionSteps,
      completionStepsTime_transcriptCompletionSteps]
    exact hprefix source hsource
  simpa [steps] using completionStepsCost_ge_remaining_integral hn curve
    hcurveContinuous hcurveMono ζ ε steps hstepsDuration hstepsComplete
      hstepsPrefix

/-- On one simultaneous urn-good placement, every literal prefix of the
settled adaptive run lies below the same sorted fluid completion envelope.
The realized test fraction is the full-trace predictable-selector sum; no
conditioning on that random fraction occurs. -/
theorem settled_prefix_completion_le_sortedEnvelope
    {n : ℕ} (hn : 0 < n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : Fin n → ℝ) (policy : CompletePolicy p)
    (σ : ObservedTrace.Placement n)
    (G : ExactPositiveGrid ι p) (selected : ι → Bool)
    {γ zeroMass τ μ blindError : ℝ} {mass : ι → ℝ}
    (hmassDef : ∀ i, mass i = populationMean
      (fun occurrence => if G.category i (p occurrence) then 1 else 0))
    (hzeroMassDef : zeroMass = populationMean
      (fun occurrence => if zeroCategory (p occurrence) then 1 else 0))
    (hμDef : μ = populationMean p)
    (hγ : 0 ≤ γ) (hblindError : 0 ≤ blindError)
    (hτ : 0 < τ) (hμ : 0 < μ) (hprice : ∀ i, 0 < G.price i)
    (hpopulationMass : zeroMass + ∑ i, mass i = 1)
    (hmeanPartition :
      (∑ i, G.price i * selectedPart selected mass i) +
        ∑ i, G.price i * residualPart selected mass i = μ)
    (hclassGood : ∀ cutoff i,
      |(∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if G.category i
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        mass i *
          ∑ k ∈ positionsThrough cutoff,
            compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ γ * n)
    (hzeroGood : ∀ cutoff,
      |(∑ k ∈ positionsThrough cutoff,
          compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            (if zeroCategory
              (p (revealOrder (touchTrace p policy) σ k)) then 1 else 0)) -
        zeroMass *
          ∑ k ∈ positionsThrough cutoff,
            compiledTestSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ γ * n)
    (hblindGood : ∀ cutoff,
      |(∑ k ∈ positionsThrough cutoff,
          compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ) *
            p (revealOrder (touchTrace p policy) σ k)) -
        μ *
          ∑ k ∈ positionsThrough cutoff,
            compiledBlindSelector p policy k
              (revealOrder (touchTrace p policy) σ)| ≤ blindError * n)
    (hmax : ∀ x : ι → ℝ,
      (∀ i, 0 ≤ x i) → (∀ i, x i ≤ mass i) →
      τ * RandomizedAnnounced.discoveryMass zeroMass x ≤
        RandomizedAnnounced.discoveryWork G.price x)
    (hmodulePositive :
      0 < RandomizedAnnounced.discoveryMass zeroMass
        (selectedPart selected mass))
    (hmoduleDensity :
      τ * RandomizedAnnounced.discoveryMass zeroMass
          (selectedPart selected mass) =
        RandomizedAnnounced.discoveryWork G.price
          (selectedPart selected mass))
    (pre : Transcript n)
    (hpre : pre <+:
      (settledRun p policy.strategy σ).config.transcript) :
    let q := (∑ k, compiledTestSelector p policy k
      (revealOrder (touchTrace p policy) σ)) / n
    let a := RandomizedAnnounced.discoveryMass zeroMass
      (selectedPart selected mass)
    let residualMass := residualPart selected mass
    (completionCount (placedProcessing p σ) pre : ℝ) / n ≤
      fluidBlocksCompleted
          (optionalSortedBlocks q a τ μ G.price residualMass)
          (elapsed (placedProcessing p σ) pre / n + blindError) +
        (Fintype.card ι + 1) * γ := by
  dsimp
  let full := (settledRun p policy.strategy σ).config.transcript
  let fuel := pre.length
  let reveal := revealOrder (touchTrace p policy) σ
  let q : ℝ := (∑ k, compiledTestSelector p policy k reveal) / n
  let a := RandomizedAnnounced.discoveryMass zeroMass
    (selectedPart selected mass)
  let residualMass := residualPart selected mass
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpreLength : pre.length ≤ full.length := hpre.length_le
  have hfullLength : full.length ≤ 2 * n + 1 := by
    dsimp [full, settledRun]
    rw [run_transcript_eq_runWord]
    exact runWord_length_le_fuel _ _ _ _
  have hfuel : fuel ≤ 2 * n + 1 := hpreLength.trans hfullLength
  have hrunTake := run_transcript_eq_take_of_le_length
    (placedProcessing p σ) policy.strategy hfuel hpreLength
  have hpreTake : pre = full.take pre.length := list_eq_take_of_prefix hpre
  have hrunPre :
      (run (placedProcessing p σ) policy.strategy fuel).config.transcript = pre := by
    simpa [fuel, full] using hrunTake.trans hpreTake.symm
  let touches := (touchChoices pre).length
  have htouchesLe : touches ≤ n := by
    have hprefChoices := touchChoices_prefix hpre
    have hlength := hprefChoices.length_le
    have hfullChoices :
        (touchChoices full).length = n := by
      have hchoices := touchTrace_choices_ofFn p policy σ
      dsimp [full]
      rw [← hchoices]
      simp
    simpa [touches, full, hfullChoices] using hlength
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg (Finset.sum_nonneg fun k _ =>
      compiledTestSelector_nonneg p policy k reveal) hnR.le
  have hsumTestLe : (∑ k, compiledTestSelector p policy k reveal) ≤ n := by
    calc
      (∑ k, compiledTestSelector p policy k reveal) ≤
          ∑ _k : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ =>
          compiledTestSelector_le_one p policy k reveal
      _ = n := by simp
  have hq1 : q ≤ 1 := by
    dsimp [q]
    rw [div_le_one hnR]
    exact hsumTestLe
  have hmass0 : ∀ i, 0 ≤ mass i := by
    intro i
    rw [hmassDef i]
    exact (populationMean_mem_Icc hn
      (fun occurrence => if G.category i (p occurrence) then 1 else 0)
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])
      (fun occurrence => by
        by_cases h : G.category i (p occurrence) = true <;> simp [h])).1
  have hresidual0 : ∀ i, 0 ≤ residualMass i := residualPart_nonneg hmass0
  have ha0 : 0 ≤ a := hmodulePositive.le
  by_cases htouches : touches = 0
  · have hcountLe := run_completionCount_le_startedLabels_length
      (placedProcessing p σ) policy.strategy fuel
    rw [hrunPre] at hcountLe
    have hstartedLength : pre.startedLabels.length = touches := by
      rw [← touchChoices_map_fst]
      simp [touches]
    have hcountZero : completionCount (placedProcessing p σ) pre = 0 := by
      rw [hstartedLength, htouches] at hcountLe
      omega
    have hcurve0 := fluidBlocksCompleted_nonneg
      (optionalSortedBlocks_mass_nonneg
        (q := q) (a := a) (τ := τ) (μ := μ)
        (p := G.price) (residualMass := residualMass)
        hq0 hq1 ha0 hresidual0)
      (elapsed (placedProcessing p σ) pre / n + blindError)
    have hslack0 : 0 ≤ (Fintype.card ι + 1 : ℝ) * γ := by positivity
    rw [hcountZero]
    norm_num
    linarith
  · let cutoff : Fin n := ⟨touches - 1, by omega⟩
    have hlength :
        (touchChoices
          (run (placedProcessing p σ) policy.strategy fuel).config.transcript).length =
            cutoff.val + 1 := by
      rw [hrunPre]
      dsimp [cutoff, touches]
      omega
    have hcompletionLeOne :
        (completionCount (placedProcessing p σ)
          (run (placedProcessing p σ) policy.strategy fuel).config.transcript : ℝ) /
            n ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast run_completionCount_le_n
        (placedProcessing p σ) policy.strategy fuel
    have hopen := operational_prefix_completion_le_sortedEnvelope
      hn p policy σ G hfuel cutoff hlength selected
      hmassDef hzeroMassDef hμDef hγ hblindError hτ hμ hprice
      hpopulationMass hmeanPartition (hclassGood cutoff) (hzeroGood cutoff)
      (hblindGood cutoff) hmax hmodulePositive hmoduleDensity hcompletionLeOne
    simpa [hrunPre, q, a, residualMass, reveal] using hopen

end

end ObservedEnvelope
end RandomizedOptional
end SchedulingPaper
