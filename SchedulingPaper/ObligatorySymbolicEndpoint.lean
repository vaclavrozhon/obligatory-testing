import SchedulingPaper.ObligatoryEndpointReduction

/-!
# From a symbolic AdaptiveThreshold path to a boundary word

A genuine obligatory run has three symbolic classes: a zero, a positive job
processed immediately, and a positive job deferred to the final tail.  The
fourth formal bank letter `epsilon` appears only after an immediate
coordinate is moved to its one-sided zero endpoint.

This file proves that the endpoint vertex supplied by
`ObligatoryEndpointReduction` is literally represented by a four-letter
boundary word.  In particular its fixed-word excess is exactly the already
bounded `obligatoryBoundaryExcess`.
-/

namespace SchedulingPaper

noncomputable section

inductive ObligatoryRuntimeClass
  | zero
  | immediate
  | deferred
  deriving DecidableEq, Repr

def ObligatoryRuntimeClass.outcome : ObligatoryRuntimeClass → BoundaryOutcome
  | .zero => .zero
  | .immediate => .immediate
  | .deferred => .deferred

def obligatorySymbolicThresholds :
    AnalysisState → List ObligatoryRuntimeClass → List ℝ
  | _, [] => []
  | s, symbol :: symbols =>
      s.threshold ::
        obligatorySymbolicThresholds
          (s.step symbol.outcome) symbols

@[simp] theorem obligatorySymbolicThresholds_length
    (s : AnalysisState) (symbols : List ObligatoryRuntimeClass) :
    (obligatorySymbolicThresholds s symbols).length = symbols.length := by
  induction symbols generalizing s with
  | nil => rfl
  | cons symbol symbols ih =>
      simp [obligatorySymbolicThresholds, ih]

def obligatorySymbolOutcomeFn
    (symbols : List ObligatoryRuntimeClass) :
    Fin symbols.length → BoundaryOutcome :=
  fun i => (symbols.get i).outcome

def obligatorySymbolThresholdFn
    (s : AnalysisState) (symbols : List ObligatoryRuntimeClass) :
    Fin symbols.length → ℝ :=
  fun i =>
    (obligatorySymbolicThresholds s symbols).get
      ⟨i, by simpa using i.isLt⟩

/-- States are equivalent for the threshold policy when they have the same
countdown, deferred count, and total number of symbolic positive outcomes.
The latter may be split differently between substantive and epsilon
coordinates. -/
def AnalysisState.SymbolicallyEquivalent
    (left right : AnalysisState) : Prop :=
  left.x = right.x ∧
    left.deferred = right.deferred ∧
    left.substantive + left.epsilon =
      right.substantive + right.epsilon

theorem AnalysisState.SymbolicallyEquivalent.refl
    (s : AnalysisState) :
    s.SymbolicallyEquivalent s :=
  ⟨rfl, rfl, rfl⟩

theorem AnalysisState.SymbolicallyEquivalent.y_eq
    {left right : AnalysisState}
    (h : left.SymbolicallyEquivalent right) :
    left.y = right.y := by
  rcases h with ⟨hx, hd, hpositive⟩
  have hform (s : AnalysisState) :
      s.y =
        (s.deferred -
          RStar * (s.substantive + s.epsilon)) / s.x := by
    unfold AnalysisState.y AnalysisState.eta AnalysisState.b
    ring
  rw [hform left, hform right, hx, hd, hpositive]

theorem AnalysisState.SymbolicallyEquivalent.threshold_eq
    {left right : AnalysisState}
    (h : left.SymbolicallyEquivalent right) :
    left.threshold = right.threshold := by
  unfold AnalysisState.threshold
  rw [h.y_eq]

/-- The formal endpoint chosen for one runtime class. -/
def endpointOutcome
    (symbol : ObligatoryRuntimeClass) (value : ℝ) : BoundaryOutcome :=
  match symbol with
  | .zero => .zero
  | .immediate => if value = 0 then .epsilon else .immediate
  | .deferred => .deferred

/-- Coordinate choices at the live endpoints of a symbolic path. -/
def ObligatoryEndpointChoices :
    AnalysisState → List ObligatoryRuntimeClass → List ℝ → Prop
  | _, [], values => values = []
  | _, _ :: _, [] => False
  | s, symbol :: symbols, value :: values =>
      (match symbol with
      | .zero => value = 0
      | .immediate => value = 0 ∨ value = s.threshold
      | .deferred => value = s.threshold) ∧
      ObligatoryEndpointChoices
        (s.step symbol.outcome) symbols values

theorem ObligatoryEndpointChoices.length_eq
    {s : AnalysisState} {symbols : List ObligatoryRuntimeClass}
    {values : List ℝ}
    (h : ObligatoryEndpointChoices s symbols values) :
    values.length = symbols.length := by
  induction symbols generalizing s values with
  | nil =>
      simp [ObligatoryEndpointChoices] at h
      simp [h]
  | cons symbol symbols ih =>
      cases values with
      | nil =>
          simp [ObligatoryEndpointChoices] at h
      | cons value values =>
          simp only [ObligatoryEndpointChoices] at h
          simp [ih h.2]

def obligatoryEndpointWord :
    List ObligatoryRuntimeClass → List ℝ → List BoundaryOutcome
  | [], _ => []
  | _, [] => []
  | symbol :: symbols, value :: values =>
      endpointOutcome symbol value ::
        obligatoryEndpointWord symbols values

@[simp] theorem obligatoryEndpointWord_length
    {s : AnalysisState} {symbols : List ObligatoryRuntimeClass}
    {values : List ℝ}
    (h : ObligatoryEndpointChoices s symbols values) :
    (obligatoryEndpointWord symbols values).length =
      symbols.length := by
  induction symbols generalizing s values with
  | nil =>
      simp [obligatoryEndpointWord]
  | cons symbol symbols ih =>
      cases values with
      | nil =>
          simp [ObligatoryEndpointChoices] at h
      | cons value values =>
          simp only [ObligatoryEndpointChoices] at h
          simp [obligatoryEndpointWord, ih h.2]

theorem symbolicallyEquivalent_step_endpoint
    {s t : AnalysisState} (heq : s.SymbolicallyEquivalent t)
    {symbol : ObligatoryRuntimeClass} {value : ℝ}
    (hchoice :
      match symbol with
      | .zero => value = 0
      | .immediate => value = 0 ∨ value = s.threshold
      | .deferred => value = s.threshold) :
    (s.step symbol.outcome).SymbolicallyEquivalent
      (t.step (endpointOutcome symbol value)) := by
  rcases heq with ⟨hx, hd, hpositive⟩
  cases symbol with
  | zero =>
      simp [ObligatoryRuntimeClass.outcome, endpointOutcome,
        AnalysisState.SymbolicallyEquivalent, AnalysisState.step,
        hx, hd, hpositive]
  | deferred =>
      simp [ObligatoryRuntimeClass.outcome, endpointOutcome,
        AnalysisState.SymbolicallyEquivalent, AnalysisState.step,
        hx, hd]
      linarith
  | immediate =>
      rcases hchoice with hzero | hthreshold
      · simp [ObligatoryRuntimeClass.outcome, endpointOutcome,
          AnalysisState.SymbolicallyEquivalent, AnalysisState.step,
          hzero, hx, hd] at hpositive ⊢
        linarith
      · by_cases hvalue : value = 0
        · simp [ObligatoryRuntimeClass.outcome, endpointOutcome,
            AnalysisState.SymbolicallyEquivalent, AnalysisState.step,
            hvalue, hx, hd] at hpositive ⊢
          linarith
        · simp [ObligatoryRuntimeClass.outcome, endpointOutcome,
            AnalysisState.SymbolicallyEquivalent, AnalysisState.step,
            hvalue, hx, hd]
          linarith

def endpointJobs :
    List ObligatoryRuntimeClass → List ℝ → List ObligatoryBoundaryJob
  | [], _ => []
  | _, [] => []
  | symbol :: symbols, value :: values =>
      ⟨endpointOutcome symbol value, value⟩ ::
        endpointJobs symbols values

def symbolicJobs :
    List ObligatoryRuntimeClass → List ℝ → List ObligatoryBoundaryJob
  | [], _ => []
  | _, [] => []
  | symbol :: symbols, value :: values =>
      ⟨symbol.outcome, value⟩ ::
        symbolicJobs symbols values

/-- Evaluating the endpoint word at the evolving formal thresholds produces
exactly the selected endpoint processing vector. -/
theorem obligatoryBoundaryJobs_endpointWord
    {s t : AnalysisState} (heq : s.SymbolicallyEquivalent t)
    {symbols : List ObligatoryRuntimeClass} {values : List ℝ}
    (hchoices : ObligatoryEndpointChoices s symbols values) :
    obligatoryBoundaryJobs t
        (obligatoryEndpointWord symbols values) =
      endpointJobs symbols values := by
  induction symbols generalizing s t values with
  | nil =>
      simp [obligatoryEndpointWord, endpointJobs,
        obligatoryBoundaryJobs]
  | cons symbol symbols ih =>
      cases values with
      | nil =>
          simp [ObligatoryEndpointChoices] at hchoices
      | cons value values =>
          rcases hchoices with ⟨hhead, htail⟩
          have hthreshold := heq.threshold_eq
          have hnext :=
            symbolicallyEquivalent_step_endpoint heq hhead
          cases symbol with
          | zero =>
              change value = 0 at hhead
              subst value
              simpa [obligatoryEndpointWord, endpointJobs,
                endpointOutcome, obligatoryBoundaryValue] using
                congrArg
                  (fun tail =>
                    ObligatoryBoundaryJob.mk .zero 0 :: tail)
                  (ih hnext htail)
          | deferred =>
              change value = s.threshold at hhead
              have hvalueT : value = t.threshold := by
                rw [hhead, hthreshold]
              simpa [obligatoryEndpointWord, endpointJobs,
                endpointOutcome, obligatoryBoundaryValue,
                hvalueT] using
                  congrArg
                    (fun tail =>
                      ObligatoryBoundaryJob.mk .deferred value :: tail)
                    (ih hnext htail)
          | immediate =>
              by_cases hzero : value = 0
              · subst value
                simpa [obligatoryEndpointWord, endpointJobs,
                  endpointOutcome, obligatoryBoundaryValue] using
                    congrArg
                      (fun tail =>
                        ObligatoryBoundaryJob.mk .epsilon 0 :: tail)
                      (ih hnext htail)
              · have hvalue : value = s.threshold := by
                  rcases hhead with h | h
                  · exact (hzero h).elim
                  · exact h
                have hvalueT : value = t.threshold := by
                  rw [hvalue, hthreshold]
                have htzero : t.threshold ≠ 0 := by
                  intro ht
                  apply hzero
                  rw [hvalueT, ht]
                simpa [obligatoryEndpointWord, endpointJobs,
                  endpointOutcome, obligatoryBoundaryValue, hzero,
                  hvalueT, htzero] using
                    congrArg
                      (fun tail =>
                        ObligatoryBoundaryJob.mk .immediate value :: tail)
                      (ih hnext htail)

theorem endpointOutcome_deferred_iff
    (symbol : ObligatoryRuntimeClass) (value : ℝ) :
    endpointOutcome symbol value = .deferred ↔
      symbol.outcome = .deferred := by
  cases symbol <;>
    simp [endpointOutcome, ObligatoryRuntimeClass.outcome] <;>
    split_ifs <;> simp

theorem endpointOutcome_pairCharge
    (left right : ObligatoryRuntimeClass)
    (p q : ℝ) :
    obligatoryALGPairCharge
        ⟨endpointOutcome left p, p⟩
        ⟨endpointOutcome right q, q⟩ =
      obligatoryALGPairCharge
        ⟨left.outcome, p⟩ ⟨right.outcome, q⟩ := by
  cases left <;> cases right <;>
    simp [endpointOutcome, ObligatoryRuntimeClass.outcome,
      obligatoryALGPairCharge] <;>
    split_ifs <;> rfl

private theorem endpointJobs_algPair_map
    (left : ObligatoryRuntimeClass) (p : ℝ) :
    ∀ symbols values,
      (endpointJobs symbols values).map
          (obligatoryALGPairCharge
            ⟨endpointOutcome left p, p⟩) =
        (symbolicJobs symbols values).map
          (obligatoryALGPairCharge
            ⟨left.outcome, p⟩) := by
  intro symbols
  induction symbols with
  | nil =>
      intro values
      simp [endpointJobs, symbolicJobs]
  | cons right symbols ih =>
      intro values
      cases values with
      | nil =>
          simp [endpointJobs, symbolicJobs]
      | cons q values =>
          simp only [endpointJobs, symbolicJobs, List.map_cons]
          rw [endpointOutcome_pairCharge, ih values]

theorem endpointJobs_alg_eq_symbolicJobs :
    ∀ symbols values,
      obligatoryALGPairObjective (endpointJobs symbols values) =
        obligatoryALGPairObjective (symbolicJobs symbols values) := by
  intro symbols
  induction symbols with
  | nil =>
      intro values
      simp [endpointJobs, symbolicJobs, obligatoryALGPairObjective]
  | cons symbol symbols ih =>
      intro values
      cases values with
      | nil =>
          simp [endpointJobs, symbolicJobs, obligatoryALGPairObjective]
      | cons value values =>
          simp only [endpointJobs, symbolicJobs,
            obligatoryALGPairObjective]
          rw [ih values]
          rw [endpointJobs_algPair_map]

private theorem endpointJobs_optPair_map
    (left : ObligatoryRuntimeClass) (p : ℝ) :
    ∀ symbols values,
      (endpointJobs symbols values).map
          (obligatoryOPTPairCharge
            ⟨endpointOutcome left p, p⟩) =
        (symbolicJobs symbols values).map
          (obligatoryOPTPairCharge
            ⟨left.outcome, p⟩) := by
  intro symbols
  induction symbols with
  | nil =>
      intro values
      simp [endpointJobs, symbolicJobs]
  | cons right symbols ih =>
      intro values
      cases values with
      | nil =>
          simp [endpointJobs, symbolicJobs]
      | cons q values =>
          simp only [endpointJobs, symbolicJobs, List.map_cons]
          simp only [obligatoryOPTPairCharge]
          rw [ih values]

theorem endpointJobs_opt_eq_symbolicJobs :
    ∀ symbols values,
      obligatoryOPTPairObjective (endpointJobs symbols values) =
        obligatoryOPTPairObjective (symbolicJobs symbols values) := by
  intro symbols
  induction symbols with
  | nil =>
      intro values
      simp [endpointJobs, symbolicJobs, obligatoryOPTPairObjective]
  | cons symbol symbols ih =>
      intro values
      cases values with
      | nil =>
          simp [endpointJobs, symbolicJobs, obligatoryOPTPairObjective]
      | cons value values =>
          simp only [endpointJobs, symbolicJobs,
            obligatoryOPTPairObjective]
          rw [ih values]
          rw [endpointJobs_optPair_map]

/-! ## Packaging a complete symbolic endpoint reduction -/

theorem obligatorySymbolicThresholds_nonneg
    {s : AnalysisState} {symbols : List ObligatoryRuntimeClass}
    (hmatch :
      BoundaryStateMatches s (symbols.map
        ObligatoryRuntimeClass.outcome)) :
    ∀ a ∈ obligatorySymbolicThresholds s symbols, 0 ≤ a := by
  induction symbols generalizing s with
  | nil =>
      simp [obligatorySymbolicThresholds]
  | cons symbol symbols ih =>
      have hs := hmatch.feasible_of_cons
      have hthreshold :
          0 ≤ s.threshold :=
        (AnalysisState.threshold_ge_one hs).trans' zero_le_one
      intro a ha
      simp only [obligatorySymbolicThresholds,
        List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hthreshold
      · exact ih hmatch.step a ha

theorem obligatorySymbolThresholdFn_nonneg
    (symbols : List ObligatoryRuntimeClass) :
    ∀ i,
      0 ≤ obligatorySymbolThresholdFn
        (initialAnalysisState symbols.length) symbols i := by
  intro i
  apply obligatorySymbolicThresholds_nonneg
    (s := initialAnalysisState symbols.length)
    (symbols := symbols)
  · simpa using
      boundaryStateMatches_initial
        (symbols.map ObligatoryRuntimeClass.outcome)
  · exact List.get_mem _ _

private theorem endpointChoices_of_get
    {s : AnalysisState} {symbols : List ObligatoryRuntimeClass}
    {values : List ℝ}
    (hlength : values.length = symbols.length)
    (hget :
      ∀ i : Fin symbols.length,
        match symbols.get i with
        | .zero => values.get ⟨i, by simpa [hlength] using i.isLt⟩ = 0
        | .immediate =>
            values.get ⟨i, by simpa [hlength] using i.isLt⟩ = 0 ∨
            values.get ⟨i, by simpa [hlength] using i.isLt⟩ =
              obligatorySymbolThresholdFn s symbols i
        | .deferred =>
            values.get ⟨i, by simpa [hlength] using i.isLt⟩ =
              obligatorySymbolThresholdFn s symbols i) :
    ObligatoryEndpointChoices s symbols values := by
  induction symbols generalizing s values with
  | nil =>
      have : values = [] := List.eq_nil_of_length_eq_zero (by simpa using hlength)
      simpa [this, ObligatoryEndpointChoices]
  | cons symbol symbols ih =>
      cases values with
      | nil =>
          simp at hlength
      | cons value values =>
          have htailLength : values.length = symbols.length := by
            simpa using hlength
          have hheadRaw := hget (0 : Fin (symbol :: symbols).length)
          have htailGet :
              ∀ i : Fin symbols.length,
                match symbols.get i with
                | .zero =>
                    values.get
                      ⟨i, by simpa [htailLength] using i.isLt⟩ = 0
                | .immediate =>
                    values.get
                        ⟨i, by simpa [htailLength] using i.isLt⟩ = 0 ∨
                    values.get
                        ⟨i, by simpa [htailLength] using i.isLt⟩ =
                      obligatorySymbolThresholdFn
                        (s.step symbol.outcome) symbols i
                | .deferred =>
                    values.get
                        ⟨i, by simpa [htailLength] using i.isLt⟩ =
                      obligatorySymbolThresholdFn
                        (s.step symbol.outcome) symbols i := by
            intro i
            have htailRaw :=
              hget (Fin.succ i :
                Fin (symbol :: symbols).length)
            simpa [obligatorySymbolThresholdFn,
              obligatorySymbolicThresholds] using htailRaw
          have htail := ih htailLength htailGet
          cases symbol with
          | zero =>
              have hhead : value = 0 := by
                simpa [obligatorySymbolThresholdFn,
                  obligatorySymbolicThresholds] using hheadRaw
              exact ⟨hhead, htail⟩
          | immediate =>
              have hhead : value = 0 ∨ value = s.threshold := by
                simpa [obligatorySymbolThresholdFn,
                  obligatorySymbolicThresholds] using hheadRaw
              exact ⟨hhead, htail⟩
          | deferred =>
              have hhead : value = s.threshold := by
                simpa [obligatorySymbolThresholdFn,
                  obligatorySymbolicThresholds] using hheadRaw
              exact ⟨hhead, htail⟩

private theorem symbolicJobs_ofFn :
    ∀ (symbols : List ObligatoryRuntimeClass)
      (processing : Fin symbols.length → ℝ),
      symbolicJobs symbols (List.ofFn processing) =
        obligatoryJobsOfFunctions
          (obligatorySymbolOutcomeFn symbols) processing := by
  intro symbols
  induction symbols with
  | nil =>
      intro processing
      simp [symbolicJobs, obligatoryJobsOfFunctions]
  | cons symbol symbols ih =>
      intro processing
      let tailProcessing : Fin symbols.length → ℝ :=
        fun i => processing i.succ
      have htail := ih tailProcessing
      rw [show List.ofFn processing =
          processing 0 :: List.ofFn tailProcessing by
        simpa [tailProcessing] using
          (List.ofFn_succ processing)]
      rw [show obligatoryJobsOfFunctions
            (obligatorySymbolOutcomeFn (symbol :: symbols))
            processing =
          ⟨symbol.outcome, processing 0⟩ ::
            obligatoryJobsOfFunctions
              (obligatorySymbolOutcomeFn symbols)
              tailProcessing by
        simp [obligatoryJobsOfFunctions,
          obligatorySymbolOutcomeFn, tailProcessing,
          List.ofFn_succ]]
      simp [symbolicJobs, htail]

/-- A fixed genuine symbolic decision path is dominated by a literal
four-letter boundary word.  This is the complete endpoint-extremalization
step, including the unbounded deferred intervals and one-sided epsilon
vertices. -/
theorem exists_obligatoryBoundaryWord_ge_symbolic
    (symbols : List ObligatoryRuntimeClass)
    (processing : Fin symbols.length → ℝ)
    (hzero :
      ∀ i, symbols.get i = .zero → processing i = 0)
    (himmediate :
      ∀ i, symbols.get i = .immediate →
        0 ≤ processing i ∧
          processing i ≤
            obligatorySymbolThresholdFn
              (initialAnalysisState symbols.length) symbols i)
    (hdeferred :
      ∀ i, symbols.get i = .deferred →
        obligatorySymbolThresholdFn
            (initialAnalysisState symbols.length) symbols i ≤
          processing i) :
    ∃ outcomes : List BoundaryOutcome,
      outcomes.length = symbols.length ∧
      obligatoryFixedWordExcess
          (obligatorySymbolOutcomeFn symbols) processing ≤
        obligatoryBoundaryExcess outcomes := by
  let threshold :=
    obligatorySymbolThresholdFn
      (initialAnalysisState symbols.length) symbols
  let outcome := obligatorySymbolOutcomeFn symbols
  have hthreshold : ∀ i, 0 ≤ threshold i := by
    intro i
    exact obligatorySymbolThresholdFn_nonneg symbols i
  have hzero' :
      ∀ i, outcome i = .zero ∨ outcome i = .epsilon →
        processing i = 0 := by
    intro i hi
    cases hs : symbols.get i with
    | zero =>
        exact hzero i hs
    | immediate =>
        have hout : outcome i = .immediate := by
          have h :=
            congrArg ObligatoryRuntimeClass.outcome hs
          simpa [outcome, obligatorySymbolOutcomeFn,
            ObligatoryRuntimeClass.outcome] using h
        rw [hout] at hi
        simp at hi
    | deferred =>
        have hout : outcome i = .deferred := by
          have h :=
            congrArg ObligatoryRuntimeClass.outcome hs
          simpa [outcome, obligatorySymbolOutcomeFn,
            ObligatoryRuntimeClass.outcome] using h
        rw [hout] at hi
        simp at hi
  have himmediate' :
      ∀ i, outcome i = .immediate →
        0 ≤ processing i ∧ processing i ≤ threshold i := by
    intro i hi
    cases hs : symbols.get i with
    | zero =>
        have hout : outcome i = .zero := by
          have h :=
            congrArg ObligatoryRuntimeClass.outcome hs
          simpa [outcome, obligatorySymbolOutcomeFn,
            ObligatoryRuntimeClass.outcome] using h
        rw [hout] at hi
        contradiction
    | immediate =>
        exact himmediate i hs
    | deferred =>
        have hout : outcome i = .deferred := by
          have h :=
            congrArg ObligatoryRuntimeClass.outcome hs
          simpa [outcome, obligatorySymbolOutcomeFn,
            ObligatoryRuntimeClass.outcome] using h
        rw [hout] at hi
        contradiction
  have hdeferred' :
      ∀ i, outcome i = .deferred →
        threshold i ≤ processing i := by
    intro i hi
    cases hs : symbols.get i with
    | zero =>
        have hout : outcome i = .zero := by
          have h :=
            congrArg ObligatoryRuntimeClass.outcome hs
          simpa [outcome, obligatorySymbolOutcomeFn,
            ObligatoryRuntimeClass.outcome] using h
        rw [hout] at hi
        contradiction
    | immediate =>
        have hout : outcome i = .immediate := by
          have h :=
            congrArg ObligatoryRuntimeClass.outcome hs
          simpa [outcome, obligatorySymbolOutcomeFn,
            ObligatoryRuntimeClass.outcome] using h
        rw [hout] at hi
        contradiction
    | deferred =>
        exact hdeferred i hs
  obtain ⟨vertex, hvbox, hvvertex, hge⟩ :=
    exists_obligatory_reduced_endpoint_ge
      outcome threshold processing hthreshold hzero'
        himmediate' hdeferred'
  let values : List ℝ := List.ofFn vertex
  have hvaluesLength : values.length = symbols.length := by
    simp [values]
  have hchoices :
      ObligatoryEndpointChoices
        (initialAnalysisState symbols.length) symbols values := by
    apply endpointChoices_of_get hvaluesLength
    intro i
    have hv := hvvertex i
    cases hs : symbols.get i with
    | zero =>
        have hout : outcome i = .zero := by
          have h :=
            congrArg ObligatoryRuntimeClass.outcome hs
          simpa [outcome, obligatorySymbolOutcomeFn,
            ObligatoryRuntimeClass.outcome] using h
        simpa [values, threshold,
          obligatoryReducedLower, obligatoryReducedUpper, hout] using hv
    | immediate =>
        have hout : outcome i = .immediate := by
          have h :=
            congrArg ObligatoryRuntimeClass.outcome hs
          simpa [outcome, obligatorySymbolOutcomeFn,
            ObligatoryRuntimeClass.outcome] using h
        simpa [values, threshold,
          obligatoryReducedLower, obligatoryReducedUpper, hout] using hv
    | deferred =>
        have hout : outcome i = .deferred := by
          have h :=
            congrArg ObligatoryRuntimeClass.outcome hs
          simpa [outcome, obligatorySymbolOutcomeFn,
            ObligatoryRuntimeClass.outcome] using h
        rcases hv with hv | hv <;>
          simpa [values, threshold,
            obligatoryReducedLower, obligatoryReducedUpper, hout] using hv
  let word := obligatoryEndpointWord symbols values
  have hwordLength : word.length = symbols.length := by
    exact obligatoryEndpointWord_length hchoices
  have hjobs :
      obligatoryBoundaryJobs
          (initialAnalysisState word.length) word =
        endpointJobs symbols values := by
    rw [hwordLength]
    exact obligatoryBoundaryJobs_endpointWord
      (AnalysisState.SymbolicallyEquivalent.refl _) hchoices
  have hsymbolic :
      symbolicJobs symbols values =
        obligatoryJobsOfFunctions outcome vertex := by
    simpa [values, outcome] using symbolicJobs_ofFn symbols vertex
  have hfixed :=
    obligatoryFixedWordExcess_eq_pairObjectives outcome vertex
  have hendpointALG :=
    endpointJobs_alg_eq_symbolicJobs symbols values
  have hendpointOPT :=
    endpointJobs_opt_eq_symbolicJobs symbols values
  have hvertex :
      obligatoryFixedWordExcess outcome vertex =
        obligatoryBoundaryALG word -
          RStar * obligatoryBoundaryOPT word := by
    rw [hfixed]
    unfold obligatoryBoundaryALG obligatoryBoundaryOPT
    rw [hjobs, hendpointALG, hendpointOPT, hsymbolic]
  refine ⟨word, hwordLength, hge.trans_eq ?_⟩
  rw [hvertex,
    obligatory_boundary_pair_excess_eq_boundaryExcess]

end

end SchedulingPaper
