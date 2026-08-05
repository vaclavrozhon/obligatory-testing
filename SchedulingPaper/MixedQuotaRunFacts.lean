import SchedulingPaper.MixedQuotaTerminal
import SchedulingPaper.MixedQuotaFreeze
import SchedulingPaper.LowBaseline

/-!
# Fuel and terminal facts for the mixed-quota run

The universal work rank is independent of the oracle.  Freezing and replay
therefore transfer the ordinary `2n+1` fuel bound to every adaptive run.  We
record the specialization needed by the mixed-quota lower construction next
to its reachable-history theorem.
-/

namespace SchedulingPaper

noncomputable section

namespace LowerBound

/-- Every adaptive experiment is semantically settled after the universal
analysis fuel.  No admissibility hypothesis is needed for this purely
operational fact. -/
theorem adaptiveRun_analysisFuel_settled
    {n : ℕ} (cap : Cap) (adversary : Online.Oracle n)
    (strategy : Online.Strategy n) :
    let fuel := 2 * n + 1
    let result :=
      (Online.adaptiveRun cap adversary strategy fuel).result
    resultSettled result := by
  dsimp only
  let frozen :=
    Online.frozenProcessingTimes cap adversary strategy
      (fun _ => 0) (2 * n + 1)
  have hfixed :
      (Online.run cap (Online.fixedOracle frozen)
        strategy (2 * n + 1)).reason ≠ .outOfFuel :=
    Online.run_reason_ne_outOfFuel_analysisFuel
      cap (Online.fixedOracle frozen) strategy
  have hreplay :
      Online.run cap (Online.fixedOracle frozen)
          strategy (2 * n + 1) =
        (Online.adaptiveRun cap adversary
          strategy (2 * n + 1)).result := by
    simpa [frozen] using
      Online.replay cap adversary strategy
        (fun _ => 0) (2 * n + 1)
  unfold resultSettled
  rw [← hreplay]
  exact hfixed

namespace MixedQuotaOracle

/-- At analysis fuel the concrete mixed-quota run is both settled and
represented by one of the two reachable mixed phases. -/
theorem mixedQuota_analysisFuel_history
    {n : ℕ} (hn : 0 < n) {u : ℝ}
    {M A B : ℕ} (hM : 0 < M)
    (strategy : Online.Strategy n) :
    let fuel := 2 * n + 1
    let result :=
      (Online.adaptiveRun (.finite u)
        (oracle n u M A B) strategy fuel).result
    resultSettled result ∧
      ∃ phase,
        MixedQuotaHistory n u (quotaFraction M A B) A B
          phase result.config := by
  dsimp only
  refine ⟨adaptiveRun_analysisFuel_settled
    (.finite u) (oracle n u M A B) strategy, ?_⟩
  exact adaptiveRun_mixedQuotaHistory hn hM strategy (2 * n + 1)

end MixedQuotaOracle

end LowerBound

end

end SchedulingPaper
