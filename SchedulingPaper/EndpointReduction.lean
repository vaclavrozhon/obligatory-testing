import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Ring

namespace SchedulingPaper

noncomputable section

open Set

/-- A convex real function on a closed interval is bounded above by the
larger endpoint value. -/
theorem convexOn_Icc_le_max_endpoints
    {f : ℝ → ℝ} {a b x : ℝ}
    (hf : ConvexOn ℝ (Icc a b) f)
    (hx : x ∈ Icc a b) :
    f x ≤ max (f a) (f b) := by
  have hab : a ≤ b := hx.1.trans hx.2
  exact hf.le_max_of_mem_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hx

/-- Supremum form of `convexOn_Icc_le_max_endpoints`. -/
theorem sSup_image_Icc_le_max_endpoints
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ConvexOn ℝ (Icc a b) f) :
    sSup (f '' Icc a b) ≤ max (f a) (f b) := by
  apply csSup_le
  · exact ⟨f a, a, ⟨le_rfl, hab⟩, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact convexOn_Icc_le_max_endpoints hf hx

/-- The supremum is exactly the larger endpoint value. -/
theorem sSup_image_Icc_eq_max_endpoints
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hf : ConvexOn ℝ (Icc a b) f) :
    sSup (f '' Icc a b) = max (f a) (f b) := by
  apply le_antisymm (sSup_image_Icc_le_max_endpoints hab hf)
  have hbound : BddAbove (f '' Icc a b) := by
    refine ⟨max (f a) (f b), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact convexOn_Icc_le_max_endpoints hf hx
  apply max_le
  · exact le_csSup hbound ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  · exact le_csSup hbound ⟨b, ⟨hab, le_rfl⟩, rfl⟩

/-- Coordinatewise closed box. -/
def coordinateBox {n : ℕ} (lower upper : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ Icc (lower i) (upper i)}

/-- A vertex chooses one endpoint in every coordinate. -/
def IsBoxVertex {n : ℕ} (lower upper x : Fin n → ℝ) : Prop :=
  ∀ i, x i = lower i ∨ x i = upper i

/-- Convexity of every one-coordinate slice, with all other coordinates
fixed at an arbitrary point of the box. -/
def CoordinatewiseConvexOnBox {n : ℕ}
    (lower upper : Fin n → ℝ)
    (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x, x ∈ coordinateBox lower upper → ∀ i,
    ConvexOn ℝ (Icc (lower i) (upper i))
      (fun t => f (Function.update x i t))

private theorem exists_endpoint_update_ge
    {n : ℕ} {lower upper : Fin n → ℝ}
    {f : (Fin n → ℝ) → ℝ}
    (horder : ∀ i, lower i ≤ upper i)
    (hconvex : CoordinatewiseConvexOnBox lower upper f)
    (x : Fin n → ℝ) (hx : x ∈ coordinateBox lower upper)
    (i : Fin n) :
    ∃ e, (e = lower i ∨ e = upper i) ∧
      f x ≤ f (Function.update x i e) := by
  have hmax :=
    (hconvex x hx i).le_max_of_mem_Icc
      (show lower i ∈ Icc (lower i) (upper i) from
        ⟨le_rfl, horder i⟩)
      (show upper i ∈ Icc (lower i) (upper i) from
        ⟨horder i, le_rfl⟩)
      (hx i)
  have hmax' :
      f x ≤ max
        (f (Function.update x i (lower i)))
        (f (Function.update x i (upper i))) := by
    simpa [Function.update] using hmax
  by_cases hends :
      f (Function.update x i (lower i)) ≤
        f (Function.update x i (upper i))
  · exact ⟨upper i, Or.inr rfl, hmax'.trans_eq (max_eq_right hends)⟩
  · have hreverse :
        f (Function.update x i (upper i)) ≤
          f (Function.update x i (lower i)) :=
      le_of_not_ge hends
    exact ⟨lower i, Or.inl rfl,
      hmax'.trans_eq (max_eq_left hreverse)⟩

private theorem exists_partial_vertex_ge
    {n : ℕ} {lower upper : Fin n → ℝ}
    {f : (Fin n → ℝ) → ℝ}
    (horder : ∀ i, lower i ≤ upper i)
    (hconvex : CoordinatewiseConvexOnBox lower upper f)
    (coordinates : Finset (Fin n))
    (x : Fin n → ℝ) (hx : x ∈ coordinateBox lower upper) :
    ∃ y,
      y ∈ coordinateBox lower upper ∧
      (∀ i ∈ coordinates, y i = lower i ∨ y i = upper i) ∧
      (∀ i ∉ coordinates, y i = x i) ∧
      f x ≤ f y := by
  induction coordinates using Finset.induction_on with
  | empty =>
      exact ⟨x, hx, by simp, by simp, le_rfl⟩
  | @insert i coordinates hi ih =>
      obtain ⟨y, hyBox, hyEnds, hyOutside, hxy⟩ := ih
      obtain ⟨e, he, hye⟩ :=
        exists_endpoint_update_ge horder hconvex y hyBox i
      let z := Function.update y i e
      have hzBox : z ∈ coordinateBox lower upper := by
        intro j
        by_cases hji : j = i
        · subst j
          rcases he with rfl | rfl <;>
            simp [z, horder]
        · simpa [z, Function.update, hji] using hyBox j
      have hzEnds :
          ∀ j ∈ insert i coordinates,
            z j = lower j ∨ z j = upper j := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjs
        · simpa [z, Function.update] using he
        · have hji : j ≠ i := by
            intro h
            subst j
            exact hi hjs
          simpa [z, Function.update, hji] using hyEnds j hjs
      have hzOutside :
          ∀ j ∉ insert i coordinates, z j = x j := by
        intro j hj
        have hji : j ≠ i := by
          intro h
          subst j
          exact hj (Finset.mem_insert_self i coordinates)
        have hjs : j ∉ coordinates := by
          intro h
          exact hj (Finset.mem_insert_of_mem h)
        simpa [z, Function.update, hji] using hyOutside j hjs
      exact ⟨z, hzBox, hzEnds, hzOutside, hxy.trans hye⟩

/-- Iterated endpoint reduction on a finite box: every point is dominated by
some vertex. -/
theorem exists_boxVertex_ge
    {n : ℕ} {lower upper : Fin n → ℝ}
    {f : (Fin n → ℝ) → ℝ}
    (horder : ∀ i, lower i ≤ upper i)
    (hconvex : CoordinatewiseConvexOnBox lower upper f)
    (x : Fin n → ℝ) (hx : x ∈ coordinateBox lower upper) :
    ∃ vertex,
      vertex ∈ coordinateBox lower upper ∧
      IsBoxVertex lower upper vertex ∧
      f x ≤ f vertex := by
  obtain ⟨vertex, hbox, hvertex, _houtside, hle⟩ :=
    exists_partial_vertex_ge horder hconvex Finset.univ x hx
  exact ⟨vertex, hbox, fun i => hvertex i (Finset.mem_univ i), hle⟩

/-- Pointwise box bound obtained by checking only vertices. -/
theorem value_le_of_boxVertices_le
    {n : ℕ} {lower upper : Fin n → ℝ}
    {f : (Fin n → ℝ) → ℝ} {bound : ℝ}
    (horder : ∀ i, lower i ≤ upper i)
    (hconvex : CoordinatewiseConvexOnBox lower upper f)
    (hvertices :
      ∀ vertex, IsBoxVertex lower upper vertex → f vertex ≤ bound)
    (x : Fin n → ℝ) (hx : x ∈ coordinateBox lower upper) :
    f x ≤ bound := by
  obtain ⟨vertex, _hbox, hvertex, hxv⟩ :=
    exists_boxVertex_ge horder hconvex x hx
  exact hxv.trans (hvertices vertex hvertex)

/-- The piecewise-affine function used in endpoint reductions:
an affine term minus a nonnegative multiple of `min p h` is convex. -/
theorem convexOn_affine_sub_mul_min
    (A B c h : ℝ) (hc : 0 ≤ c) :
    ConvexOn ℝ univ
      (fun p : ℝ => A * p + B - c * min p h) := by
  have hAffine :
      ConvexOn ℝ univ (fun p : ℝ => A * p + B) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    dsimp
    calc
      A * (a * x + b * y) + B =
          A * (a * x + b * y) + (a + b) * B := by
            rw [hab, one_mul]
      _ = a * (A * x + B) + b * (A * y + B) := by ring
      _ ≤ a * (A * x + B) + b * (A * y + B) := le_rfl
  have hMin :
      ConcaveOn ℝ univ (fun p : ℝ => min p h) := by
    have hId : ConcaveOn ℝ univ (fun p : ℝ => p) := by
      simpa only [id_eq] using
        (concaveOn_id (𝕜 := ℝ)
          (convex_univ : Convex ℝ (univ : Set ℝ)))
    have hConst : ConcaveOn ℝ univ (fun _ : ℝ => h) :=
      concaveOn_const h convex_univ
    simpa only [Pi.inf_apply] using hId.inf hConst
  have hScaled :
      ConcaveOn ℝ univ (fun p : ℝ => c * min p h) := by
    simpa only [smul_eq_mul] using hMin.smul hc
  exact hAffine.sub hScaled

/-- Interval-restricted form of `convexOn_affine_sub_mul_min`. -/
theorem convexOn_Icc_affine_sub_mul_min
    (A B c h lower upper : ℝ) (hc : 0 ≤ c) :
    ConvexOn ℝ (Icc lower upper)
      (fun p : ℝ => A * p + B - c * min p h) :=
  (convexOn_affine_sub_mul_min A B c h hc).subset
    (subset_univ _) (convex_Icc lower upper)

end

end SchedulingPaper
