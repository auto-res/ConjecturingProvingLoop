

theorem P3_neq {X : Type*} [TopologicalSpace X] {A : Set X} : ¬ P3 A → interior (closure A) ≠ closure A := by
  intro hNotP3
  intro h_eq
  -- From the assumed equality we can build `P3 A`.
  have hP3 : P3 A := by
    intro x hxA
    have hx_closure : x ∈ closure A := subset_closure hxA
    simpa [h_eq] using hx_closure
  -- This contradicts the assumption `¬ P3 A`.
  exact hNotP3 hP3