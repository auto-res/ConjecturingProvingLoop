

theorem interior_subset_closure_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} : interior A ⊆ closure (interior (closure A)) := by
  intro x hx
  -- Step 1: send `x` into `interior (closure A)` via monotonicity of `interior`.
  have hx₁ : x ∈ interior (closure A) :=
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hx
  -- Step 2: every set is contained in its closure.
  have hsubset : (interior (closure A) : Set X) ⊆ closure (interior (closure A)) :=
    subset_closure
  exact hsubset hx₁