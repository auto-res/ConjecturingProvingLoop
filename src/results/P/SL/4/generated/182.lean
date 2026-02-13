

theorem interior_subset_closure_interior_closure_fixed
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A ⊆ closure (interior (closure A)) := by
  intro x hxIntA
  -- First, use the monotonicity of `interior` to lift the point to
  -- `interior (closure A)`.
  have hxIntClA : x ∈ interior (closure A) :=
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hxIntA
  -- Any point of an interior lies in the closure of that interior.
  exact subset_closure hxIntClA