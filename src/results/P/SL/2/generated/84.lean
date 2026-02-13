

theorem Topology.interior_closure_interior_subset_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  -- Step 1: `x` lies in the closure of `interior A`.
  have hx₁ : x ∈ closure (interior A) := interior_subset hx
  -- Step 2: `closure (interior A)` is contained in `closure A`.
  have hx₂ : (closure (interior A) : Set X) ⊆ closure A :=
    closure_mono interior_subset
  -- Combining the two inclusions yields the result.
  exact hx₂ hx₁