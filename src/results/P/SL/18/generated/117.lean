

theorem subset_closure_interior_closure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) :
    (A : Set X) ⊆ closure (interior (closure A)) := by
  -- From `P1`, we already know `A ⊆ closure (interior A)`.
  have h₁ : (A : Set X) ⊆ closure (interior A) := hP1
  -- And `closure (interior A) ⊆ closure (interior (closure A))` by monotonicity.
  have h₂ :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closure_interior_subset_closure_interior_closure (A := A)
  -- Combining the two inclusions yields the desired result.
  exact Set.Subset.trans h₁ h₂