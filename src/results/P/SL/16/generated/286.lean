

theorem Topology.closure_subset_closure_of_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : (B : Set X) ⊆ interior (closure A)) :
    closure B ⊆ closure A := by
  -- First, take closures on both sides of the inclusion `h`.
  have h₁ : closure B ⊆ closure (interior (closure A)) :=
    closure_mono h
  -- Next, use the fact that `interior (closure A) ⊆ closure A`.
  have h₂ : closure (interior (closure A)) ⊆ closure A := by
    have : interior (closure A) ⊆ closure A := interior_subset
    have h_cl : closure (interior (closure A)) ⊆ closure (closure A) :=
      closure_mono this
    simpa [closure_closure] using h_cl
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂