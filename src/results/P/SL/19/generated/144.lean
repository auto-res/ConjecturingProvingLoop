

theorem Topology.closure_subset_closure_of_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : A ⊆ interior (closure B)) :
    closure A ⊆ closure B := by
  -- First, take closures on both sides of the inclusion `h`.
  have h₁ : closure A ⊆ closure (interior (closure B)) := closure_mono h
  -- Then, use the previously proved inclusion
  -- `closure (interior (closure B)) ⊆ closure B`.
  have h₂ : closure (interior (closure B)) ⊆ closure B :=
    Topology.closure_interior_closure_subset_closure (A := B)
  -- Assemble the two inclusions.
  exact Set.Subset.trans h₁ h₂