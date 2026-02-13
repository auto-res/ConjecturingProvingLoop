

theorem Topology.interior_subset_interior_closure_union_left
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior A ⊆ interior (closure (A ∪ B)) := by
  -- First inclusion: `interior A ⊆ interior (closure A)`.
  have h₁ : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A)
  -- Second inclusion: `interior (closure A) ⊆ interior (closure (A ∪ B))`.
  have h₂ : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
    apply interior_mono
    have : closure A ⊆ closure (A ∪ B) := by
      apply closure_mono
      exact Set.subset_union_left
    exact this
  -- Combine the two inclusions.
  exact Set.Subset.trans h₁ h₂