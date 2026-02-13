

theorem Topology.P3_and_emptyInteriorClosure_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP3 : Topology.P3 (X := X) A)
    (h_int : interior (closure (A : Set X)) = ∅) :
    (A : Set X) = ∅ := by
  -- From `P3`, every point of `A` lies in `interior (closure A)`.
  have h_subset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : x ∈ interior (closure (A : Set X)) := hP3 hxA
    simpa [h_int] using this
  -- Combine the derived inclusion with the trivial one in the other direction.
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)