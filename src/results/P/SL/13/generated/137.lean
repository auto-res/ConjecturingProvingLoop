

theorem Topology.P2_and_emptyInterior_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP2 : Topology.P2 (X:=X) A)
    (h_int : interior (A : Set X) = ∅) :
    (A : Set X) = ∅ := by
  -- The right side of the `P2` inclusion is empty because `interior A` is empty.
  have h_empty : interior (closure (interior (A : Set X))) = (∅ : Set X) := by
    simpa [h_int, closure_empty, interior_empty]
  -- Hence every point of `A` lies in the empty set, so `A` is empty.
  have h_subset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : (x : X) ∈ interior (closure (interior (A : Set X))) := hP2 hxA
    simpa [h_empty] using this
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)