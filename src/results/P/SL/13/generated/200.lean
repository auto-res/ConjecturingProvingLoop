

theorem Topology.P2_and_emptyInteriorClosureInterior_implies_empty {X : Type*}
    [TopologicalSpace X] {A : Set X}
    (hP2 : Topology.P2 (X := X) A)
    (h_int : interior (closure (interior (A : Set X))) = (∅ : Set X)) :
    (A : Set X) = (∅ : Set X) := by
  -- From `P2`, every point of `A` lies in `interior (closure (interior A))`,
  -- which is empty by assumption, hence `A` itself must be empty.
  have h_subset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : (x : X) ∈ interior (closure (interior (A : Set X))) := hP2 hxA
    simpa [h_int] using this
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)