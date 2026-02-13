

theorem Topology.P1_and_emptyInterior_implies_empty {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X:=X) A) (h_int : interior (A : Set X) = ∅) :
    (A : Set X) = ∅ := by
  -- `P1` tells us that every point of `A` lies in `closure (interior A)`.
  -- If `interior A` is empty, that closure is also empty, forcing `A` itself to be empty.
  have h_subset : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : x ∈ closure (interior (A : Set X)) := hP1 hxA
    simpa [h_int, closure_empty] using this
  exact Set.Subset.antisymm h_subset (Set.empty_subset _)