

theorem P1_and_closure_interior_eq_empty_implies_eq_empty
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A →
      closure (interior (A : Set X)) = (∅ : Set X) →
      A = (∅ : Set X) := by
  intro hP1 hClEmpty
  -- From `P1`, we have `A ⊆ closure (interior A)`.
  have hSub : (A : Set X) ⊆ (∅ : Set X) := by
    intro x hxA
    have : x ∈ closure (interior (A : Set X)) := hP1 hxA
    simpa [hClEmpty] using this
  exact Set.Subset.antisymm hSub (Set.empty_subset _)