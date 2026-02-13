

theorem Topology.closure_subset_univ {X : Type*} [TopologicalSpace X] (A : Set X) :
    closure (A : Set X) ⊆ (Set.univ : Set X) := by
  intro x _
  trivial