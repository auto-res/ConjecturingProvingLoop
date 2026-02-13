

theorem P1_iff_subset_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 A ↔ A ⊆ closure (interior A) := by
  rfl