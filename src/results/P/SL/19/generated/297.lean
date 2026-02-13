

theorem Topology.open_subset_interior_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsOpen A) : (A : Set X) ⊆ interior (closure A) := by
  have hSub : (A : Set X) ⊆ closure A := subset_closure
  exact interior_maximal hSub hA