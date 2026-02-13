

theorem Topology.open_subset_closure_iff_subset_interior_closure {X : Type*}
    [TopologicalSpace X] {A U : Set X} (hU : IsOpen (U : Set X)) :
    (U ⊆ closure (A : Set X)) ↔ U ⊆ interior (closure A) := by
  constructor
  · intro hU_sub
    exact interior_maximal hU_sub hU
  · intro hU_sub
    exact Set.Subset.trans hU_sub interior_subset