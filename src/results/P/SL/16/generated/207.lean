

theorem Topology.open_subset_closure_subset_interior_closure
    {X : Type*} [TopologicalSpace X] {A U : Set X}
    (hUopen : IsOpen U) (hUsubset : U ⊆ closure A) :
    U ⊆ interior (closure A) := by
  exact interior_maximal hUsubset hUopen