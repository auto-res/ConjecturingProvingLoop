

theorem Topology.subset_interior_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) :
    (A : Set X) ⊆ interior (closure A) := by
  exact interior_maximal (subset_closure : (A : Set X) ⊆ closure A) hA