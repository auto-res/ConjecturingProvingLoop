

theorem Topology.interior_subset_interior_closure_interior {X : Type*} [TopologicalSpace X]
    (A : Set X) :
    interior A ⊆ interior (closure (interior A)) := by
  have hOpen : IsOpen (interior A) := isOpen_interior
  have hSub : (interior A : Set X) ⊆ closure (interior A) := subset_closure
  exact interior_maximal hSub hOpen