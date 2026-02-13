

theorem subset_interior_closure_of_subset_of_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hP3 : Topology.P3 A) (hBA : B ⊆ A) :
    B ⊆ interior (closure A) := by
  intro x hxB
  exact hP3 (hBA hxB)