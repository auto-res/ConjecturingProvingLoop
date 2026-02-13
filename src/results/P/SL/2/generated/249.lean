

theorem Topology.P1_iff_closure_subset_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ (closure (A : Set X) ⊆ closure (interior A)) := by
  constructor
  · intro hP1
    exact
      Topology.P1_implies_closure_subset_closure_interior (A := A) hP1
  · intro hSub
    exact
      Topology.P1_of_closure_subset_closure_interior (A := A) hSub