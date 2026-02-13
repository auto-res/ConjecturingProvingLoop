

theorem Topology.subset_interior_closure_interior_of_P2 {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : A ⊆ B) (hP2B : Topology.P2 B) :
    A ⊆ interior (closure (interior B)) := by
  intro x hxA
  exact hP2B (hAB hxA)