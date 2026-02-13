

theorem Topology.interiorClosure_mono_of_closure_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (h : closure (A : Set X) ⊆ closure (B : Set X)) :
    interior (closure (A : Set X)) ⊆ interior (closure (B : Set X)) := by
  exact interior_mono h