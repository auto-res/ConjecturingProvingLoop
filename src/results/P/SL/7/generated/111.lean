

theorem Topology.interiorClosure_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    interior (closure (A : Set X)) ⊆ closure (interior (closure (A : Set X))) := by
  intro x hx
  exact subset_closure hx