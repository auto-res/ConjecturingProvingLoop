

theorem Topology.interiorClosure_subset_closureInteriorClosure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior (closure A) ⊆ closure (interior (closure A)) := by
  intro x hx
  exact Set.subset_closure hx