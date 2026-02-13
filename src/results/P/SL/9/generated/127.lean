

theorem Topology.disjoint_closure_interiorCompl {X : Type*} [TopologicalSpace X] {A : Set X} :
    Disjoint (closure A) (interior (Aᶜ)) := by
  simpa [compl_compl] using
    (Topology.disjoint_closureCompl_interior (A := Aᶜ))