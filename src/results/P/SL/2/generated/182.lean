

theorem Topology.P3_implies_subset_closure_interior_closure {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    Topology.P3 A → (A : Set X) ⊆ closure (interior (closure (A : Set X))) := by
  intro hP3 x hxA
  have : (x : X) ∈ interior (closure (A : Set X)) := hP3 hxA
  exact subset_closure this