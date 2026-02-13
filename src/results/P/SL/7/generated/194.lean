

theorem Topology.P2_subset_closureInteriorClosureInterior
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P2 A → A ⊆ closure (interior (closure (interior A))) := by
  intro hP2 x hxA
  have hxInt : x ∈ interior (closure (interior A)) := hP2 hxA
  exact subset_closure hxInt