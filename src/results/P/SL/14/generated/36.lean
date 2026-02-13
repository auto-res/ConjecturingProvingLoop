

theorem Topology.interiorClosure_satisfies_P1
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (interior (closure A)) := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ closure (interior (closure A)) := by
    exact subset_closure hx
  simpa [interior_interior] using this