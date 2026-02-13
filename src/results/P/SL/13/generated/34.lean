

theorem Topology.P1_interiorClosure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) (interior (closure (A : Set X))) := by
  dsimp [Topology.P1]
  intro x hx
  have : (x : X) ∈ closure (interior (closure (A : Set X))) :=
    subset_closure hx
  simpa [interior_interior] using this