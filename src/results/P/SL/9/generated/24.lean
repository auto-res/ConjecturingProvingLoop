

theorem Topology.P1_interiorClosure {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (A := interior (closure A)) := by
  dsimp [Topology.P1]
  intro x hx
  have : x ∈ closure (interior (closure A)) := Set.subset_closure hx
  have h_open : IsOpen (interior (closure A)) := isOpen_interior
  simpa [h_open.interior_eq] using this