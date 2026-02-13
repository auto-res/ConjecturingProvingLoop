

theorem Topology.P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) :
    Topology.P1 (A := interior A) := by
  dsimp [Topology.P1]
  intro x hx
  have hx' : x ∈ closure (interior A) := Set.subset_closure hx
  have h_open : IsOpen (interior A) := isOpen_interior
  simpa [h_open.interior_eq] using hx'