

theorem Topology.P1_iff_closureInterior_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact Topology.closureInterior_eq_closure_of_P1 (X := X) (A := A) hP1
  · intro h_eq
    dsimp [Topology.P1]
    intro x hx
    have : x ∈ closure A := subset_closure hx
    simpa [h_eq] using this