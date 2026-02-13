

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    exact closure_eq_closure_interior_of_P1 hP1
  · intro h_eq
    dsimp [Topology.P1]
    intro x hx
    have : x ∈ closure A := subset_closure hx
    simpa [h_eq] using this