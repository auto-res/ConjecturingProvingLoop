

theorem Topology.P1_iff_closure_interior_eq_closure {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (interior A) = closure A := by
  constructor
  · intro hP1
    exact Topology.closure_interior_eq_closure_of_P1 (X := X) (A := A) hP1
  · intro h_eq
    dsimp [Topology.P1]
    intro x hxA
    have hxCl : x ∈ closure A := subset_closure hxA
    simpa [h_eq] using hxCl