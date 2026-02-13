

theorem Topology.P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    Topology.P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    exact Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hP1
  · intro h_eq
    exact fun x hxA => by
      have : x ∈ closure A := subset_closure hxA
      simpa [h_eq] using this