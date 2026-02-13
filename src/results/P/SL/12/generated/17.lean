

theorem Topology.P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (X := X) A ↔ closure (A : Set X) = closure (interior A) := by
  constructor
  · intro hA
    exact Topology.closure_eq_closure_interior_of_P1 (X := X) (A := A) hA
  · intro hEq
    have hsubset : (A : Set X) ⊆ closure (A : Set X) := subset_closure
    simpa [Topology.P1, hEq] using hsubset