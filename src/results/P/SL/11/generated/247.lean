

theorem closure_eq_closure_interior_of_P1_iUnion
    {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P1 (A i)) :
    closure (⋃ i, A i) = closure (interior (⋃ i, A i)) := by
  -- First, obtain `P1` for the union using the existing lemma.
  have hUnion : Topology.P1 (⋃ i, A i) := Topology.P1_iUnion hA
  -- Apply the characterisation of `P1` to relate the two closures.
  exact Topology.closure_eq_closure_interior_of_P1 (A := ⋃ i, A i) hUnion