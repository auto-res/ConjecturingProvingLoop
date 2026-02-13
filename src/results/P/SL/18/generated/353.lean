

theorem P3_compl_of_empty_interior
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior (A : Set X) = ∅) :
    Topology.P3 (Aᶜ) := by
  -- From the emptiness of `interior A`, deduce that `Aᶜ` is dense.
  have hDense : Dense ((Aᶜ) : Set X) :=
    (Topology.dense_compl_iff_interior_eq_empty (A := A)).2 hInt
  -- Density implies property `P3`.
  exact Topology.P3_of_dense (A := Aᶜ) hDense