

theorem Topology.P3_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X}
    (hClosed : IsClosed A) (hDense : Dense A) : Topology.P3 A := by
  -- We already have all three properties for a closed, dense set.
  have h := Topology.P_properties_of_closed_dense (A := A) hClosed hDense
  -- Extract the `P3` component.
  exact h.right.right