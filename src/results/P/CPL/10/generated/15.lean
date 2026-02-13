

theorem P1_prod_self {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P1 A) : Topology.P1 (A ×ˢ A) := by
  simpa using
    (Topology.P1_prod (X := X) (Y := X) (A := A) (B := A) hA hA)