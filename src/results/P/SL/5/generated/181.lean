

theorem P2_iff_interior_eq_self_of_isClosed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P2 (X := X) A ↔ interior (A : Set X) = A := by
  have h1 := Topology.P2_iff_P3_of_isClosed (X := X) (A := A) hA_closed
  have h2 := Topology.P3_iff_interior_eq_self_of_isClosed (X := X) (A := A) hA_closed
  exact h1.trans h2