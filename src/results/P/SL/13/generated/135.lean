

theorem Topology.closed_P3_implies_P1 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X:=X) A) :
    Topology.P1 (X:=X) A := by
  -- From the closedness of `A` and `P3`, we know that `A` is open.
  have hA_open : IsOpen (A : Set X) :=
    Topology.closed_P3_implies_isOpen (X := X) (A := A) hA_closed hP3
  -- Every open set satisfies `P1`.
  exact Topology.isOpen_subset_closureInterior (X := X) (A := A) hA_open