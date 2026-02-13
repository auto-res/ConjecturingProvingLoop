

theorem Topology.closed_P2_implies_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) (hP2 : Topology.P2 (X:=X) A) :
    interior (A : Set X) = A := by
  have hA_open : IsOpen (A : Set X) :=
    (Topology.P2_iff_isOpen_of_isClosed (X:=X) (A:=A) hA_closed).1 hP2
  simpa using hA_open.interior_eq