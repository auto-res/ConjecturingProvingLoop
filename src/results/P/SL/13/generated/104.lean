

theorem Topology.closed_P3_implies_interior_eq_self {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA_closed : IsClosed (A : Set X)) (hP3 : Topology.P3 (X:=X) A) :
    interior (A : Set X) = A := by
  have hA_open : IsOpen (A : Set X) :=
    Topology.closed_P3_implies_isOpen (X:=X) (A:=A) hA_closed hP3
  simpa using hA_open.interior_eq