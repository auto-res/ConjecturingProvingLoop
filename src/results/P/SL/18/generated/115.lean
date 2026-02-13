

theorem interior_closure_inter_eq_of_closed_P3
    {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hA_closed : IsClosed A) (hB_closed : IsClosed B)
    (hP3A : Topology.P3 A) (hP3B : Topology.P3 B) :
    interior (closure (A ∩ B : Set X)) = A ∩ B := by
  -- `A ∩ B` is closed.
  have hClosedInter : IsClosed (A ∩ B : Set X) := hA_closed.inter hB_closed
  -- `A ∩ B` satisfies `P3`.
  have hP3Inter : Topology.P3 (A ∩ B : Set X) :=
    Topology.P3_inter_closed hA_closed hB_closed hP3A hP3B
  -- Hence `A ∩ B` is open.
  have hOpenInter : IsOpen (A ∩ B : Set X) :=
    (Topology.P3_closed_iff_open hClosedInter).1 hP3Inter
  -- The interior of an open set is the set itself.
  have hIntEq : interior (A ∩ B : Set X) = A ∩ B := hOpenInter.interior_eq
  -- The closure of a closed set is the set itself.
  have hClosEq : closure (A ∩ B : Set X) = A ∩ B := hClosedInter.closure_eq
  -- Combine the two equalities to obtain the desired statement.
  simpa [hClosEq, hIntEq]