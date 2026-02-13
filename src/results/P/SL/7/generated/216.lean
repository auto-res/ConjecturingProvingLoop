

theorem Topology.closureInterior_eq_of_P3_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 A) : closure (interior A) = A := by
  -- First, derive `P1 A` from `P3 A` and the closedness of `A`.
  have hP1 : Topology.P1 A := Topology.P1_of_P3_closed (A := A) hA hP3
  -- Then apply the closed‐set characterisation of `P1`.
  exact (Topology.P1_closed_iff_closureInterior_eq (A := A) hA).1 hP1