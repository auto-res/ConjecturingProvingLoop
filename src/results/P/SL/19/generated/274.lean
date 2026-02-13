

theorem Topology.frontier_eq_empty_of_isClosed_and_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsClosed A) (hP3 : Topology.P3 (A := A)) :
    frontier A = (∅ : Set X) := by
  -- `P3` together with `A` closed implies `A` is open
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  -- A set that is both open and closed has empty frontier
  exact Topology.frontier_eq_empty_of_isOpen_and_isClosed
      (A := A) hOpen hA