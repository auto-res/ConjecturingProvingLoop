

theorem Topology.interior_eq_self_of_isClosed_and_P3 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hA : IsClosed A) :
    Topology.P3 (A := A) → interior A = A := by
  intro hP3
  -- `P3` together with the closedness of `A` implies that `A` is open
  have hOpen : IsOpen A :=
    (Topology.P3_iff_isOpen_of_isClosed (A := A) hA).1 hP3
  -- The interior of an open set is the set itself
  simpa using hOpen.interior_eq