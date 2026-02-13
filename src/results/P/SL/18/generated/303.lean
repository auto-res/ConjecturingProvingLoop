

theorem interior_closure_nonempty_iff_of_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP3 : Topology.P3 A) :
    (interior (closure (A : Set X))).Nonempty ↔ A.Nonempty := by
  constructor
  · intro hInt
    exact Topology.nonempty_of_interior_closure_nonempty (A := A) hInt
  · intro hA
    exact Topology.interior_closure_nonempty_of_P3 (A := A) hP3 hA