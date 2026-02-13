

theorem Topology.interior_eq_self_of_closed_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP3 : Topology.P3 A) :
    interior A = A := by
  apply subset_antisymm
  ·
    exact interior_subset
  ·
    intro x hxA
    have : x ∈ interior (closure A) := hP3 hxA
    simpa [hA_closed.closure_eq] using this