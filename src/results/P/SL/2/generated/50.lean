

theorem Topology.isClosed_P3_implies_interior_closure_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X} :
    IsClosed A → Topology.P3 A → interior (closure A) = A := by
  intro hClosed hP3
  apply subset_antisymm
  ·
    intro x hx
    have : x ∈ closure A := interior_subset hx
    simpa [hClosed.closure_eq] using this
  ·
    intro x hxA
    exact hP3 hxA