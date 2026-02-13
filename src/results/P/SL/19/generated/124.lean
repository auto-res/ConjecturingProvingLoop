

theorem Topology.P3_of_interior_eq_self {X : Type*} [TopologicalSpace X] {A : Set X}
    (hInt : interior A = A) : Topology.P3 (A := A) := by
  dsimp [Topology.P3]
  intro x hx
  have hxInt : x ∈ interior A := by
    simpa [hInt] using hx
  have hsubset : interior A ⊆ interior (closure A) :=
    Topology.interior_subset_interior_closure (A := A)
  exact hsubset hxInt