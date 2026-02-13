

theorem P3_univ {X : Type*} [TopologicalSpace X] : Topology.P3 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, isOpen_univ.interior_eq] using hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  intro x hx
  simpa [closure_univ, isOpen_univ.interior_eq] using hx