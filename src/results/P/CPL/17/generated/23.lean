

theorem P2_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : Topology.P2 A := by
  exact P2_of_open (A := A) (isOpen_discrete _)

theorem P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → Topology.P3 A := by
  intro hClosure
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hClosure, interior_univ] using this