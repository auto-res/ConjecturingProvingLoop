

theorem P1_of_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : Topology.P1 A := by
  intro x hxA
  have h_int : interior (A : Set X) = A := (isOpen_discrete _).interior_eq
  have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
  simpa [h_int] using hx_cl