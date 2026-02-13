

theorem subset_closure_interior_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (X := X) A) :
    (A : Set X) ⊆ closure (interior A) := by
  intro x hx
  exact hP1 hx