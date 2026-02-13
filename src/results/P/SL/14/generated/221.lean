

theorem Topology.Subset_closureInteriorClosure_of_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (A : Set X) ⊆ closure (interior (closure A)) := by
  intro hP1
  dsimp [Topology.P1] at hP1
  have h_step :
      closure (interior A) ⊆ closure (interior (closure A)) :=
    Topology.closureInterior_subset_closureInteriorClosure (X := X) (A := A)
  exact Set.Subset.trans hP1 h_step