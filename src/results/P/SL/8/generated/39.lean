

theorem P3_subset_interiorClosure_of_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP3 : Topology.P3 A) (hAB : A ⊆ B) :
    A ⊆ interior (closure B) := by
  dsimp [Topology.P3] at hP3
  have h_closure : closure A ⊆ closure B := closure_mono hAB
  have h_interior : interior (closure A) ⊆ interior (closure B) :=
    interior_mono h_closure
  exact Set.Subset.trans hP3 h_interior