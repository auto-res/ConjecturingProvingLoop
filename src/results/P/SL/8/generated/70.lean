

theorem P3_subset_interior_of_closure_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hP3 : Topology.P3 A) (hcl : closure A ⊆ B) :
    A ⊆ interior B := by
  dsimp [Topology.P3] at hP3
  have hInt : interior (closure A) ⊆ interior B := interior_mono hcl
  exact Set.Subset.trans hP3 hInt