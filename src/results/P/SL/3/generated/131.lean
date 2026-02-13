

theorem inter_interiors_subset_interior_inter {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    (interior (A : Set X)) ∩ interior B ⊆ interior ((A ∩ B) : Set X) := by
  have hSubset : (interior (A : Set X)) ∩ interior B ⊆ (A : Set X) ∩ B := by
    intro x hx
    rcases hx with ⟨hA, hB⟩
    exact And.intro (interior_subset hA) (interior_subset hB)
  have hOpen : IsOpen ((interior (A : Set X)) ∩ interior B) :=
    isOpen_interior.inter isOpen_interior
  exact interior_maximal hSubset hOpen