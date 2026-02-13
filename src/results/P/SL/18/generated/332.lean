

theorem interior_inter_subset_interiors_alt
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (A ∩ B : Set X) ⊆ interior A ∩ interior B := by
  intro x hx
  exact
    ⟨(interior_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx,
     (interior_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx⟩