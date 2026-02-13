

theorem closure_inter_interior_subset_closureInterior_right
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ interior B) ⊆ closure (interior B) := by
  have h : A ∩ interior B ⊆ interior B := by
    intro x hx
    exact hx.2
  exact closure_mono h