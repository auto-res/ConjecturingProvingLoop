

theorem closure_inter_interiors_subset_closure_interior_inter {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X) ∩ interior B) ⊆
      closure (interior ((A ∩ B) : Set X)) := by
  apply closure_mono
  exact inter_interiors_subset_interior_inter (A := A) (B := B)