

theorem interior_closure_interior_inter_subset {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    interior (closure (interior ((A ∩ B) : Set X))) ⊆
      interior (closure (interior A)) ∩ interior (closure (interior B)) := by
  intro x hx
  have hA :
      interior (closure (interior ((A ∩ B) : Set X))) ⊆
        interior (closure (interior A)) := by
    apply interior_mono
    have h_closure :
        closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior A) := by
      apply closure_mono
      have h_int :
          interior ((A ∩ B) : Set X) ⊆ interior A := by
        apply interior_mono
        exact Set.inter_subset_left
      exact h_int
    exact h_closure
  have hB :
      interior (closure (interior ((A ∩ B) : Set X))) ⊆
        interior (closure (interior B)) := by
    apply interior_mono
    have h_closure :
        closure (interior ((A ∩ B) : Set X)) ⊆ closure (interior B) := by
      apply closure_mono
      have h_int :
          interior ((A ∩ B) : Set X) ⊆ interior B := by
        apply interior_mono
        exact Set.inter_subset_right
      exact h_int
    exact h_closure
  exact And.intro (hA hx) (hB hx)