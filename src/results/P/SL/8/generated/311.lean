

theorem closure_subset_of_subset_interior {X : Type*} [TopologicalSpace X]
    {A B : Set X} :
    (closure A ⊆ interior B) → closure A ⊆ B := by
  intro hSub
  intro x hxClA
  have hxIntB : x ∈ interior B := hSub hxClA
  exact interior_subset hxIntB