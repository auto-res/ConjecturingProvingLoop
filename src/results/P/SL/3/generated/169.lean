

theorem interior_closure_iUnion_subset {X : Type*} [TopologicalSpace X]
    {ι : Sort _} {f : ι → Set X} :
    (⋃ i, interior (closure (f i : Set X))) ⊆
      interior (closure (⋃ i, f i : Set X)) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have h_closure :
      closure (f i : Set X) ⊆ closure (⋃ j, f j : Set X) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.mpr ⟨i, hy⟩
  have h_interior :
      interior (closure (f i : Set X)) ⊆
        interior (closure (⋃ j, f j : Set X)) :=
    interior_mono h_closure
  exact h_interior hxi