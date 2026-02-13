

theorem closure_iUnion_subset_closure {X : Type*} [TopologicalSpace X] {ι : Sort _}
    (f : ι → Set X) :
    (⋃ i, closure (f i : Set X)) ⊆ closure (⋃ i, f i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have h_mono : closure (f i : Set X) ⊆ closure (⋃ j, f j : Set X) := by
    apply closure_mono
    intro y hy
    exact Set.mem_iUnion.mpr ⟨i, hy⟩
  exact h_mono hxi