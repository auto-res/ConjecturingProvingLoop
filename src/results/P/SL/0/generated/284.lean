

theorem iUnion_closures_subset_closure_iUnion {X ι : Type*} [TopologicalSpace X]
    {F : ι → Set X} :
    (⋃ i, closure (F i : Set X)) ⊆ closure (⋃ i, F i : Set X) := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hx_cl⟩
  have h_sub : (F i : Set X) ⊆ ⋃ j, F j := by
    intro y hy
    exact Set.mem_iUnion.mpr ⟨i, hy⟩
  have h_cl : closure (F i : Set X) ⊆ closure (⋃ j, F j : Set X) :=
    closure_mono h_sub
  exact h_cl hx_cl