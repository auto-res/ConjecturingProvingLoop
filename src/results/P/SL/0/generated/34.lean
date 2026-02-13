

theorem P2_iUnion {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    (∀ i, Topology.P2 (F i)) → Topology.P2 (⋃ i, F i) := by
  intro hF
  dsimp [Topology.P2] at hF ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxFi⟩
  have hx_in : x ∈ interior (closure (interior (F i : Set X))) := hF i hxFi
  have h_mono : interior (closure (interior (F i : Set X))) ⊆
      interior (closure (interior (⋃ j, F j : Set X))) := by
    have h_int_sub : interior (F i : Set X) ⊆ interior (⋃ j, F j : Set X) :=
      interior_mono (Set.subset_iUnion _ _)
    have h_cl_sub : closure (interior (F i : Set X)) ⊆
        closure (interior (⋃ j, F j : Set X)) := closure_mono h_int_sub
    exact interior_mono h_cl_sub
  exact h_mono hx_in