

theorem P3_iUnion {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    (∀ i, Topology.P3 (F i)) → Topology.P3 (⋃ i, F i) := by
  intro hF
  dsimp [Topology.P3] at hF ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxFi⟩
  have hx_int : x ∈ interior (closure (F i : Set X)) := hF i hxFi
  have h_mono : interior (closure (F i : Set X)) ⊆
      interior (closure (⋃ j, F j : Set X)) := by
    have h_clos : closure (F i : Set X) ⊆ closure (⋃ j, F j : Set X) := by
      have h_subset : (F i : Set X) ⊆ ⋃ j, F j := Set.subset_iUnion _ _
      exact closure_mono h_subset
    exact interior_mono h_clos
  exact h_mono hx_int