

theorem P1_iUnion {X ι : Type*} [TopologicalSpace X] {F : ι → Set X} :
    (∀ i, Topology.P1 (F i)) → Topology.P1 (⋃ i, F i) := by
  intro hF
  dsimp [Topology.P1] at hF ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxFi⟩
  have hx_cl : x ∈ closure (interior (F i : Set X)) := hF i hxFi
  have h_mono : closure (interior (F i : Set X)) ⊆
      closure (interior (⋃ j, F j : Set X)) := by
    have h_int_sub : interior (F i : Set X) ⊆ interior (⋃ j, F j : Set X) :=
      interior_mono (Set.subset_iUnion _ _)
    exact closure_mono h_int_sub
  exact h_mono hx_cl