

theorem P3_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P3 (A i)) :
    Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxAi⟩
  have hxInterior : x ∈ interior (closure (A i)) := (hA i) hxAi
  have hsubset : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    apply interior_mono
    have hclsubset : closure (A i) ⊆ closure (⋃ j, A j) := by
      apply closure_mono
      exact Set.subset_iUnion _ _
    exact hclsubset
  exact hsubset hxInterior