

theorem P1_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P1 (A i)) :
    Topology.P1 (⋃ i, A i) := by
  classical
  dsimp [Topology.P1] at hA ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxAi⟩
  have hxClAi : x ∈ closure (interior (A i)) := (hA i) hxAi
  have hInt_subset : interior (A i) ⊆ interior (⋃ i, A i) := by
    have hSub : A i ⊆ ⋃ j, A j := Set.subset_iUnion _ _
    exact interior_mono hSub
  have hCl_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ i, A i)) :=
    closure_mono hInt_subset
  exact hCl_subset hxClAi