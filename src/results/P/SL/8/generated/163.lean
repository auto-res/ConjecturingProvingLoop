

theorem P3_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P3 (A i)) :
    Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxAi⟩
  have hxIntA : x ∈ interior (closure (A i)) := (hA i) hxAi
  have h_closure_subset : closure (A i) ⊆ closure (⋃ j, A j) := by
    have h_sub : A i ⊆ ⋃ j, A j := Set.subset_iUnion _ _
    exact closure_mono h_sub
  have h_interior_subset :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono h_closure_subset
  exact h_interior_subset hxIntA