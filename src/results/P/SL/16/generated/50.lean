

theorem Topology.P3_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hP : ∀ i, Topology.P3 (X := X) (A i)) :
    Topology.P3 (X := X) (⋃ i, A i) := by
  classical
  dsimp [Topology.P3] at hP ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hxAi⟩
  have hxIntAi : x ∈ interior (closure (A i)) := hP i hxAi
  have hAi_subset : A i ⊆ ⋃ j, A j := by
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  have h_closure_subset : closure (A i) ⊆ closure (⋃ j, A j) :=
    closure_mono hAi_subset
  have h_int_subset :
      interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) :=
    interior_mono h_closure_subset
  exact h_int_subset hxIntAi