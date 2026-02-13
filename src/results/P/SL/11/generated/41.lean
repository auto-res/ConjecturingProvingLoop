

theorem P1_iUnion {X ι : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hA : ∀ i, Topology.P1 (A i)) :
    Topology.P1 (⋃ i, A i) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxAi⟩
  have hxClosure : x ∈ closure (interior (A i)) := (hA i) hxAi
  have hsubset : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    apply closure_mono
    have hinner : interior (A i) ⊆ interior (⋃ j, A j) := by
      have hsub : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.mpr ⟨i, hy⟩
      exact interior_mono hsub
    exact hinner
  exact hsubset hxClosure