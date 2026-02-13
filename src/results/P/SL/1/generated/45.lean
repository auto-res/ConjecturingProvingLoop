

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P3 (A i)) → Topology.P3 (⋃ i, A i) := by
  intro hA
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hxInt : x ∈ interior (closure (A i)) := (hA i) hxAi
  have hsubset : interior (closure (A i)) ⊆ interior (closure (⋃ i, A i)) := by
    apply interior_mono
    have : closure (A i) ⊆ closure (⋃ i, A i) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.2 ⟨i, hy⟩
    exact this
  exact hsubset hxInt