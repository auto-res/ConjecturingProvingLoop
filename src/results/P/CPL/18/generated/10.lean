

theorem P2_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (interior A) := by
  dsimp [Topology.P2]
  simpa [interior_interior] using
    interior_maximal
      (subset_closure : (interior A : Set X) ⊆ closure (interior A))
      isOpen_interior

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, Topology.P2 (A i)) : Topology.P2 (⋃ i, A i) := by
  dsimp [Topology.P2] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxAi⟩
  have hx' : x ∈ interior (closure (interior (A i))) := hA i hxAi
  have hsubset :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ i, A i))) := by
    apply interior_mono
    apply closure_mono
    apply interior_mono
    intro y hy
    exact Set.mem_iUnion.2 ⟨i, hy⟩
  exact hsubset hx'