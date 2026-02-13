

theorem P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X}
    (hf : ∀ i, Topology.P2 (f i)) :
    Topology.P2 (⋃ i, f i) := by
  dsimp [Topology.P2] at hf ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx_int : (x : X) ∈ interior (closure (interior (f i))) := hf i hxi
  have h_subset :
      interior (closure (interior (f i))) ⊆
        interior (closure (interior (⋃ j, f j))) := by
    have h_closure :
        closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) := by
      apply closure_mono
      have h_int : interior (f i) ⊆ interior (⋃ j, f j) := by
        apply interior_mono
        intro y hy
        exact Set.mem_iUnion.mpr ⟨i, hy⟩
      exact h_int
    exact interior_mono h_closure
  exact h_subset hx_int