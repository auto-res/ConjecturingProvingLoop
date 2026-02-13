

theorem P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X}
    (hf : ∀ i, Topology.P1 (f i)) :
    Topology.P1 (⋃ i, f i) := by
  dsimp [Topology.P1] at hf ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx_cl : (x : X) ∈ closure (interior (f i)) := hf i hxi
  have h_subset :
      closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) := by
    apply closure_mono
    have h_int : interior (f i) ⊆ interior (⋃ j, f j) := by
      apply interior_mono
      intro y hy
      exact Set.mem_iUnion.mpr ⟨i, hy⟩
    exact h_int
  exact h_subset hx_cl