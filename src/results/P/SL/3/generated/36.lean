

theorem P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort _} {f : ι → Set X}
    (hf : ∀ i, Topology.P3 (f i)) :
    Topology.P3 (⋃ i, f i) := by
  dsimp [Topology.P3] at hf ⊢
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  have hx_int : (x : X) ∈ interior (closure (f i)) := hf i hxi
  have h_subset :
      interior (closure (f i)) ⊆ interior (closure (⋃ j, f j)) := by
    apply interior_mono
    have h_closure : closure (f i) ⊆ closure (⋃ j, f j) := by
      apply closure_mono
      intro y hy
      exact Set.mem_iUnion.mpr ⟨i, hy⟩
    exact h_closure
  exact h_subset hx_int