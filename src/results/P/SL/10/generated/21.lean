

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P2 (A i)) → Topology.P2 (⋃ i, A i) := by
  intro h_all
  dsimp [Topology.P2] at h_all ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx_int : x ∈ interior (closure (interior (A i))) := (h_all i) hxA
  have h_subset :
      interior (closure (interior (A i))) ⊆
      interior (closure (interior (⋃ j, A j))) := by
    have h_closure :
        closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
      have h_int : interior (A i) ⊆ interior (⋃ j, A j) := by
        have h_sub : (A i) ⊆ ⋃ j, A j := by
          intro y hy
          exact Set.mem_iUnion.2 ⟨i, hy⟩
        exact interior_mono h_sub
      exact closure_mono h_int
    exact interior_mono h_closure
  exact h_subset hx_int