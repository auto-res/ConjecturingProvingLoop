

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, Topology.P3 (A i)) : Topology.P3 (⋃ i, A i) := by
  dsimp [Topology.P3] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  -- `x` lies in `interior (closure (A i))`
  have hx_int : x ∈ interior (closure (A i)) := (hA i) hxi
  -- `interior (closure (A i)) ⊆ interior (closure (⋃ j, A j))`
  have h_mono : interior (closure (A i)) ⊆ interior (closure (⋃ j, A j)) := by
    have h_closure_mono : closure (A i) ⊆ closure (⋃ j, A j) := by
      have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_subset
    exact interior_mono h_closure_mono
  exact h_mono hx_int