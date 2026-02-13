

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X}
    (hA : ∀ i, Topology.P1 (A i)) : Topology.P1 (⋃ i, A i) := by
  dsimp [Topology.P1] at hA ⊢
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  -- `x` is in `closure (interior (A i))`
  have hx_closure_int : x ∈ closure (interior (A i)) := (hA i) hxi
  -- `closure (interior (A i)) ⊆ closure (interior (⋃ j, A j))`
  have h_mono : closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) := by
    have h_int_mono : interior (A i) ⊆ interior (⋃ j, A j) := by
      have h_subset : (A i : Set X) ⊆ ⋃ j, A j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset
    exact closure_mono h_int_mono
  exact h_mono hx_closure_int