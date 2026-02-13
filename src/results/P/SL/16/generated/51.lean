

theorem Topology.P2_iUnion {ι X : Type*} [TopologicalSpace X] {A : ι → Set X}
    (hP : ∀ i, Topology.P2 (X := X) (A i)) :
    Topology.P2 (X := X) (⋃ i, A i) := by
  classical
  dsimp [Topology.P2] at hP ⊢
  intro x hxUnion
  rcases Set.mem_iUnion.1 hxUnion with ⟨i, hxAi⟩
  have hxInt : x ∈ interior (closure (interior (A i))) := hP i hxAi
  -- Step 1:  interior (A i) ⊆ interior (⋃ j, A j)
  have h_int_subset : interior (A i) ⊆ interior (⋃ j, A j) := by
    have h_sub : interior (A i) ⊆ ⋃ j, A j := by
      intro y hy
      have hyAi : y ∈ A i := interior_subset hy
      exact Set.mem_iUnion.2 ⟨i, hyAi⟩
    exact interior_maximal h_sub isOpen_interior
  -- Step 2:  closure (interior (A i)) ⊆ closure (interior (⋃ j, A j))
  have h_closure_subset :
      closure (interior (A i)) ⊆ closure (interior (⋃ j, A j)) :=
    closure_mono h_int_subset
  -- Step 3:  interior (closure (interior (A i))) ⊆ interior (closure (interior (⋃ j, A j)))
  have h_int_subset' :
      interior (closure (interior (A i))) ⊆
        interior (closure (interior (⋃ j, A j))) :=
    interior_mono h_closure_subset
  exact h_int_subset' hxInt