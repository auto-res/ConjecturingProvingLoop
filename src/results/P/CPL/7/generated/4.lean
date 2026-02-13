

theorem P2_of_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} (hA : closure (interior A) = Set.univ) : Topology.P2 A := by
  intro x hx
  simpa [hA, interior_univ] using (Set.mem_univ x)

theorem P1_Union {X : Type*} [TopologicalSpace X] {ι : Type*} {F : ι → Set X} (hF : ∀ i, Topology.P1 (F i)) : Topology.P1 (⋃ i, F i) := by
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxFi⟩
  have hxi : x ∈ closure (interior (F i)) := (hF i) hxFi
  have hsubset : closure (interior (F i)) ⊆ closure (interior (⋃ j, F j)) := by
    have h_subset_F : (F i : Set X) ⊆ ⋃ j, F j := by
      intro y hy
      exact Set.mem_iUnion_of_mem i hy
    have hsubset_int : interior (F i) ⊆ interior (⋃ j, F j) :=
      interior_mono h_subset_F
    exact closure_mono hsubset_int
  exact hsubset hxi