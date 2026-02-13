

theorem P1_iff_P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P1 A ↔ Topology.P3 A := by
  simpa using
    ((Topology.P1_iff_P2_of_open (X := X) (A := A) hA).trans
      (Topology.P2_iff_P3_of_open (X := X) (A := A) hA))

theorem exists_dense_P2 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, Topology.P2 A ∧ Dense A := by
  refine ⟨(Set.univ : Set X), ?_, ?_⟩
  · exact Topology.P2_univ (X := X)
  · simpa using dense_univ