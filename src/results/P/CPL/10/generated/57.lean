

theorem P2_inter_three {X : Type*} [TopologicalSpace X] {A B C : Set X} (hA : Topology.P2 A) (hB : Topology.P2 B) (hC : Topology.P2 C) : Topology.P2 (A ∩ B ∩ C) := by
  have hAB : Topology.P2 (A ∩ B) := Topology.P2_inter (X := X) hA hB
  simpa using (Topology.P2_inter (X := X) hAB hC)

theorem exists_clopen_P1 {X : Type*} [TopologicalSpace X] : ∃ A : Set X, IsOpen A ∧ IsClosed A ∧ Topology.P1 A := by
  refine ⟨(Set.univ : Set X), isOpen_univ, isClosed_univ, ?_⟩
  simpa using Topology.P1_univ (X := X)