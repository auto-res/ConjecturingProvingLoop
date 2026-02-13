

theorem P2_union_compl {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Topology.P2 A) : Topology.P2 (A ∪ Aᶜ) := by
  simpa [Set.union_compl_self] using (P2_univ (X := X))