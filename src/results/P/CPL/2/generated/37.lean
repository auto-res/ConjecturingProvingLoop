

theorem P2_implies_P1_or_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 (X:=X) A → (Topology.P1 (X:=X) A ∨ Topology.P3 (X:=X) A) := by
  intro h
  exact Or.inl (Topology.P1_of_P2 (A := A) h)