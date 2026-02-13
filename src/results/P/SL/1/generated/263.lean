

theorem Topology.P1_P2_P3_of_isClopen_compl
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    IsClopen A → Topology.P1 (Aᶜ) ∧ Topology.P2 (Aᶜ) ∧ Topology.P3 (Aᶜ) := by
  intro hA
  simpa using
    (Topology.P1_P2_P3_of_isClopen (A := Aᶜ) hA.compl)