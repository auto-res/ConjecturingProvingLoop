

theorem Topology.P2_iff_P3_of_discrete
    {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} :
    Topology.P2 (A := A) ↔ Topology.P3 (A := A) := by
  -- Use the equivalences with `P1` already established for discrete spaces.
  have h₁ : Topology.P2 (A := A) ↔ Topology.P1 (A := A) :=
    (Topology.P1_iff_P2_of_discrete (A := A)).symm
  have h₂ : Topology.P1 (A := A) ↔ Topology.P3 (A := A) :=
    Topology.P1_iff_P3_of_discrete (A := A)
  simpa using h₁.trans h₂