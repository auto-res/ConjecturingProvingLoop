

theorem Topology.P1_P2_P3_closure_iff_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    (Topology.P1 (closure (A : Set X)) ∧ Topology.P2 (closure (A : Set X)) ∧
        Topology.P3 (closure (A : Set X))) ↔
      IsOpen (closure (A : Set X)) := by
  -- We already have an equivalence for the pair `P2 ∧ P3`.
  have hPair :=
    (Topology.P2_P3_closure_iff_isOpen (A := A))
  constructor
  · -- From the triple of properties we deduce openness via the pair equivalence.
    intro hTriple
    exact hPair.1 ⟨hTriple.2.1, hTriple.2.2⟩
  · -- Openness immediately gives all three properties.
    intro hOpen
    exact Topology.IsOpen_P1_P2_P3_closure (A := A) hOpen