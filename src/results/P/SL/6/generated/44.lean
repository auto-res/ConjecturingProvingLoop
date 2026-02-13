

theorem open_satisfies_all_Ps
    {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen (A : Set X)) :
    Topology.P1 (A : Set X) ∧ Topology.P2 A ∧ Topology.P3 A := by
  exact
    ⟨Topology.open_satisfies_P1 (A := A) hA,
      ⟨Topology.open_satisfies_P2 (A := A) hA,
        Topology.open_satisfies_P3 (A := A) hA⟩⟩