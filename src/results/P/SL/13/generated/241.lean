

theorem Topology.all_P_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) :
    Topology.P1 (X := X) (Aᶜ : Set X) ∧
      Topology.P2 (X := X) (Aᶜ : Set X) ∧
        Topology.P3 (X := X) (Aᶜ : Set X) := by
  -- The complement of a closed set is open.
  have hA_open_compl : IsOpen (Aᶜ : Set X) := hA_closed.isOpen_compl
  -- Any open set satisfies all three properties `P1`, `P2`, and `P3`.
  exact
    Topology.isOpen_implies_all_P (X := X) (A := Aᶜ) hA_open_compl