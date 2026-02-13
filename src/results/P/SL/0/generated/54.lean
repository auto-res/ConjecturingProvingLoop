

theorem interior_has_all_Ps {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (interior (A : Set X)) ∧
    Topology.P2 (interior (A : Set X)) ∧
    Topology.P3 (interior (A : Set X)) := by
  -- `P1` and `P3` for `interior A` are already bundled together.
  have hP1P3 := Topology.interior_has_P1_and_P3 (X := X) (A := A)
  -- `P2` for `interior A` is provided separately.
  have hP2 := Topology.interior_has_P2 (X := X) (A := A)
  -- Combine the three properties.
  exact And.intro hP1P3.1 (And.intro hP2 hP1P3.2)