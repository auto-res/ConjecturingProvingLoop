

theorem interior_union_has_P1 {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (interior A ∪ interior B) := by
  -- `interior A` and `interior B` each satisfy `P1`.
  have hP1A : Topology.P1 (interior A) :=
    Topology.interior_has_P1 (X := X) (A := A)
  have hP1B : Topology.P1 (interior B) :=
    Topology.interior_has_P1 (X := X) (A := B)
  -- The union of two `P1` sets again satisfies `P1`.
  exact
    Topology.P1_union
      (X := X) (A := interior A) (B := interior B) hP1A hP1B