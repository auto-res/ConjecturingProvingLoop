

theorem Topology.open_closure_satisfies_P1_P2_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) :
    Topology.P1 (X := X) (closure A) ∧
      Topology.P2 (X := X) (closure A) ∧
      Topology.P3 (X := X) A := by
  -- `P1` holds for `closure A` because it is open.
  have hP1 : Topology.P1 (X := X) (closure A) := by
    simpa [closure_closure] using
      (Topology.isOpen_closure_implies_P1 (X := X) (A := closure A) hOpen)
  -- `P2` holds for `closure A` by openness of `closure A`.
  have hP2 : Topology.P2 (X := X) (closure A) :=
    Topology.P2_of_open_closure (X := X) (A := A) hOpen
  -- `P3` holds for `A` when `closure A` is open.
  have hP3 : Topology.P3 (X := X) A :=
    Topology.P3_of_open_closure (X := X) (A := A) hOpen
  exact ⟨hP1, hP2, hP3⟩