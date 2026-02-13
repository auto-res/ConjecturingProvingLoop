

theorem P1_P2_P3_of_boundary_empty {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (A : Set X) \ interior (A : Set X) = (∅ : Set X) →
      Topology.P1 A ∧ Topology.P2 A ∧ Topology.P3 A := by
  intro hBoundary
  -- An empty boundary implies that `A` is both open and closed.
  have hClopen : IsOpen (A : Set X) ∧ IsClosed (A : Set X) :=
    (boundary_eq_empty_iff_isClopen (A := A)).1 hBoundary
  -- Any open set satisfies `P1`, `P2`, and `P3`.
  have hP1 : Topology.P1 (A : Set X) := Topology.P1_of_isOpen (A := A) hClopen.1
  have hP2 : Topology.P2 (A : Set X) := Topology.P2_of_isOpen (A := A) hClopen.1
  have hP3 : Topology.P3 (A : Set X) := Topology.P3_of_isOpen (A := A) hClopen.1
  exact ⟨hP1, hP2, hP3⟩