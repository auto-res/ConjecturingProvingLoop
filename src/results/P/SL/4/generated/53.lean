

theorem P2_iff_P3_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 A ↔ Topology.P3 A := by
  -- For an open set, `interior A = A`.
  have h_int : interior A = A := hA.interior_eq
  -- Rewrite `P2` using the above equality.
  have hP2 : Topology.P2 A ↔ A ⊆ interior (closure A) := by
    dsimp [Topology.P2]
    simpa [h_int]
  -- `P3` is already exactly the same inclusion.
  have h : (A ⊆ interior (closure A)) ↔ Topology.P3 A := by
    dsimp [Topology.P3]
    exact Iff.rfl
  -- Combine the two equivalences.
  exact hP2.trans h