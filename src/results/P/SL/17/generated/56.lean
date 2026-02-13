

theorem Topology.P1_iff_P2_of_isOpen {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen A) : Topology.P1 A ↔ Topology.P2 A := by
  constructor
  · intro _hP1
    -- Since `A` is open, `P2` always holds for `A`.
    unfold Topology.P2
    intro x hxA
    have h_subset : A ⊆ interior (closure A) :=
      interior_maximal subset_closure hOpen
    have hxInt : x ∈ interior (closure A) := h_subset hxA
    simpa [hOpen.interior_eq] using hxInt
  · intro hP2
    exact Topology.P2_implies_P1 (A := A) hP2