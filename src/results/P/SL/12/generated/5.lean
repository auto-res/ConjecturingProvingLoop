

theorem Topology.isOpen_P2 {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen A) :
    Topology.P2 (X := X) A := by
  -- Using `P3` for open sets
  have h : A ⊆ interior (closure A) := Topology.isOpen_P3 (X := X) hA
  -- Rewrite the goal via `interior` of an open set
  simpa [Topology.P2, hA.interior_eq] using h