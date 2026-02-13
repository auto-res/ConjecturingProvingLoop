

theorem Topology.interior_eq_self_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} :
    interior A = (A : Set X) → Topology.P3 A := by
  intro hIntEq
  have hOpen : IsOpen (A : Set X) :=
    (isOpen_iff_interior_eq (A := A)).2 hIntEq
  exact Topology.isOpen_implies_P3 (A := A) hOpen