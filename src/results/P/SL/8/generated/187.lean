

theorem P3_closure_imp_P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 (closure A) → Topology.P1 (closure A) := by
  intro hP3
  -- `P3 (closure A)` implies `closure A` is open.
  have hOpen : IsOpen (closure A) :=
    Topology.P3_closure_isOpen_closure (X := X) (A := A) hP3
  -- Openness yields `P1`.
  exact Topology.isOpen_closure_imp_P1 (X := X) (A := A) hOpen