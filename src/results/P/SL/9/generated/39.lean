

theorem Topology.closureInterior_closure_eq_closure_of_P1 {X : Type*} [TopologicalSpace X]
    {A : Set X} (hP1 : Topology.P1 (A := A)) :
    closure (interior (closure A)) = closure A := by
  -- First, obtain `P1` for `closure A`.
  have hP1_closure : Topology.P1 (A := closure A) :=
    Topology.P1_implies_P1_closure (A := A) hP1
  -- Translate `P1` into the desired equality.
  simpa using
    (Topology.P1_iff_closureInterior_eq_closure (A := closure A)).1 hP1_closure