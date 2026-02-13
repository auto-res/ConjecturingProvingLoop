

theorem Topology.P1_closure_iff_closure_interior_closure_eq_closure
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 (closure (A : Set X)) ↔
      closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- Use the existing equivalence with `S = closure A`.
  have hEquiv :=
    (Topology.P1_iff_closure_interior_eq_closure
        (A := closure (A : Set X)))
  constructor
  · intro hP1
    have h := (hEquiv).1 hP1
    simpa [closure_closure] using h
  · intro hEq
    -- Rewrite the given equality to the form expected by `hEquiv`.
    have h' :
        closure (interior (closure (A : Set X))) =
          closure (closure (A : Set X)) := by
      simpa [closure_closure] using hEq
    exact (hEquiv).2 h'