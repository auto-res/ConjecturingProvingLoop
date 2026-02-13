

theorem Topology.closure_interior_eq_self_iff_isClosed_and_P1
    {X : Type*} [TopologicalSpace X] {A : Set X} :
    closure (interior A) = (A : Set X) ↔ (IsClosed A ∧ Topology.P1 A) := by
  constructor
  · intro hEq
    -- `A` is closed because it is the closure of some set.
    have hClosed : IsClosed (A : Set X) := by
      have : IsClosed (closure (interior A) : Set X) := isClosed_closure
      simpa [hEq] using this
    -- Use the closedness to rewrite `closure A`.
    have hClA : closure (A : Set X) = (A : Set X) := hClosed.closure_eq
    -- Turn the given equality into the characterisation of `P1`.
    have hP1 : Topology.P1 A := by
      -- Both closures coincide because they are equal to `A`.
      have hClosureEq : closure (interior A) = closure (A : Set X) := by
        simpa [hEq, hClA]
      exact
        (Topology.P1_iff_closure_interior_eq_closure (A := A)).mpr hClosureEq
    exact And.intro hClosed hP1
  · rintro ⟨hClosed, hP1⟩
    exact
      Topology.isClosed_P1_implies_closure_interior_eq_self
        (A := A) hClosed hP1