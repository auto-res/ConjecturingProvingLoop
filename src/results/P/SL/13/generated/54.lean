

theorem Topology.closed_P1_implies_closureInterior_eq_self {X : Type*}
    [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed (A : Set X)) (hP1 : Topology.P1 (X:=X) A) :
    closure (interior A) = (A : Set X) := by
  -- From `P1` we have equality of closures of `A` and `interior A`
  have h_eq : closure (A : Set X) = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closureInterior (X:=X) (A:=A)).1 hP1
  -- Use the closedness of `A` to rewrite `closure A` as `A`
  simpa [hA_closed.closure_eq] using h_eq.symm