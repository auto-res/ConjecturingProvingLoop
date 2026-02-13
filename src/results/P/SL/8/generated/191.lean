

theorem closed_P2_imp_closureInterior_eq {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA_closed : IsClosed A) (hP2 : Topology.P2 A) :
    closure (interior A) = A := by
  -- First, use closedness together with `P2` to obtain `P1`.
  have hP1 : Topology.P1 A :=
    closed_P2_imp_P1 (X := X) (A := A) hA_closed hP2
  -- Translate `P1` into the desired equality via the closed‐set characterization.
  exact
    (closed_P1_iff_closure_interior_eq (X := X) (A := A) hA_closed).1 hP1