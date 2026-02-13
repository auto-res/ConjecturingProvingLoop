

theorem P3_of_P1_and_open_closure {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A) (hOpenCl : IsOpen (closure A)) :
    Topology.P3 A := by
  dsimp [Topology.P3] at *
  intro x hxA
  -- From `P1`, obtain membership in `closure (interior A)`.
  have hx_closure_int : x ∈ closure (interior A) := hP1 hxA
  -- `P1` gives an equality of closures.
  have hEq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1
  -- Transfer membership to `closure A`.
  have hx_closure : x ∈ closure A := by
    simpa [hEq] using hx_closure_int
  -- Since `closure A` is open, its interior is itself.
  have hIntEq : interior (closure A) = closure A := hOpenCl.interior_eq
  -- Conclude the desired membership in the interior.
  simpa [hIntEq] using hx_closure