

theorem open_closure_interior_eq_closure_implies_P3
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (interior (A : Set X))))
    (hEq  : closure (interior (A : Set X)) = closure A) :
    Topology.P3 (A : Set X) := by
  dsimp [Topology.P3]
  intro x hxA
  -- First, place `x` inside `closure (interior A)` using the equality of closures.
  have hx_clInt : x ∈ closure (interior (A : Set X)) := by
    have hx_cl : x ∈ closure (A : Set X) := subset_closure hxA
    simpa [hEq] using hx_cl
  -- Since this set is open, its interior equals itself.
  have hx_int_clInt :
      x ∈ interior (closure (interior (A : Set X))) := by
    simpa [hOpen.interior_eq] using hx_clInt
  -- The equality of closures yields an equality of their interiors.
  have hIntEq :
      interior (closure (interior (A : Set X))) =
        interior (closure (A : Set X)) := by
    simpa using congrArg interior hEq
  -- Reinterpret the membership in the desired interior.
  have hx_int : x ∈ interior (closure (A : Set X)) := by
    simpa [hIntEq] using hx_int_clInt
  exact hx_int