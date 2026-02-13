

theorem closure_interior_closure_eq_closure_of_open_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- Since `closure A` is open, its interior coincides with itself.
  have hInt : interior (closure (A : Set X)) = closure (A : Set X) :=
    hOpen.interior_eq
  -- Rewrite and simplify using `closure_closure`.
  have : closure (interior (closure (A : Set X))) =
      closure (closure (A : Set X)) := by
    simpa [hInt]
  simpa [closure_closure] using this