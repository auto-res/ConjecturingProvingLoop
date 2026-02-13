

theorem Topology.closureInteriorClosure_eq_closure_of_isOpen
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure (A : Set X))) :
    closure (interior (closure (A : Set X))) = closure (A : Set X) := by
  -- Since `closure A` is open, its interior is itself.
  have hInt : interior (closure (A : Set X)) = closure (A : Set X) :=
    hOpen.interior_eq
  -- Rewrite using this fact and simplify with idempotency of `closure`.
  calc
    closure (interior (closure (A : Set X)))
        = closure (closure (A : Set X)) := by
          simpa [hInt]
    _ = closure (A : Set X) := by
          simpa [closure_closure]