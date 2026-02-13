

theorem Topology.closureInteriorClosure_eq_closure_of_isOpen_closure
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hOpen : IsOpen (closure A)) :
    closure (interior (closure A)) = closure A := by
  have hInt : interior (closure A) = closure A := hOpen.interior_eq
  calc
    closure (interior (closure A)) = closure (closure A) := by
      simpa [hInt]
    _ = closure A := by
      simpa [closure_closure]