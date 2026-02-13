

theorem dense_of_P1_and_interior_closure_interior_eq_univ
    {X : Type*} [TopologicalSpace X] {A : Set X}
    (hP1 : Topology.P1 A)
    (hInt : interior (closure (interior A)) = (Set.univ : Set X)) :
    Dense A := by
  -- First, show that `closure (interior A)` is the whole space.
  have h_closure_int : closure (interior A : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    ·
      have h_subset : interior (closure (interior A)) ⊆ closure (interior A) :=
        interior_subset
      simpa [hInt] using h_subset
  -- From `P1`, deduce `closure A = closure (interior A)`.
  have h_closure_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- Hence `closure A = univ`.
  have h_closureA_univ : closure A = (Set.univ : Set X) := by
    simpa [h_closure_int] using h_closure_eq
  -- Translate this equality into density of `A`.
  exact (dense_iff_closure_eq (s := A)).2 h_closureA_univ