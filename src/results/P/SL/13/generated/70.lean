

theorem Topology.closure_interior_closure_mono {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hAB : (A : Set X) ⊆ B) :
    closure (interior (closure A)) ⊆ closure (interior (closure B)) := by
  -- First, enlarge `A` to `B` using closure monotonicity.
  have h_closure_subset : closure (A : Set X) ⊆ closure B := closure_mono hAB
  -- Then, apply interior monotonicity to the previous inclusion.
  have h_interior_subset :
      interior (closure (A : Set X)) ⊆ interior (closure B) :=
    interior_mono h_closure_subset
  -- Finally, take closures on both sides to obtain the desired inclusion.
  exact closure_mono h_interior_subset