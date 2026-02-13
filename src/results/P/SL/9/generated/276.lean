

theorem Topology.disjoint_closureCompl_open {X : Type*} [TopologicalSpace X] {A : Set X}
    (hA : IsOpen (A : Set X)) : Disjoint (closure (Aᶜ)) A := by
  -- From a general lemma we know `closure (Aᶜ) ⊆ (interior A)ᶜ`.
  have hsubset : closure (Aᶜ : Set X) ⊆ (A : Set X)ᶜ := by
    simpa [hA.interior_eq] using
      (Topology.closure_compl_subset_compl_interior (A := A))
  -- Translate this containment into the required disjointness.
  exact (Set.disjoint_left).2 (by
    intro x hx_cl hx_A
    have : x ∈ (Aᶜ : Set X) := hsubset hx_cl
    exact this hx_A)