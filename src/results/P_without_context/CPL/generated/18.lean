

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] {A : Set X} (h : Topology.P2 A) : Topology.P3 A := by
  -- Using the monotonicity of closure and interior we build the required chain of inclusions
  have h_int_subset : interior (closure (interior A)) ⊆ interior (closure A) := by
    -- first, `closure (interior A)` is contained in `closure A`
    have h_closure_subset : closure (interior A) ⊆ closure A :=
      closure_mono interior_subset
    -- applying `interior` preserves the inclusion
    exact interior_mono h_closure_subset
  -- chaining the inclusions given by `h` and `h_int_subset`
  exact subset_trans h h_int_subset

theorem P1_union {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : Topology.P1 A) (hB : Topology.P1 B) : Topology.P1 (A ∪ B) := by
  -- Unfold the definition of `Topology.P1`.
  unfold Topology.P1 at *
  -- We need to show: `A ∪ B ⊆ closure (interior (A ∪ B))`.
  apply Set.union_subset
  · -- First, deal with `A`.
    refine Set.Subset.trans hA ?_
    -- `interior A` is contained in `interior (A ∪ B)`.
    have h_int_subset : interior A ⊆ interior (A ∪ B) := by
      exact interior_mono (by
        intro x hx
        exact Or.inl hx)
    -- Monotonicity of `closure` gives the required inclusion.
    exact closure_mono h_int_subset
  · -- Then, deal with `B`.
    refine Set.Subset.trans hB ?_
    have h_int_subset : interior B ⊆ interior (A ∪ B) := by
      exact interior_mono (by
        intro x hx
        exact Or.inr hx)
    exact closure_mono h_int_subset

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 A := by
  unfold Topology.P1
  intro x hx
  have hAuniv : (A : Set X) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    have h_eq : y = x := Subsingleton.elim y x
    simpa [h_eq] using hx
  have hx_int : x ∈ interior A := by
    simpa [hAuniv, interior_univ] using (Set.mem_univ x)
  exact subset_closure hx_int

theorem P3_of_closure_subset_interior {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior (closure A)) : Topology.P3 A := by
  dsimp [Topology.P3]
  exact Set.Subset.trans subset_closure h