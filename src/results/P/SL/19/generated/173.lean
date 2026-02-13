

theorem Topology.closure_interior_union_eq_closure_interior_union_of_P1
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    Topology.P1 (A := A) → Topology.P1 (A := B) →
      closure (interior (A ∪ B)) = closure (interior A) ∪ closure (interior B) := by
  intro hP1A hP1B
  -- Equalities coming from `P1` for `A` and `B`.
  have hA_eq : closure A = closure (interior A) :=
    Topology.closure_eq_closure_interior_of_P1 (A := A) hP1A
  have hB_eq : closure B = closure (interior B) :=
    Topology.closure_eq_closure_interior_of_P1 (A := B) hP1B
  -- Equality for the union obtained from `P1` on both sets.
  have hUnion_eq :
      closure (A ∪ B) = closure (interior (A ∪ B)) :=
    Topology.closure_eq_closure_interior_union_of_P1
      (A := A) (B := B) hP1A hP1B
  -- Prove both inclusions to establish set equality.
  apply Set.Subset.antisymm
  · intro x hx
    -- Convert membership using `hUnion_eq`.
    have hx_closure_union : x ∈ closure (A ∪ B) := by
      simpa [hUnion_eq] using hx
    -- Rewrite `closure (A ∪ B)` via `closure_union`.
    have hx_union : x ∈ closure A ∪ closure B := by
      simpa [closure_union] using hx_closure_union
    -- Use `hA_eq` and `hB_eq` to land in the desired union.
    cases hx_union with
    | inl hA_mem =>
        have : x ∈ closure (interior A) := by
          simpa [hA_eq] using hA_mem
        exact Or.inl this
    | inr hB_mem =>
        have : x ∈ closure (interior B) := by
          simpa [hB_eq] using hB_mem
        exact Or.inr this
  · -- The reverse inclusion is an existing lemma.
    exact
      Topology.closure_interior_union_subset_closure_interior_union
        (A := A) (B := B)