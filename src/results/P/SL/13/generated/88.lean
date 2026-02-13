

theorem Topology.interior_closure_inter_subset_inter_interior_closure {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    interior (closure ((A ∩ B) : Set X)) ⊆
      interior (closure A) ∩ interior (closure B) := by
  intro x hx
  -- First, use monotonicity of `closure` and `interior` with respect to `A`.
  have hA_subset : closure ((A ∩ B) : Set X) ⊆ closure A :=
    closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)
  have hxA : x ∈ interior (closure A) := (interior_mono hA_subset) hx
  -- Next, do the same with respect to `B`.
  have hB_subset : closure ((A ∩ B) : Set X) ⊆ closure B :=
    closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)
  have hxB : x ∈ interior (closure B) := (interior_mono hB_subset) hx
  -- Combine the two inclusions to obtain the desired result.
  exact ⟨hxA, hxB⟩