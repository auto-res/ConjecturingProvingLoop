

theorem Topology.closure_inter_subset {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (A ∩ B : Set X) ⊆ closure (A : Set X) ∩ closure (B : Set X) := by
  intro x hx
  have hA : x ∈ closure (A : Set X) := by
    -- `A ∩ B` is contained in `A`, so the closure of `A ∩ B` is contained in the closure of `A`.
    exact (closure_mono (Set.inter_subset_left : (A ∩ B : Set X) ⊆ A)) hx
  have hB : x ∈ closure (B : Set X) := by
    -- `A ∩ B` is contained in `B`, hence the closure of `A ∩ B` is contained in the closure of `B`.
    exact (closure_mono (Set.inter_subset_right : (A ∩ B : Set X) ⊆ B)) hx
  exact ⟨hA, hB⟩