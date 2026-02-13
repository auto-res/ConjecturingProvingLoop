

theorem Topology.inter_closure_interior_subset_closure_interior_union {X : Type*}
    [TopologicalSpace X] {A B : Set X} :
    closure (interior (A : Set X)) ∩ closure (interior B) ⊆
      closure (interior (A ∪ B)) := by
  intro x hx
  rcases hx with ⟨hA, _hB⟩
  -- `interior A` is contained in `interior (A ∪ B)`
  have h_subset : (interior (A : Set X)) ⊆ interior (A ∪ B) :=
    interior_mono (Set.subset_union_left : (A : Set X) ⊆ A ∪ B)
  -- Taking closures preserves this inclusion
  have h_closure_subset :
      closure (interior (A : Set X)) ⊆ closure (interior (A ∪ B)) :=
    closure_mono h_subset
  exact h_closure_subset hA