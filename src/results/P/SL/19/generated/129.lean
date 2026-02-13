

theorem Topology.interior_closure_inter_subset_interior_closure_union
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    interior (closure A) ∩ interior (closure B) ⊆
      interior (closure (A ∪ B)) := by
  intro x hx
  have hxA : x ∈ interior (closure A) := hx.1
  have hClosA : closure A ⊆ closure (A ∪ B) := closure_mono (by
    intro y hy
    exact Or.inl hy)
  exact (interior_mono hClosA) hxA