

theorem Topology.P3_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P3 (A i)) → Topology.P3 (Set.iUnion A) := by
  intro h
  unfold Topology.P3
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx₁ : x ∈ interior (closure (A i)) := h i hxA
  have hsubset_closure : closure (A i) ⊆ closure (Set.iUnion A) :=
    closure_mono (Set.subset_iUnion A i)
  have hsubset : interior (closure (A i)) ⊆ interior (closure (Set.iUnion A)) :=
    interior_mono hsubset_closure
  exact hsubset hx₁