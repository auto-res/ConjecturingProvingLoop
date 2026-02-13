

theorem Topology.P2_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P2 (A i)) → Topology.P2 (Set.iUnion A) := by
  intro h
  unfold Topology.P2
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx₁ : x ∈ interior (closure (interior (A i))) := h i hxA
  have hsubset_int : interior (A i) ⊆ interior (Set.iUnion A) :=
    interior_mono (Set.subset_iUnion A i)
  have hsubset_clos : closure (interior (A i)) ⊆ closure (interior (Set.iUnion A)) :=
    closure_mono hsubset_int
  have hsubset : interior (closure (interior (A i))) ⊆
      interior (closure (interior (Set.iUnion A))) :=
    interior_mono hsubset_clos
  exact hsubset hx₁