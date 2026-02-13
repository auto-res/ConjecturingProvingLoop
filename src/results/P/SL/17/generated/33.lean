

theorem Topology.P1_iUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {A : ι → Set X} :
    (∀ i, Topology.P1 (A i)) → Topology.P1 (Set.iUnion A) := by
  intro h
  unfold Topology.P1
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxA⟩
  have hx₁ : x ∈ closure (interior (A i)) := h i hxA
  have hsubset : interior (A i) ⊆ interior (Set.iUnion A) :=
    interior_mono (Set.subset_iUnion A i)
  have hclosure : closure (interior (A i)) ⊆ closure (interior (Set.iUnion A)) :=
    closure_mono hsubset
  exact hclosure hx₁