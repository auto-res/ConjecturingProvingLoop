

theorem P2_iUnion_finset {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι] {A : ι → Set X} : (∀ i, P2 (A i)) → P2 (⋃ i, A i) := by
  intro hP2
  simpa using (Topology.P2_iUnion (X := X) (A := A) hP2)

theorem P1_closure_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P3 A → P1 (closure A) := by
  intro hP3
  intro x hx_cl
  have hsubset : (A : Set X) ⊆ interior (closure A) := hP3
  have hclosure_subset :
      (closure (A : Set X)) ⊆ closure (interior (closure A)) :=
    closure_mono hsubset
  exact hclosure_subset hx_cl