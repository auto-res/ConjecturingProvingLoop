

theorem P2_of_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure (interior A) = Set.univ) : Topology.P2 (A := A) := by
  intro x hx
  simpa [h, interior_univ]

theorem P3_of_neighbourhood_basis {X : Type*} [TopologicalSpace X] {A : Set X} (h : ∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior (closure A)) : Topology.P3 (A := A) := by
  intro x hxA
  rcases h x hxA with ⟨U, _U_open, hxU, h_subset⟩
  have hx_closureU : (x : X) ∈ closure U := subset_closure hxU
  exact h_subset hx_closureU

theorem P2_seq_union {X : Type*} [TopologicalSpace X] {A : ℕ → Set X} (h : ∀ n, Topology.P2 (A := A n)) : Topology.P2 (A := ⋃ n, A n) := by
  simpa using (P2_iUnion (s := A) (h := h))